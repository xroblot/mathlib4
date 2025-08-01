/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Lean.Meta.RefinedDiscrTree.Basic
import Lean.Meta.LazyDiscrTree

/-!
# Constructing a RefinedDiscrTree

`RefinedDiscrTree` is lazy, so to add an entry, we need to compute
the first `Key` and a `LazyEntry`. These are computed by `initializeLazyEntry`.

We provide `RefinedDiscrTree.insert` for directly performing this insert.

For initializing a `RefinedDiscrTree` using all imported constants,
we provide `createImportedDiscrTree`, which loops through all imported constants,
and does this with a parallel computation.

There is also `createModuleDiscrTree` which does the same but with the constants
from the current file.

-/
namespace Lean.Meta.RefinedDiscrTree

variable {α : Type}

/-- Directly insert a `Key`, `LazyEntry` pair into a `RefinedDiscrTree`. -/
def insert (d : RefinedDiscrTree α) (key : Key) (entry : LazyEntry × α) : RefinedDiscrTree α :=
  if let some trie := d.root[key]? then
    { d with
      tries := d.tries.modify trie fun node => { node with pending := node.pending.push entry } }
  else
    { d with
      root := d.root.insert key d.tries.size
      tries := d.tries.push <| .node #[] none {} {} #[entry] }

/--
Structure for quickly initializing a lazy discrimination tree with a large number
of elements using concurrent functions for generating entries.
-/
structure PreDiscrTree (α : Type) where
  /-- Maps keys to index in tries array. -/
  root : Std.HashMap Key Nat := {}
  /-- Lazy entries for root of trie. -/
  tries : Array (Array (LazyEntry × α)) := #[]
  deriving Inhabited

namespace PreDiscrTree

@[specialize]
private def modifyAt (d : PreDiscrTree α) (k : Key)
    (f : Array (LazyEntry × α) → Array (LazyEntry × α)) : PreDiscrTree α :=
  let { root, tries } := d
  match root[k]? with
  | none =>
    { root := root.insert k tries.size, tries := tries.push (f #[]) }
  | some i =>
    { root, tries := tries.modify i f }

/-- Add an entry to the pre-discrimination tree. -/
def push (d : PreDiscrTree α) (k : Key) (e : LazyEntry × α) : PreDiscrTree α :=
  d.modifyAt k (·.push e)

/-- Convert a pre-discrimination tree to a `RefinedDiscrTree`. -/
def toRefinedDiscrTree (d : PreDiscrTree α) : RefinedDiscrTree α :=
  let { root, tries } := d
  { root, tries := tries.map fun pending => .node #[] none {} {} pending }

/-- Merge two discrimination trees. -/
def append (x y : PreDiscrTree α) : PreDiscrTree α :=
  let (x, y, f) :=
    if x.root.size ≥ y.root.size then
      (x, y, fun y x => x ++ y)
    else
      (y, x, fun x y => x ++ y)
  let { root := yk, tries := ya } := y
  yk.fold (init := x) fun d k yi => d.modifyAt k (f ya[yi]!)

instance : Append (PreDiscrTree α) where
  append := PreDiscrTree.append

end PreDiscrTree


/-- Information about a failed import. -/
private structure ImportFailure where
  /-- Module with constant that import failed on. -/
  module : Name
  /-- Constant that import failed on. -/
  const : Name
  /-- Exception that triggers error. -/
  exception : Exception

/-- Information generation from imported modules. -/
private structure ImportErrorData where
  errors : IO.Ref (Array ImportFailure)

private def ImportErrorData.new : BaseIO ImportErrorData := do
  return { errors := ← IO.mkRef #[] }
/--
Add the entries generated by `act name constInfo` to the `PreDiscrTree`.

Note: It is expensive to create two new `IO.Ref`s for every `MetaM` operation,
  so instead we reuse the same refs `mstate` and `cstate`. These are also used to
  remember the cache, and the namegenerator across the operations.
-/
@[inline] private def addConstToPreDiscrTree
    (cctx : Core.Context)
    (env : Environment)
    (modName : Name)
    (data : ImportErrorData)
    (mstate : IO.Ref Meta.State)
    (cstate : IO.Ref Core.State)
    (act : Name → ConstantInfo → MetaM (List (α × List (Key × LazyEntry))))
    (tree : PreDiscrTree α) (name : Name) (constInfo : ConstantInfo) :
    BaseIO (PreDiscrTree α) := do
  -- here we use an if-then-else clause instead of the more stylish if-then-return,
  -- because it compiles to more performant code
  if constInfo.isUnsafe then pure tree else
  if LazyDiscrTree.blacklistInsertion env name then pure tree else
  /- For efficiency, we leave it up to the implementation of `act` to reset the states if needed -/
  -- mstate.modify fun s => { cache := s.cache }
  -- cstate.modify fun s => { env := s.env, cache := s.cache, ngen := s.ngen }
  let mctx := { config := { transparency := .reducible } }
  match ← (((act name constInfo) mctx mstate) cctx cstate).toBaseIO with
  | .ok a =>
    return a.foldl (fun t (val, entries) =>
      entries.foldl (fun t (key, entry) => t.push key (entry, val)) t) tree
  | .error e =>
    let i : ImportFailure := {
      module := modName,
      const := name,
      exception := e }
    data.errors.modify (·.push i)
    return tree


/--
Contains the pre discrimination tree and any errors occuring during initialization of
the library search tree.
-/
private structure InitResults (α : Type) where
  tree : PreDiscrTree α := {}
  errors : Array ImportFailure := #[]

namespace InitResults

/-- Combine two initial results. -/
protected def append (x y : InitResults α) : InitResults α :=
  let { tree := xv, errors := xe } := x
  let { tree := yv, errors := ye } := y
  { tree := xv ++ yv, errors := xe ++ ye }

instance : Append (InitResults α) where
  append := InitResults.append

end InitResults

private def toInitResults (data : ImportErrorData) (tree : PreDiscrTree α) :
    BaseIO (InitResults α) := do
  let de ← data.errors.swap #[]
  pure ⟨tree, de⟩

/--
Loop through all constants that appear in the module `mdata`,
and add the entries generated by `act` to the `PreDiscrTree`.
-/
private partial def loadImportedModule
    (cctx : Core.Context)
    (env : Environment)
    (data : ImportErrorData)
    (mstate : IO.Ref Meta.State)
    (cstate : IO.Ref Core.State)
    (act : Name → ConstantInfo → MetaM (List (α × List (Key × LazyEntry))))
    (mname : Name)
    (mdata : ModuleData)
    (tree : PreDiscrTree α)
    (i : Nat := 0) : BaseIO (PreDiscrTree α) := do
  if h : i < mdata.constNames.size then
    let name := mdata.constNames[i]
    let constInfo := mdata.constants[i]!
    let state ← addConstToPreDiscrTree cctx env mname data mstate cstate act tree name constInfo
    loadImportedModule cctx env data mstate cstate act mname mdata state (i+1)
  else
    return tree

/--
Loop through all constants that appear in the modules with module index from `start` to `stop - 1`,
and add the entries generated by `act` to the `PreDiscrTree`.
-/
private def createImportInitResults (cctx : Core.Context) (ngen : NameGenerator)
    (env : Environment) (act : Name → ConstantInfo → MetaM (List (α × List (Key × LazyEntry))))
    (capacity start stop : Nat) : BaseIO (InitResults α) := do
  let tree := { root := .emptyWithCapacity capacity }
  go start stop tree (← ImportErrorData.new) (← IO.mkRef {}) (← IO.mkRef { env, ngen })
where
  go (start stop : Nat) (tree : PreDiscrTree α)
      (data : ImportErrorData)
      (mstate : IO.Ref Meta.State)
      (cstate : IO.Ref Core.State) :
      BaseIO (InitResults α) := do
    if start < stop then
      let mname := env.header.moduleNames[start]!
      let mdata := env.header.moduleData[start]!
      let tree ← loadImportedModule cctx env data mstate cstate act mname mdata tree
      go (start+1) stop tree data mstate cstate
    else
      toInitResults data tree
  termination_by stop - start

private def getChildNgen : CoreM NameGenerator := do
  let ngen ← getNGen
  let (cngen, ngen) := ngen.mkChild
  setNGen ngen
  pure cngen

private def logImportFailure (f : ImportFailure) : CoreM Unit :=
  logError m!"Processing failure with {f.const} in {f.module}:\n  {f.exception.toMessageData}"

/--
Create a `RefinedDiscrTree` consisting of all entries generated by `act`
from imported constants. (it gets called by `addConstToPreDiscrTree`).
This uses parallel computation.
-/
def createImportedDiscrTree (ngen : NameGenerator) (env : Environment)
    (act : Name → ConstantInfo → MetaM (List (α × List (Key × LazyEntry))))
    (constantsPerTask capacityPerTask : Nat) :
    CoreM (RefinedDiscrTree α) := do
  let numModules := env.header.moduleData.size
  let cctx ← read
  let rec
    /-- Allocate constants to tasks according to `constantsPerTask`. -/
    go (ngen : NameGenerator) (tasks : Array (Task (InitResults α))) (start cnt idx : Nat) := do
      if h : idx < numModules then
        let mdata := env.header.moduleData[idx]
        let cnt := cnt + mdata.constants.size
        if cnt > constantsPerTask then
          let (childNGen, ngen) := ngen.mkChild
          let t ← (createImportInitResults
            cctx childNGen env act capacityPerTask start (idx+1)).asTask
          go ngen (tasks.push t) (idx+1) 0 (idx+1)
        else
          go ngen tasks start cnt (idx+1)
      else
        if start < numModules then
          let (childNGen, _) := ngen.mkChild
          let t ← (createImportInitResults
            cctx childNGen env act capacityPerTask start numModules).asTask
          pure (tasks.push t)
        else
          pure tasks
    termination_by env.header.moduleData.size - idx
  let tasks ← go ngen #[] 0 0 0
  let r : InitResults α := tasks.foldl (init := {}) (· ++ ·.get)
  r.errors.forM logImportFailure
  return r.tree.toRefinedDiscrTree

/--
A discriminator tree for the current module's declarations only.

Note. We use different discrimination trees for imported and current module
declarations since imported declarations are typically much more numerous but
not changed while the current module is edited.
-/
structure ModuleDiscrTreeRef (α : Type _) where
  /-- The reference to the `RefinedDiscrTree`. -/
  ref : IO.Ref (RefinedDiscrTree α)

private def createModulePreDiscrTree
    (cctx : Core.Context)
    (ngen : NameGenerator)
    (env : Environment)
    (act : Name → ConstantInfo → MetaM (List (α × List (Key × LazyEntry)))) :
    BaseIO (InitResults α) := do
  let modName := env.header.mainModule
  let data ← ImportErrorData.new
  let r ← env.constants.map₂.foldlM (init := {}) (addConstToPreDiscrTree
    cctx env modName data (← IO.mkRef {}) (← IO.mkRef { env, ngen }) act)
  toInitResults data r

/--
Create a `RefinedDiscrTree` for current module declarations, consisting of all
entries generated by `act` from constants in the current file.
(it gets called by `addConstToPreDiscrTree`)
-/
def createModuleDiscrTree (act : Name → ConstantInfo → MetaM (List (α × List (Key × LazyEntry)))) :
    CoreM (RefinedDiscrTree α) := do
  let env ← getEnv
  let ngen ← getChildNgen
  let ctx ← readThe Core.Context
  let { tree, errors } ← createModulePreDiscrTree ctx ngen env act
  errors.forM logImportFailure
  return tree.toRefinedDiscrTree

/--
Create a reference for a `RefinedDiscrTree` for current module declarations.
-/
def createModuleTreeRef (act : Name → ConstantInfo → MetaM (List (α × List (Key × LazyEntry)))) :
    MetaM (ModuleDiscrTreeRef α) := do
  profileitM Exception "build module discriminator tree" (← getOptions) do
    let t ← createModuleDiscrTree act
    pure { ref := ← IO.mkRef t }

end Lean.Meta.RefinedDiscrTree

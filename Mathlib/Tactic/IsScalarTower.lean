/-
Copyright (c) 2025 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Group.Action.Faithful

/-!
# The `scalar_tower` tactic

A tactic that automatically proves `IsScalarTower A B C` goals.
-/

public meta section

open Lean Meta Elab Tactic

namespace Mathlib.Tactic.IsScalarTower

/-- Try to close `IsScalarTower A B C` via a given lemma applied to `D`.
    `mkArgs A B C D` builds the explicit argument array for the lemma.
    Returns the remaining `IsScalarTower` subgoals, or fails if any subgoal is not. -/
def tryWithIntermediate (goal : MVarId) (lemmaName : Name)
    (mkArgs : Expr → Expr → Expr → Expr → Array Expr) (D : Expr) : MetaM (List MVarId) := do
  goal.withContext do
    let args := (← goal.getType).getAppArgs
    let A := args[0]!
    let B := args[1]!
    let C := args[2]!
    let thm ← mkConstWithFreshMVarLevels lemmaName
    let subgoals ← goal.apply (mkAppN thm (mkArgs A B C D)) { allowSynthFailures := true }
    for sg in subgoals do
      let sgType ← whnf (← sg.getType)
      unless sgType.isAppOf ``IsScalarTower do
        throwError "unexpected subgoal: {← ppExpr sgType}"
    return subgoals

/-- The three lemmas used to split an `IsScalarTower A B C` goal via an intermediate type `D`,
    paired with how to arrange `A B C D` into explicit arguments. -/
def intermediaryLemmas : List (Name × (Expr → Expr → Expr → Expr → Array Expr)) :=
  [(``IsScalarTower.to₁₂₃, fun A B C D => #[A, B, C, D]),
   (``IsScalarTower.to₁₃₄, fun A B C D => #[A, D, B, C]),
   (``IsScalarTower.to₁₂₄, fun A B C D => #[A, B, D, C])]

partial def proveIST (goal : MVarId) (depth : Nat := 10) : MetaM Unit := do
  if depth = 0 then throwError "scalar_tower: max depth reached"
  goal.withContext do
    -- Step 1: Try global instance synthesis.
    let saved ← getMCtx
    try
      goal.assign (← synthInstance (← goal.getType))
      return
    catch _ => setMCtx saved
    -- Step 2: Try a direct local hypothesis.
    let saved ← getMCtx
    try
      goal.assumption
      return
    catch _ => setMCtx saved
    -- Step 3: Try IsScalarTower.of_algebraMap_eq'.
    let saved ← getMCtx
    try
      let ofAlg ← mkConstWithFreshMVarLevels ``IsScalarTower.of_algebraMap_eq'
      let subgoals ← goal.apply ofAlg
      for sg in subgoals do
        let saved2 ← getMCtx
        try sg.refl; continue catch _ => setMCtx saved2
        sg.assumption
      return
    catch _ => setMCtx saved
    -- Step 4: Try each lemma with each candidate type D.
    -- Candidates: Sort-typed local variables, plus type arguments extracted from
    -- Algebra/SMul/IsScalarTower hypotheses (to find coerced types like ↥F).
    let goalArgs := (← goal.getType).getAppArgs
    let A := goalArgs[0]!
    let B := goalArgs[1]!
    let C := goalArgs[2]!
    -- Collect raw candidates: Sort-typed locals, plus type arguments extracted from
    -- structure/class hypotheses (covers Algebra, SMul, IST, Field, Module, etc.,
    -- including coerced types like ↥F from hypotheses such as [Field ↥F]).
    let env ← getEnv
    let mut rawCandidates : Array Expr := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      if decl.type.isSort then
        rawCandidates := rawCandidates.push decl.toExpr
      else if let Expr.const name _ := decl.type.getAppFn then
        if isStructure env name then
          for arg in decl.type.getAppArgs do
            let argTy ← inferType arg
            -- Only add type-valued arguments (Sort but not Prop).
            if argTy.isSort && !argTy.isProp then
              rawCandidates := rawCandidates.push arg
    -- Filter out A, B, C (would cause infinite recursion) and deduplicate,
    -- to avoid an explosion of tryWithIntermediate attempts in large contexts.
    let mut dCandidates : Array Expr := #[]
    for D in rawCandidates do
      if ← isDefEq D A then continue
      if ← isDefEq D B then continue
      if ← isDefEq D C then continue
      if ← dCandidates.anyM (isDefEq D ·) then continue
      dCandidates := dCandidates.push D
    for D in dCandidates do
      for (lemmaName, mkArgs) in intermediaryLemmas do
        let saved ← getMCtx
        try
          let subgoals ← tryWithIntermediate goal lemmaName mkArgs D
          for sg in subgoals do proveIST sg (depth - 1)
          return
        catch _ => setMCtx saved
    throwError "scalar_tower: failed to prove {← ppExpr (← goal.getType)}"

elab "scalar_tower" : tactic =>
  withMainContext do
    liftMetaFinishingTactic proveIST

end Mathlib.Tactic.IsScalarTower

end

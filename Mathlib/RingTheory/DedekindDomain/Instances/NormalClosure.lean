/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Normal closure of Dedekind domains

Consider an extension of `R ⊆ S` of Dedekind domains. It is sometimes useful to work with a larger
extension `R ⊆ S ⊆ T` such that `FractionRing T/ FractionRing R` is Galois.

In this file, we define such an extension and prove several useful results about it.

-/

noncomputable section

attribute [local instance] FractionRing.liftAlgebra

variable (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S]
  [NoZeroSMulDivisors R S] [Module.Finite R S]

local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S
local notation3 "E₀" => IntermediateField.normalClosure K L (AlgebraicClosure L)

-- Several instances are only useful to construct `T` so they are marked as `local`

local instance : Algebra S E₀ := ((algebraMap L E₀).comp (algebraMap S L)).toAlgebra
-- instance : IsScalarTower S L E₀ := IsScalarTower.of_algebraMap_eq' rfl
-- instance : Module.Finite L E₀ := Module.Finite.right K L E₀
-- instance : IsScalarTower S L E₀ := IsScalarTower.of_algebraMap_eq' rfl

def integralNormalClosure := integralClosure S E₀

local notation3 "T" => integralNormalClosure R S
local notation3 "E" => FractionRing T

local instance : IsIntegralClosure T S E₀  := integralClosure.isIntegralClosure S E₀

local instance : IsFractionRing T E₀ :=
  have : Module.Finite L E₀ := Module.Finite.right K L E₀
  have : IsScalarTower S L E₀ := IsScalarTower.of_algebraMap_eq' rfl
  integralClosure.isFractionRing_of_finite_extension L E₀

variable [PerfectField (FractionRing R)]

local instance : Algebra.IsSeparable L E₀ :=
  have : PerfectField L := @Algebra.IsAlgebraic.perfectField K L _ _ _ _ _
  have : Module.Finite L E₀ := Module.Finite.right K L E₀
  have : Algebra.IsAlgebraic L E₀ := Algebra.IsAlgebraic.of_finite L E₀
  Algebra.IsAlgebraic.isSeparable_of_perfectField

instance [IsDedekindDomain S] : IsDedekindDomain T :=
  have : Module.Finite L E₀ := Module.Finite.right K L E₀
  have : IsScalarTower S L E₀ := IsScalarTower.of_algebraMap_eq' rfl
  integralClosure.isDedekindDomain S L E₀

set_option synthInstance.maxHeartbeats 60000 in
set_option maxHeartbeats 600000 in
instance [IsDedekindDomain S] : Module.Finite S T := by
  have : Module.Finite L E₀ := Module.Finite.right K L E₀
  have : IsScalarTower S L E₀ := IsScalarTower.of_algebraMap_eq' rfl
  exact IsIntegralClosure.finite S L E₀ T

instance : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra

instance : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl

instance [IsDedekindDomain S] : Module.Finite R T := Module.Finite.trans S T

local instance : FaithfulSMul S E₀ := (faithfulSMul_iff_algebraMap_injective S E₀).mpr <|
  (FaithfulSMul.algebraMap_injective L E₀).comp (FaithfulSMul.algebraMap_injective S L)

instance : FaithfulSMul R T := (faithfulSMul_iff_algebraMap_injective R T).mpr <|
    (FaithfulSMul.algebraMap_injective S T).comp (FaithfulSMul.algebraMap_injective R S)

set_option synthInstance.maxHeartbeats 100000 in
local instance : IsScalarTower R T E₀ := by

  exact IsScalarTower.to₁₃₄ R S T E₀
  -- have : IsScalarTower K L E₀ := normalClosure.instIsScalarTowerSubtypeMemIntermediateFieldNormalClosure K L (AlgebraicClosure L)
  -- have : IsScalarTower R L E₀ := IsScalarTower.to₁₃₄ R K L E₀
  -- have : IsScalarTower R S E₀ := IsScalarTower.to₁₂₄ R S L E₀
  -- have : IsScalarTower R T E₀ := IsScalarTower.to₁₃₄ R S T E₀

#exit

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
instance [IsDedekindDomain S] : IsGalois K E := by
  refine { to_isSeparable := Algebra.IsAlgebraic.isSeparable_of_perfectField, to_normal := ?_ }
  have : Normal K E₀ := normalClosure.normal K L (AlgebraicClosure L)

  apply Normal.of_equiv_equiv (f := RingEquiv.refl K)
    (g := ((FractionRing.algEquiv T E₀).symm : E₀ ≃+* E))
  ext x
  refine x.ind fun ⟨r, s⟩ ↦ ?_
  simp only [RingEquiv.coe_ringHom_refl, RingHomCompTriple.comp_eq, FractionRing.mk_eq_div,
    map_div₀, AlgEquiv.symm_toRingEquiv, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
  rw [← IsScalarTower.algebraMap_apply R K E₀]
  rw [← IsScalarTower.algebraMap_apply R K E₀]
  rw [← IsScalarTower.algebraMap_apply R K E]
  rw [← IsScalarTower.algebraMap_apply R K E]
  rw [← AlgEquiv.symm_toRingEquiv]
  rw [AlgEquiv.coe_ringEquiv]
  rw [IsScalarTower.algebraMap_apply R T E₀]
  rw [IsScalarTower.algebraMap_apply R T E₀]
  rw [AlgEquiv.commutes, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]

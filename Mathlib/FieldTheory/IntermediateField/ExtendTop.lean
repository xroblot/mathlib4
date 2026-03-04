/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Extending the top of an intermediate field

Given a tower of field extensions `M/L/K` and an intermediate field `F` of `L/K`,
`IntermediateField.extendTop F M` is `F` viewed as an intermediate field of the larger
extension `M/K`, defined as the image of `F` under the embedding `L →ₐ[K] M`.

This file establishes algebra and scalar tower instances for `F.extendTop M`, and shows that
some algebraic properties are inherited by `F.extendTop M`.

-/

@[expose] public section

namespace IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (F : IntermediateField K L)
  (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/--
Docs.
-/
abbrev extendTop : IntermediateField K M := F.map (Algebra.algHom K L M)

/--
Docs.
-/
@[simps! apply_coe]
noncomputable def extendTopEquiv : F ≃ₐ[K] (F.extendTop M) := F.equivMap (Algebra.algHom K L M)

namespace extendTop

noncomputable instance algebra : Algebra F (F.extendTop M) where
  smul s x := by
    have y := mem_map.mp x.prop
    refine ⟨s • x, ?_⟩
    refine ⟨s • y.choose, ?_, ?_⟩
    · rw [Algebra.smul_def]
      refine F.mul_mem ?_ y.choose_spec.1
      simp only [algebraMap_apply, SetLike.coe_mem]
    · rw [RingHom.coe_coe, Algebra.smul_def, map_mul, y.choose_spec.2]
      change algebraMap L M _ * _ = _
      rw [← IsScalarTower.algebraMap_apply F L M, Algebra.smul_def]
  algebraMap := (algebraMap F M).codRestrict (F.extendTop M) (by
    intro x
    refine ⟨x, x.prop, ?_⟩
    rw [IsScalarTower.algebraMap_apply F L M]
    rfl)
  commutes' _ _ := CommRing.mul_comm _ _
  smul_def' c x := by
    rw [Subtype.ext_iff]
    convert_to c • (x : M) = _
    rw [MulMemClass.coe_mul, RingHom.codRestrict_apply, ← Algebra.smul_def]

instance : IsScalarTower F (F.extendTop M) M := IsScalarTower.of_algebraMap_eq' rfl

variable (R S T : Type*) [CommRing R] [CommRing S] [Algebra S F]

variable [Algebra S M] [IsScalarTower S F M]

noncomputable instance algebra' : Algebra S (F.extendTop M) where
  smul s x := by
    refine ⟨s • x, ?_⟩
    rw [Algebra.smul_def]
    refine (F.extendTop M).mul_mem ?_ x.prop
    simp [IsScalarTower.algebraMap_apply S F M,
      IsScalarTower.algebraMap_apply F (F.extendTop M) M]
  algebraMap := ((algebraMap S M).codRestrict (F.extendTop M) (by
      intro x
      rw [Algebra.algebraMap_eq_smul_one, ← smul_one_smul F x (1 : M),
        ← Algebra.algebraMap_eq_smul_one, IsScalarTower.algebraMap_apply F (F.extendTop M) M]
      simp))
  commutes' _ _ := Subtype.ext <| by simp [Algebra.commutes]
  smul_def' s x := Subtype.ext <| by
    convert_to s • (x : M) = _
    rw [MulMemClass.coe_mul, RingHom.codRestrict_apply, ← Algebra.smul_def]

-- Check there is no diamond
example [Algebra S K] [IsScalarTower S K M] :
    ((F.extendTop M).algebra' : Algebra S (F.extendTop M)) =
      (algebra' F M S : Algebra S (F.extendTop M)) := rfl

-- Check there is no diamond
example : (algebra _ _ : Algebra F (F.extendTop M)) =
    (algebra' _ _ _ : Algebra F (F.extendTop M)) := rfl

instance : IsScalarTower S (F.extendTop M) M := IsScalarTower.of_algebraMap_eq' rfl

instance : IsScalarTower S F (F.extendTop M) := IsScalarTower.to₁₂₃ S F (F.extendTop M) M

instance [Algebra R S] [Algebra R F] [Algebra R M] [IsScalarTower R F M] [IsScalarTower R S M] :
    IsScalarTower R S (F.extendTop M) := IsScalarTower.to₁₂₃ R S (F.extendTop M) M

/--
Docs.
-/
@[simps! apply_coe]
noncomputable def _root_.IntermediateField.extendTopEquiv' : F ≃ₐ[S] (F.extendTop M) :=
  AlgEquiv.ofBijective (Algebra.algHom S F (F.extendTop M)) (extendTopEquiv F M).bijective

instance isFractionRing [IsFractionRing S F] :
    IsFractionRing S (F.extendTop M) :=
  .of_algEquiv (R := S) (L := F.extendTop M) (K := F) <| F.extendTopEquiv' M S

instance isIntegralClosure [Algebra R F] [Algebra R M] [IsScalarTower R F M]
    [IsIntegralClosure S R F] :
    IsIntegralClosure S R (F.extendTop M) := by
  refine .of_algEquiv S (F.extendTopEquiv' M R) ?_
  ext
  simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    extendTopEquiv'_apply_coe]
  rw [← IsScalarTower.algebraMap_apply]
  rfl

end IntermediateField.extendTop

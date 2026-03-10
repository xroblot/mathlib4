module

public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois

@[expose] public section

-- section Misc

-- theorem AlgEquiv.restrictScalars_smul (R : Type*) {S A : Type*} [CommSemiring R] [CommSemiring S]
--     [Semiring A] [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] (f : A ≃ₐ[S] A)
--     (x : A) : (restrictScalars R f) • x = f • x := by


-- end Misc

open AlgEquiv MulAction

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L] (F : Type*) [Field F]
  [Algebra K F] [Algebra F L] [IsScalarTower K F L] [Normal K F]

theorem AlgEquiv.algebraMap_restrictNormalHom_smul (x : F) (g : Gal(L/K)) :
    algebraMap F L (AlgEquiv.restrictNormalHom F g • x) = g • (algebraMap F L x) := by
  rw [AlgEquiv.smul_def, AlgEquiv.smul_def]
  exact AlgEquiv.restrictNormal_commutes _ _ _

open Pointwise

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [MulSemiringAction Gal(L/K) B]
  [Algebra B L] [SMulDistribClass Gal(L/K) B L] [FaithfulSMul B L] [Algebra A L]
  [IsScalarTower A B L]

section Algebra

variable [Algebra A F] [MulSemiringAction Gal(F/K) A] [SMulDistribClass Gal(F/K) A F]
  [IsScalarTower A F L]

theorem AlgEquiv.algebraMap_restrictNormalHom_smul' (x : A) (g : Gal(L/K)) :
    algebraMap A B (AlgEquiv.restrictNormalHom F g • x) = g • (algebraMap A B x) := by
  apply FaithfulSMul.algebraMap_injective B L
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A F L, algebraMap.smul',
    algebraMap_restrictNormalHom_smul, ← IsScalarTower.algebraMap_apply, algebraMap.smul',
    ← IsScalarTower.algebraMap_apply]

open Ideal

theorem Ideal.comap_smul_eq_restrictNormalHom_smul_comap (g : Gal(L/K)) (P : Ideal B) :
    Ideal.comap (algebraMap A B) (g • P) =
      AlgEquiv.restrictNormalHom F g • Ideal.comap (algebraMap A B) P := by
  ext x
  rw [mem_comap, mem_pointwise_smul_iff_inv_smul_mem, mem_pointwise_smul_iff_inv_smul_mem,
    mem_comap, ← map_inv, algebraMap_restrictNormalHom_smul']

variable (K L) {A B}

/--
Docs.
-/
@[simps! apply_coe]
noncomputable def Ideal.stabilizerMapOfLiesOver (P : Ideal B) (p : Ideal A) [P.LiesOver p] :
    stabilizer Gal(L/K) P →* stabilizer Gal(F/K) p :=
  ((AlgEquiv.restrictNormalHom F).restrict (stabilizer Gal(L/K) P)).codRestrict
    (stabilizer Gal(F/K) p)
  (fun ⟨g, hg⟩ ↦ by
    have := congr_arg (Ideal.comap (algebraMap A B)) hg
    rwa [comap_smul_eq_restrictNormalHom_smul_comap F, ← under_def, ← over_def P p] at this)

theorem Ideal.stabilizerMapOfLiesOver_surjective [IsFractionRing A F] [IsFractionRing B L]
    [IsGalois F L] [IsIntegrallyClosed A] [Algebra.IsIntegral A B] (P : Ideal B) (p : Ideal A)
    [P.IsPrime] [P.LiesOver p] [IsGalois K L] [FiniteDimensional F L] [MulSemiringAction Gal(L/F) B]
    [SMulDistribClass Gal(L/F) B L] :
    Function.Surjective (Ideal.stabilizerMapOfLiesOver K L F P p) := by
  have : IsGaloisGroup Gal(L/F) A B := .of_isFractionRing _ _ _ F L
  intro ⟨g, hg⟩
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L g
  have : (σ⁻¹ • P).LiesOver p := by
    rwa [liesOver_iff, under_def, Ideal.comap_smul_eq_restrictNormalHom_smul_comap F, ← under_def,
      ← over_def P p, map_inv, eq_inv_smul_iff]
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p P (σ⁻¹ • P) Gal(L/F)
  refine ⟨⟨σ * τ.restrictScalars K, ?_⟩, ?_⟩
  · have : restrictScalars K τ • P = τ • P := by
      ext x
      have : (restrictScalars K τ)⁻¹ • x = τ⁻¹ • x := by
        apply FaithfulSMul.algebraMap_injective B L
        rw [algebraMap.smul', algebraMap.smul', AlgEquiv.smul_def, AlgEquiv.smul_def, coe_inv,
          coe_inv, restrictScalars_symm_apply]
      rw [mem_pointwise_smul_iff_inv_smul_mem, mem_pointwise_smul_iff_inv_smul_mem, this]
    rw [mem_stabilizer_iff, mul_smul, this, hτ, smul_inv_smul]
  · simp only [Subtype.ext_iff, stabilizerMapOfLiesOver_apply_coe, map_mul, mul_eq_left,
      AlgEquiv.ext_iff, one_apply]
    intro _
    apply FaithfulSMul.algebraMap_injective F L
    simp [restrictNormalHom]

end Algebra

set_option backward.isDefEq.respectTransparency false in
theorem Ideal.stabilizerMapOfLiesOver_ker (E : IntermediateField K L) [Normal K E]
    [Algebra A E] [MulSemiringAction Gal(E/K) A] [SMulDistribClass Gal(E/K) A E]
    [IsScalarTower A E L] (p : Ideal A) (P : Ideal B) [P.LiesOver p] :
    (Ideal.stabilizerMapOfLiesOver K L E P p).ker =
      E.fixingSubgroup.subgroupOf (stabilizer Gal(L/K) P) := by
  unfold stabilizerMapOfLiesOver
  rw [MonoidHom.ker_codRestrict, MonoidHom.ker_restrict, IntermediateField.restrictNormalHom_ker]

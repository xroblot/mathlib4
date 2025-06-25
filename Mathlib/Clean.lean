import Mathlib

open nonZeroDivisors NumberField

theorem Submodule.span_mono_left {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M]
    [Module R M] [Module S M] [SMul R S] [IsScalarTower R S M] {s : Set M} :
    (span R s : Set M) ≤ span S s := by
  rw [← Submodule.span_span_of_tower R S]
  exact Submodule.subset_span

theorem differentIdeal_ne_bot' (A K B L : Type*) [CommRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] [CommRing B] [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsDomain A] [IsIntegrallyClosed A] [IsDedekindDomain B] [NoZeroSMulDivisors A B]
    [Module.Finite A B] [Algebra.IsSeparable K L] :
    differentIdeal A B ≠ ⊥ := by
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization _ K _ _
  have : FiniteDimensional K L := Module.Finite_of_isLocalization A B _ _ A⁰
  rw [ne_eq, ← FractionalIdeal.coeIdeal_inj (K := L), coeIdeal_differentIdeal (K := K)]
  simp

open nonZeroDivisors Algebra FractionalIdeal
section numberfield

open NumberField

variable (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

theorem differentIdeal_eq_differentIdeal_mul_differentIdeal' :
    differentIdeal (𝓞 K) (𝓞 M) =
       differentIdeal (𝓞 L) (𝓞 M) *
        (differentIdeal (𝓞 K) (𝓞 L)).map (algebraMap (𝓞 L) (𝓞 M)) :=
  differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 K) K L (𝓞 L) (𝓞 M) M

end numberfield
namespace IntermediateField.LinearDisjoint

open Submodule IntermediateField

variable {A K C M : Type*} [CommRing A] [Field K] [CommRing C] [Field M] [Algebra K M]
  [Algebra A K] [IsFractionRing A K] [Algebra C M] [Algebra A M] [IsScalarTower A K M]
  {L₁ L₂ : IntermediateField K M} {B₁ B₂ : Type*} [CommRing B₁] [CommRing B₂] [Algebra B₁ L₁]
  [Algebra B₂ L₂] [Algebra A B₂] [Algebra B₁ C] [Algebra B₂ C] [Algebra B₁ M] [Algebra B₂ M]
  [IsScalarTower A B₂ L₂] [IsScalarTower B₁ C M] [IsScalarTower B₂ C M] [IsScalarTower B₁ L₁ M]
  [IsScalarTower B₂ L₂ M] [Algebra.IsSeparable K M] [FiniteDimensional K M]

variable (A C B₁ B₂) in
theorem traceDual_le_span_traceDual' [IsLocalization (algebraMapSubmonoid B₂ A⁰) L₂]
    [Module.Free A B₂] [Module.Finite A B₂]
    (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤) :
    traceDual B₁ L₁ (1 : Submodule C M) ≤
      span C (algebraMap L₂ M '' (traceDual A K (1 : Submodule B₂ L₂))) := by
  intro x hx
  let b₂ := (Module.Free.chooseBasis A B₂).localizationLocalization K A⁰ L₂
  have h₂' : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
    simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂
  let bM : Basis _ L₁ M := h₁.basisOfBasisRight h₂' b₂.traceDual
  rw [← bM.sum_repr x]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rsuffices ⟨c, hc⟩ : bM.repr x i ∈ (algebraMap B₁ L₁).range := by
    have : (h₁.basisOfBasisRight h₂' b₂).traceDual = bM := by
      refine (DFunLike.ext'_iff.trans Basis.traceDual_eq_iff).mpr fun _ _ ↦ ?_
      rw [h₁.basisOfBasisRight_apply, h₁.basisOfBasisRight_apply, traceForm_apply, ← map_mul,
        h₁.trace_algebraMap_eq h₂, b₂.trace_traceDual_mul, MonoidWithZeroHom.map_ite_one_zero]
    rw [← this, (h₁.basisOfBasisRight h₂' b₂).traceDual_repr_apply x i]
    refine mem_traceDual.mp hx _ ?_
    rw [mem_one, h₁.basisOfBasisRight_apply, Basis.localizationLocalization_apply,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B₂ C M]
    exact ⟨_, rfl⟩
  rw [← hc, ← algebra_compatible_smul L₁, algebra_compatible_smul C]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine ⟨b₂.traceDual i, ?_, by rw [h₁.basisOfBasisRight_apply]⟩
  rw [SetLike.mem_coe, ← restrictScalars_mem A, traceDual_span_of_basis A _ b₂
    (by rw [Basis.localizationLocalization_span K A⁰ L₂]; ext; simp)]
  exact Submodule.subset_span <| Set.mem_range_self i

variable (A C B₁ B₂) in
theorem traceDual_le_span_traceDual [IsLocalization (algebraMapSubmonoid B₂ A⁰) L₂]
    [Module.Free A B₂] [Module.Finite A B₂]
    (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤) :
    (traceDual B₁ L₁ (1 : Submodule C M)).restrictScalars B₁ ≤
      span B₁ (algebraMap L₂ M '' (traceDual A K (1 : Submodule B₂ L₂))) := by
  intro x hx
  let b₂ := (Module.Free.chooseBasis A B₂).localizationLocalization K A⁰ L₂
  have h₂' : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
    simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂
  let bM : Basis _ L₁ M := h₁.basisOfBasisRight h₂' b₂.traceDual
  rw [← bM.sum_repr x]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rsuffices ⟨c, hc⟩ : bM.repr x i ∈ (algebraMap B₁ L₁).range := by
    have : (h₁.basisOfBasisRight h₂' b₂).traceDual = bM := by
      refine (DFunLike.ext'_iff.trans Basis.traceDual_eq_iff).mpr fun _ _ ↦ ?_
      rw [h₁.basisOfBasisRight_apply, h₁.basisOfBasisRight_apply, traceForm_apply, ← map_mul,
        h₁.trace_algebraMap_eq h₂, b₂.trace_traceDual_mul, MonoidWithZeroHom.map_ite_one_zero]
    rw [← this, (h₁.basisOfBasisRight h₂' b₂).traceDual_repr_apply x i]
    refine mem_traceDual.mp hx _ ?_
    rw [mem_one, h₁.basisOfBasisRight_apply, Basis.localizationLocalization_apply,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B₂ C M]
    exact ⟨_, rfl⟩
  rw [← hc, ← algebra_compatible_smul L₁]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine ⟨b₂.traceDual i, ?_, by rw [h₁.basisOfBasisRight_apply]⟩
  rw [SetLike.mem_coe, ← restrictScalars_mem A, traceDual_span_of_basis A _ b₂
    (by rw [Basis.localizationLocalization_span K A⁰ L₂]; ext; simp)]
  exact Submodule.subset_span <| Set.mem_range_self i

variable [IsDomain A] [IsDomain B₁]
  [IsIntegrallyClosed A] [IsIntegrallyClosed B₁] [IsDedekindDomain B₂] [IsDedekindDomain C]
  [IsFractionRing B₁ L₁] [IsFractionRing B₂ L₂] [IsFractionRing C M]
  [IsIntegralClosure B₂ A L₂] [IsIntegralClosure C B₂ M] [IsIntegralClosure C B₁ M]
  [NoZeroSMulDivisors B₁ C] [NoZeroSMulDivisors B₂ C]

-- variable (A B₁ B₂ C) in
-- -- That's essentially a weaker version of `traceDual_le_span_traceDual'`
-- theorem differentIdeal_dvd_differentIdeal_map [Module.Free A B₂] [Module.Finite A B₂]
--     (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤) :
--     differentIdeal B₁ C ∣ (differentIdeal A B₂).map (algebraMap B₂ C) := by
--   have := IsIntegralClosure.isLocalization A K L₂ B₂
--   have := IsIntegralClosure.isLocalization B₂ L₂ M C
--   rw [Ideal.dvd_iff_le, ← coeIdeal_le_coeIdeal' C⁰ (P := M) le_rfl, coeIdeal_differentIdeal B₁ L₁,
--     le_inv_comm _ (by simp), ← extended_coeIdeal_eq_map_algebraMap L₂ M, ← extended_inv,
--     coeIdeal_differentIdeal A K, inv_inv, ← coe_le_coe, coe_dual_one, coe_extended_eq_span,
--     ← coeToSet_coeToSubmodule, coe_dual_one]
--   · convert traceDual_le_span_traceDual A C B₁ B₂ h₁ h₂
--     exact (IsLocalization.algebraMap_eq_map_map_submonoid B₂⁰ C L₂ M).symm
--   · exact coeIdeal_ne_zero.mpr <| differentIdeal_ne_bot' A K B₂ L₂
--   · exact coeIdeal_ne_zero.mpr <| Ideal.map_ne_bot_of_ne_bot <| differentIdeal_ne_bot' A K B₂ L₂

variable [Algebra A B₁] [IsDedekindDomain B₁] [NoZeroSMulDivisors A B₁]
  [Algebra A C] [IsScalarTower A B₁ L₁] [IsScalarTower A C M] [IsIntegralClosure B₁ A L₁]
  [IsIntegralClosure C A M] [NoZeroSMulDivisors A C] [IsScalarTower K L₂ M] [IsScalarTower K L₁ M]

-- theorem differentIdeal_map_eq_differentIdeal [Module.Free A B₁] [Module.Finite A B₁]
--     [Module.Free A B₂] [Module.Finite A B₂] (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)
--     (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
--       ((differentIdeal A B₂).map (algebraMap B₂ C))) :
--     (differentIdeal A B₁).map (algebraMap B₁ C) = differentIdeal B₂ C := by
--   have := IsIntegralClosure.isLocalization B₁ L₁ M C
--   have := IsIntegralClosure.isLocalization B₂ L₂ M C
--   have main := (differentIdeal_eq_differentIdeal_mul_differentIdeal
--     A K L₁ B₁ C M).symm.trans (differentIdeal_eq_differentIdeal_mul_differentIdeal A K L₂ B₂ C M)
--   apply dvd_antisymm'
--   · have h' : IsCoprime (differentIdeal B₂ C) (differentIdeal B₁ C) := by
--       refine (h₃.of_isCoprime_of_dvd_right ?_).of_isCoprime_of_dvd_left ?_
--       · exact differentIdeal_dvd_differentIdeal_map A C B₁ B₂ h₁ h₂
--       · exact differentIdeal_dvd_differentIdeal_map A C B₂ B₁ h₁.symm (by rwa [sup_comm])
--     exact h'.dvd_of_dvd_mul_left (dvd_of_mul_right_eq _ main.symm)
--   · exact h₃.dvd_of_dvd_mul_right (dvd_of_mul_left_eq _ main)

variable (A C B₁ B₂) in
theorem traceDual_eq_span_traceDual [Module.Finite A B₂] [Module.Free A B₂]
    [NoZeroSMulDivisors A B₂] (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
      ((differentIdeal A B₂).map (algebraMap B₂ C))) :
    span B₁ (algebraMap L₂ M '' (traceDual A K (1 : Submodule B₂ L₂))) =
      (traceDual B₁ L₁ (1 : Submodule C M)).restrictScalars B₁ := by
  apply le_antisymm
  · suffices span C (algebraMap L₂ M '' (traceDual A K (1 : Submodule B₂ L₂))) ≤
        traceDual B₁ L₁ (1 : Submodule C M) by
      refine SetLike.coe_subset_coe.mp (subset_trans ?_ this)
      rw [← Submodule.span_span_of_tower B₁ C]
      exact Submodule.subset_span
    have := IsIntegralClosure.isLocalization B₂ L₂ M C
    rw [← coe_dual_one, coeToSet_coeToSubmodule, ← coe_extended_eq_span_algebraMap, ← coe_dual_one,
      coe_le_coe, ← inv_inv (dual B₁ L₁ 1), ← le_inv_comm (inv_ne_zero (by simp)),
      ← extended_inv _ (by simp), ← coeIdeal_differentIdeal A K, ← coeIdeal_differentIdeal B₁ L₁,
      extended_coeIdeal_eq_map_algebraMap L₂ M, coeIdeal_le_coeIdeal' _ le_rfl, ← Ideal.dvd_iff_le]
    · have := (differentIdeal_eq_differentIdeal_mul_differentIdeal A K L₂ B₂ C M).symm.trans
          (differentIdeal_eq_differentIdeal_mul_differentIdeal A K L₁ B₁ C M)
      exact h₃.symm.dvd_of_dvd_mul_right (dvd_of_mul_left_eq _ this)
    · exact extended_ne_zero _ _ (FaithfulSMul.algebraMap_injective _ _) (by simp)
  · have := IsIntegralClosure.isLocalization A K L₂ B₂
    exact traceDual_le_span_traceDual A C B₁ B₂ h₁ h₂

example
    [IsScalarTower A L₁ M]
    [IsScalarTower A B₂ M]
    [Module.Free A B₁]
    [Module.Finite A B₁]
    [NoZeroSMulDivisors A B₂]
    (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
      ((differentIdeal A B₂).map (algebraMap B₂ C)))
    {ι : Type*} (b : Basis ι A B₁) :
    span B₂ (Set.range (algebraMap B₁ M ∘ b)) =
      LinearMap.range (IsScalarTower.toAlgHom B₂ C M) := by
  classical
  have : Finite ι := Module.Finite.finite_basis b
  have h_main : (traceDual B₂ L₂ (1 : Submodule C M)).restrictScalars B₂ =
      span B₂ (algebraMap L₁ M '' (traceDual A K (1 : Submodule B₁ L₁))) :=
    (traceDual_eq_span_traceDual A C B₂ B₁ h₁.symm (by rwa [sup_comm]) h₃.symm).symm
  convert congr_arg (Submodule.restrictScalars B₂) <|
    congr_arg coeToSubmodule <| (1 : FractionalIdeal C⁰ M).dual_dual B₂ L₂
  · rw [coe_dual _ _ (by simp), coe_dual_one]
    rw [restrictScalars_traceDual, h_main]
    have : IsLocalization (algebraMapSubmonoid B₁ A⁰) L₁ :=
      IsIntegralClosure.isLocalization A K L₁ B₁
    let b₁ := b.localizationLocalization K A⁰ L₁
    have := Submodule.traceDual_span_of_basis (A := A) (1 : Submodule B₁ L₁) b₁ ?_
    · rw [← Submodule.coe_restrictScalars A, this, ← IsScalarTower.coe_toAlgHom' A L₁ M,
        ← map_coe, map_span, span_span_of_tower, IsScalarTower.coe_toAlgHom', ← Set.range_comp]
      have h₂' : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
        simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂
      have : algebraMap L₁ M ∘ b₁.traceDual = (h₁.basisOfBasisLeft h₂' b₁).traceDual := by
        rw [eq_comm, Basis.traceDual_eq_iff]
        intro i j
        simp only [Function.comp_apply, basisOfBasisLeft_apply, traceForm_apply]
        rw [← map_mul, h₁.symm.trace_algebraMap_eq (by rwa [sup_comm])]
        rw [b₁.trace_traceDual_mul i j, MonoidWithZeroHom.map_ite_one_zero]
      rw [this, (traceForm L₂ M).dualSubmodule_span_of_basis (traceForm_nondegenerate L₂ M),
        ← Basis.traceDual_def, Basis.traceDual_traceDual]
      congr!
      ext
      rw [Function.comp_apply, basisOfBasisLeft_apply, Basis.localizationLocalization_apply,
        ← IsScalarTower.algebraMap_apply]
    · rw [b.localizationLocalization_span K A⁰ L₁]
      ext; simp
  · ext; simp

#exit


    have : IsLocalization (algebraMapSubmonoid B₁ A⁰) L₁ :=
      IsIntegralClosure.isLocalization A K L₁ B₁
    have : IsLocalization (algebraMapSubmonoid C B₁⁰) M :=
      IsIntegralClosure.isLocalization B₁ L₁ M C
    have h₂' : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
      simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂
    let b₁ := b.localizationLocalization K A⁰ L₁
    have : algebraMap B₁ M ∘ b = (h₁.basisOfBasisRight h₂' b₁) := by
      sorry
    rw [this]
    have := Submodule.traceDual_span_of_basis (A := B₂) (K := L₂) (B := C) (L := M)
      (I := span C (Set.range (h₁.basisOfBasisRight h₂' b₁).traceDual)) (ι := ι)
      (h₁.basisOfBasisRight h₂' b₁).traceDual ?_
    sorry
  · ext; simp


#exit
  classical
  have : Finite ι := sorry
  convert congr_arg (Submodule.restrictScalars B₂) <|
    congr_arg coeToSubmodule <| (1 : FractionalIdeal C⁰ M).dual_dual B₂ L₂
  · have : IsLocalization (algebraMapSubmonoid B₁ A⁰) L₁ :=
      IsIntegralClosure.isLocalization A K L₁ B₁
    have : IsLocalization (algebraMapSubmonoid C B₁⁰) M :=
      IsIntegralClosure.isLocalization B₁ L₁ M C
    have h₂' : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
      simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂
    let b₁ := b.localizationLocalization K A⁰ L₁
    have : algebraMap B₁ M ∘ b = (h₁.basisOfBasisRight h₂' b₁) := by
      sorry
    rw [this]
    have := Submodule.traceDual_span_of_basis (A := B₂) (K := L₂) (B := C) (L := M)
      (I := span C (Set.range (h₁.basisOfBasisRight h₂' b₁).traceDual)) (ι := ι)
      (h₁.basisOfBasisRight h₂' b₁).traceDual ?_
    sorry


    rw [Basis.traceDual_traceDual] at this
    rw [← this]
    congr

    have h := congr_arg ((↑) : Ideal C → FractionalIdeal C⁰ M)
        (differentIdeal_map_eq_differentIdeal h₁ h₂ h₃)
    rw [← inv_inj, coeIdeal_differentIdeal B₂ L₂, ← extended_coeIdeal_eq_map_algebraMap L₁ M,
      ← extended_inv, coeIdeal_differentIdeal A K, inv_inv, inv_inv] at h
    replace h := congr_arg coeToSubmodule <| h
    rw [coe_extended_eq_span, coe_dual_one, ← coeToSet_coeToSubmodule, coe_dual_one] at h
    have := IsLocalization.algebraMap_eq_map_map_submonoid B₁⁰ C L₁ M
    erw [← this] at h
    rw [coe_dual, coe_dual_one]
    rw [← h]
    congr

#exit
    let b₁ := b.localizationLocalization K A⁰ L₁
    have : (traceDual A K (1 : Submodule B₁ L₁) : Set L₁) = span A (Set.range b₁.traceDual) := by
      rw [← Submodule.traceDual_span_of_basis A (1 : Submodule B₁ L₁),
        Submodule.coe_restrictScalars]
      rw [b.localizationLocalization_span K A⁰ L₁]
      ext; simp
    rw [this, ← IsScalarTower.coe_toAlgHom' A L₁ M, ← map_coe, map_span, span_span_of_tower]
    rw [IsScalarTower.coe_toAlgHom', ← Set.range_comp]
    have h₂' : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
      simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂
    have : algebraMap L₁ M ∘ b₁.traceDual = (h₁.basisOfBasisRight h₂' b₁).traceDual := by
      rw [eq_comm, Basis.traceDual_eq_iff]
      intro i j
      simp only [Function.comp_apply, basisOfBasisRight_apply, traceForm_apply]
      rw [← map_mul, h₁.symm.trace_algebraMap_eq (by rwa [sup_comm])]
      rw [b₁.trace_traceDual_mul i j, MonoidWithZeroHom.map_ite_one_zero]
    rw [this]
    have := Submodule.traceDual_span_of_basis (A := B₂) (K := L₂) (B := C) (L := M)
      (I := span C (Set.range (h₁.basisOfBasisRight h₂' b₁).traceDual)) (ι := ι)
      (h₁.basisOfBasisRight h₂' b₁).traceDual ?_
    · rw [this]
      congr
      simp
      congr!
      ext
      simp
      sorry
    · ext
      simp
      sorry
    · simp
    · sorry
  · ext
    simp [mem_one_iff]

end IntermediateField.LinearDisjoint

import Mathlib

open nonZeroDivisors NumberField

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

theorem LinearMap.BilinForm.dualBasis_eq_iff {V : Type*} {K : Type*} [Field K] [AddCommGroup V]
    [Module K V] {ι : Type*} [DecidableEq ι] [Finite ι] (B : LinearMap.BilinForm K V)
    (hB : B.Nondegenerate) (b : Basis ι K V) (v : ι → V) :
    B.dualBasis hB b = v ↔ ∀ i j, B (v i) (b j) = if j = i then 1 else 0 :=
  ⟨fun h _ _ ↦ by rw [← h, apply_dualBasis_left],
    fun h ↦ funext fun _ ↦ (B.dualBasis hB b).ext_elem_iff.mpr fun _ ↦ by
      rw [dualBasis_repr_apply, dualBasis_repr_apply, apply_dualBasis_left, h]⟩

/-- Doc -/
noncomputable def Basis.traceDual {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) :
    Basis ι K L :=
  (Algebra.traceForm K L).dualBasis (traceForm_nondegenerate K L) b

@[simp]
theorem Basis.traceDual_repr_apply {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) (x : L) (i : ι) :
    (b.traceDual).repr x i = (Algebra.traceForm K L x) (b i) :=
  (Algebra.traceForm K L).dualBasis_repr_apply _ b _ i

theorem Basis.trace_traceDual_mul {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) (i j : ι) :
    Algebra.trace K L ((b.traceDual i) * (b j)) = if j = i then 1 else 0 :=
  (Algebra.traceForm K L).apply_dualBasis_left _ _ i j

theorem Basis.trace_mul_traceDual {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) (i j : ι) :
    Algebra.trace K L ((b i) * (b.traceDual j)) = if i = j then 1 else 0 := by
  refine (Algebra.traceForm K L).apply_dualBasis_right _ (Algebra.traceForm_isSymm K) _ i j

@[simp]
theorem Basis.traceDual_traceDual {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) :
    b.traceDual.traceDual = b :=
  (Algebra.traceForm K L).dualBasis_dualBasis _ (Algebra.traceForm_isSymm K) _

@[simp]
theorem Basis.traceDual_involutive (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι] :
    Function.Involutive (Basis.traceDual : Basis ι K L → Basis ι K L) :=
  fun b ↦ traceDual_traceDual b

theorem Basis.traceDual_injective (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι] :
    Function.Injective (Basis.traceDual : Basis ι K L → Basis ι K L) :=
  (traceDual_involutive K L).injective

@[simp]
theorem Basis.traceDual_inj {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b b' : Basis ι K L):
    b.traceDual = b'.traceDual ↔ b = b' :=
  (traceDual_injective K L).eq_iff

theorem Basis.traceDual_eq_iff {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    {b : Basis ι K L} {v : ι → L} :
    b.traceDual = v ↔
      ∀ i j, Algebra.traceForm K L (v i) (b j) = if j = i then 1 else 0 :=
  (Algebra.traceForm K L).dualBasis_eq_iff (traceForm_nondegenerate K L) b v

@[simp]
theorem Submodule.traceDual_restrictScalars (A K : Type*) {L B : Type*} [CommRing A] [Field K]
    [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] (I : Submodule B L) :
    (Submodule.traceDual A K I).restrictScalars A =
      (Algebra.traceForm K L).dualSubmodule (I.restrictScalars A) := rfl

theorem Submodule.traceDual_span_of_basis (A : Type*) {K L B : Type*}
    [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B]
    [Algebra K L] [Algebra A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsScalarTower A K L] [IsScalarTower A B L] (I : Submodule B L) {ι : Type*} [Finite ι]
    [DecidableEq ι] (b : Basis ι K L) (hb : I.restrictScalars A = Submodule.span A (Set.range b)) :
    (Submodule.traceDual A K I).restrictScalars A = Submodule.span A (Set.range b.traceDual) := by
  rw [traceDual_restrictScalars, hb]
  exact (Algebra.traceForm K L).dualSubmodule_span_of_basis (traceForm_nondegenerate K L) b

instance (K : Type*) [Field K] [NumberField K] (F : Type*) [Field F] [NumberField F] [Algebra F K] :
    IsLocalization (Algebra.algebraMapSubmonoid (𝓞 K) (𝓞 F)⁰) K := by
  refine IsLocalization.of_le (Algebra.algebraMapSubmonoid (𝓞 K) ℤ⁰) _ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, by simpa using ne_zero ha, by simp⟩
  · rintro _ ⟨x, hx, rfl⟩
    simpa using ne_zero hx

open nonZeroDivisors Algebra FractionalIdeal
section numberfield

open NumberField

variable (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

theorem differentIdeal_eq_differentIdeal_mul_differentIdeal' :
    differentIdeal (𝓞 K) (𝓞 M) =
       differentIdeal (𝓞 L) (𝓞 M) *
        (differentIdeal (𝓞 K) (𝓞 L)).map (algebraMap (𝓞 L) (𝓞 M)) :=
  differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 K) K (𝓞 L) L (𝓞 M) M

end numberfield
namespace IntermediateField.LinearDisjoint

open Submodule IntermediateField

variable {A K C M : Type*} [CommRing A] [Field K] [CommRing C] [Field M] [Algebra K M]
  [Algebra A K] [IsFractionRing A K] [Algebra C M]
  {L₁ L₂ : IntermediateField K M} {B₁ B₂ : Type*} [CommRing B₁] [CommRing B₂]
  [Algebra B₁ L₁] [Algebra B₂ L₂] [Algebra A B₂] [Algebra A L₂] [Algebra B₁ C] [Algebra B₂ C]
  [Algebra B₁ M] [Algebra B₂ M] [IsScalarTower A K L₂] [IsScalarTower A B₂ L₂]
  [IsScalarTower B₁ C M] [IsScalarTower B₂ C M] [IsScalarTower B₁ L₁ M] [IsScalarTower B₂ L₂ M]
  [Algebra.IsSeparable K M] [FiniteDimensional K M]

variable (A B₁ B₂ C) in
theorem traceDual_le_span_traceDual [IsLocalization (algebraMapSubmonoid B₂ A⁰) L₂]
    [Module.Free A B₂] [Module.Finite A B₂]
    (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤) :
    traceDual B₁ L₁ (1 : Submodule C M) ≤
      span C (algebraMap L₂ M '' (traceDual A K (1 : Submodule B₂ L₂))) := by
  intro x hx
  let b := (Module.Free.chooseBasis A B₂).localizationLocalization K A⁰ L₂
  have h₂' : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
    simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂
  let b' : Basis _ L₁ M := h₁.basisOfBasisLeft h₂' b.traceDual
  rw [← b'.sum_repr x]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rsuffices ⟨c, hc⟩ : b'.repr x i ∈ (algebraMap B₁ L₁).range := by
    have : (h₁.basisOfBasisLeft h₂' b).traceDual = b' := by
      refine (DFunLike.ext'_iff.trans Basis.traceDual_eq_iff).mpr fun _ _ ↦ ?_
      rw [h₁.basisOfBasisLeft_apply, h₁.basisOfBasisLeft_apply, traceForm_apply, ← map_mul,
        h₁.trace_algebraMap_eq h₂, b.trace_traceDual_mul, MonoidWithZeroHom.map_ite_one_zero]
    rw [← this, (h₁.basisOfBasisLeft h₂' b).traceDual_repr_apply x i]
    refine mem_traceDual.mp hx _ ?_
    rw [mem_one, h₁.basisOfBasisLeft_apply, Basis.localizationLocalization_apply,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B₂ C M]
    exact ⟨_, rfl⟩
  rw [← hc, ← algebra_compatible_smul L₁, algebra_compatible_smul C]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine ⟨b.traceDual i, ?_, by rw [h₁.basisOfBasisLeft_apply]⟩
  rw [SetLike.mem_coe, ← restrictScalars_mem A, traceDual_span_of_basis A _ b
    (by rw [Basis.localizationLocalization_span K A⁰ L₂]; ext; simp)]
  exact Submodule.subset_span <| Set.mem_range_self i

variable [IsDomain A] [IsDomain B₁]
  [IsIntegrallyClosed A] [IsIntegrallyClosed B₁] [IsDedekindDomain B₂] [IsDedekindDomain C]
  [IsFractionRing B₁ L₁] [IsFractionRing B₂ L₂] [IsFractionRing C M]
  [IsIntegralClosure B₂ A L₂] [IsIntegralClosure C B₂ M] [IsIntegralClosure C B₁ M]
  [NoZeroSMulDivisors B₁ C] [NoZeroSMulDivisors B₂ C]

variable (A B₁ B₂ C) in
theorem differentIdeal_dvd_differentIdeal_map [Module.Free A B₂] [Module.Finite A B₂]
    (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤) :
    differentIdeal B₁ C ∣ (differentIdeal A B₂).map (algebraMap B₂ C) := by
  have := IsIntegralClosure.isLocalization A K L₂ B₂
  have := IsIntegralClosure.isLocalization B₂ L₂ M C
  rw [Ideal.dvd_iff_le, ← coeIdeal_le_coeIdeal' C⁰ (P := M) le_rfl, coeIdeal_differentIdeal B₁ L₁,
    le_inv_comm _ (by simp), ← extended_coeIdeal_eq_map_algebraMap (K := L₂) M, ← extended_inv,
    coeIdeal_differentIdeal A K, inv_inv, ← coe_le_coe, coe_dual_one, coe_extended_eq_span,
    ← coeToSet_coeToSubmodule, coe_dual_one]
  · convert traceDual_le_span_traceDual A C B₁ B₂ h₁ h₂
    exact (IsLocalization.algebraMap_eq_map_map_submonoid B₂⁰ C L₂ M).symm
  · exact coeIdeal_ne_zero.mpr <| differentIdeal_ne_bot' A K B₂ L₂
  · exact coeIdeal_ne_zero.mpr <| Ideal.map_ne_bot_of_ne_bot <| differentIdeal_ne_bot' A K B₂ L₂

variable [Algebra A B₁] [IsDedekindDomain B₁] [NoZeroSMulDivisors A B₁]
  [Algebra A L₁] [Algebra A C] [Algebra A M] [IsScalarTower A B₁ L₁] [IsScalarTower A K L₁]
  [IsScalarTower A C M] [IsScalarTower A K M] [IsIntegralClosure B₁ A L₁] [IsIntegralClosure C A M]
  [NoZeroSMulDivisors A C]

theorem differentIdeal_map_eq_differentIdeal [Module.Free A B₁] [Module.Finite A B₁]
    [Module.Free A B₂] [Module.Finite A B₂] (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
      ((differentIdeal A B₂).map (algebraMap B₂ C))) :
    (differentIdeal A B₁).map (algebraMap B₁ C) = differentIdeal B₂ C := by
  have := IsIntegralClosure.isLocalization B₁ L₁ M C
  have := IsIntegralClosure.isLocalization B₂ L₂ M C
  have main := (differentIdeal_eq_differentIdeal_mul_differentIdeal
    A K B₁ L₁ C M).symm.trans (differentIdeal_eq_differentIdeal_mul_differentIdeal A K B₂ L₂ C M)
  apply dvd_antisymm'
  · have h' : IsCoprime (differentIdeal B₂ C) (differentIdeal B₁ C) := by
      refine (h₃.of_isCoprime_of_dvd_right ?_).of_isCoprime_of_dvd_left ?_
      · exact differentIdeal_dvd_differentIdeal_map A C B₁ B₂ h₁ h₂
      · exact differentIdeal_dvd_differentIdeal_map A C B₂ B₁ h₁.symm (by rwa [sup_comm])
    exact h'.dvd_of_dvd_mul_left (dvd_of_mul_right_eq _ main.symm)
  · exact h₃.dvd_of_dvd_mul_right (dvd_of_mul_left_eq _ main)

example [Module.Free A B₁] [Module.Finite A B₁]
    [Module.Free A B₂] [Module.Finite A B₂] (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal A B₁).map (algebraMap B₁ C))
      ((differentIdeal A B₂).map (algebraMap B₂ C)))
    {ι : Type*} (b : Basis ι A B₂) :
    span B₁ (Set.range (algebraMap B₂ M ∘ b)) =
      LinearMap.range (IsScalarTower.toAlgHom B₁ C M) := by
  haveI h₂' : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
      simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂

--  have : algebraMap L₂ M ∘ b = h₁.basisOfBasisLeft h₂' b := by ext; simp
--  rw [this]
  have : IsLocalization (algebraMapSubmonoid C B₁⁰) M := sorry
  let b₀ : Basis ι B₁ C := sorry
  have := Basis.localizationLocalization_span (R := B₁) L₁ B₁⁰ (A := C) M b₀
  sorry

end IntermediateField.LinearDisjoint

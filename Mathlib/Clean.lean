import Mathlib

open nonZeroDivisors NumberField

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

-- example {K M : Type*} [Field K] [Field M] [Algebra K M] [FiniteDimensional K M]
--     [Algebra.IsSeparable K M] {L₁ L₂ : IntermediateField K M}
--     (h₁ : L₁.toSubalgebra.LinearDisjoint L₂.toSubalgebra)
--     (h₂ : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤) {ι : Type*} [Finite ι] [DecidableEq ι]
--     (b : Basis ι K L₂) :
--     (b.traceDual.ofLinearDisjointLeft h₁ h₂).traceDual =
--       (b.ofLinearDisjointLeft h₁ h₂ : Basis ι L₁ M) := sorry






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

section general_compositum

-- variable (A K B L C M : Type*) [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A K]
--   [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
--   [IsScalarTower A B L] [IsDomain A] [IsFractionRing A K] [Algebra.IsSeparable K L]
--   [IsIntegralClosure B A L] [IsIntegrallyClosed A] [IsDedekindDomain B] [NoZeroSMulDivisors A B]
--   [IsFractionRing B L] [CommRing C] [Field M] [Algebra C M] [IsFractionRing C M] [Algebra B C]
--   [Algebra A C] [Algebra K M] [Algebra L M] [Algebra B M] [Algebra A M] [IsScalarTower K L M]
--   [IsScalarTower A K M] [IsScalarTower A C M] [IsScalarTower B C M] [IsScalarTower B L M]
--   [IsDedekindDomain C] [NoZeroSMulDivisors A C] [Algebra.IsSeparable K M] [FiniteDimensional K M]
--   [IsIntegralClosure C B M] [IsIntegralClosure C A M] [NoZeroSMulDivisors B C]
--   [IsLocalization (algebraMapSubmonoid C B⁰) M]

variable {A K C M : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CommRing C]
  [Field M] [Algebra C M] [IsFractionRing C M] [Algebra K M]
  (L₁ L₂ : IntermediateField K M) {B₁ B₂ : Type*} [CommRing B₁] [CommRing B₂] [Algebra B₁ L₁]
  [Algebra B₂ L₂] [IsFractionRing B₁ L₁] [IsFractionRing B₂ L₂]
  [Algebra A B₁] [Algebra A B₂] [Algebra B₁ C] [Algebra B₁ M] [Algebra B₂ C]
  [Algebra A L₂] [Algebra B₂ M]
  [IsDomain A] [IsDedekindDomain B₂] [IsDomain B₁] [IsDedekindDomain C]
  [NoZeroSMulDivisors A B₂] [NoZeroSMulDivisors B₁ C] [NoZeroSMulDivisors B₂ C]
  [IsIntegrallyClosed A] [IsIntegrallyClosed B₁]
  [IsIntegralClosure B₂ A L₂] [IsIntegralClosure C B₁ M]
  [IsScalarTower A B₂ L₂] [IsScalarTower A K L₂]
  [IsScalarTower B₁ C M] [IsScalarTower B₁ L₁ M]
  [IsScalarTower B₂ L₂ M] [IsScalarTower B₂ C M]
  [IsLocalization (algebraMapSubmonoid C B₂⁰) M]
  [Algebra.IsSeparable K M] [FiniteDimensional K M]
  (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)

open Submodule IntermediateField

set_option maxHeartbeats 1000000 in
example {ι : Type*} (b : Basis ι K L₂)
    (hb : (1 : Submodule B₂ L₂).restrictScalars A = span A (Set.range b)) :
    differentIdeal B₁ C ∣ (differentIdeal A B₂).map (algebraMap B₂ C) := by
  classical

  have : Algebra.IsSeparable L₁ M := isSeparable_tower_top_of_isSeparable K L₁ M
  have : Algebra.IsSeparable K L₂ := isSeparable_tower_bot_of_isSeparable K L₂ M
  have : FiniteDimensional L₁ M := Module.Finite.right K L₁ M
  have : FiniteDimensional K L₁ := Module.Finite.left K L₁ M
  have : FiniteDimensional K L₂ := Module.Finite.left K L₂ M
  suffices ((differentIdeal A B₂).map (algebraMap B₂ C) : FractionalIdeal C⁰ M) ≤
      (differentIdeal B₁ C : FractionalIdeal C⁰ M) by
    rw [← coe_le_coe] at this
    simp only [coe_coeIdeal, IsFractionRing.coeSubmodule_le_coeSubmodule] at this
    rwa [Ideal.dvd_iff_le]
  rw [coeIdeal_differentIdeal B₁ L₁]
  rw [← extended_coeIdeal_eq_map_algebraMap (K := L₂) M]
  rw [coeIdeal_differentIdeal A K]
  rw [extended_inv _ (by simp)]
  rw [le_inv_comm ( inv_ne_zero <| extended_ne_zero _ _ (FaithfulSMul.algebraMap_injective _ _)
    (by simp)) (by simp), inv_inv]
  rw [← coe_le_coe]
  rw [coe_dual _ _ (by simp), coe_extended_eq_span, coe_one]
  have := IsLocalization.algebraMap_eq_map_map_submonoid B₂⁰ C L₂ M
  erw [← this]
  intro x hx
  rw [IntermediateField.linearDisjoint_iff'] at h₁
  have : Fintype ι := by
    apply FiniteDimensional.fintypeBasisIndex b
  let b' := b.traceDual
  replace h₂ : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
    simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂
  let B' : Basis ι L₁ M := b'.ofLinearDisjointLeft h₁ h₂
  let B₀ := B'.traceDual
  rw [← B'.sum_repr x]
  have : ∃ c : ι → B₁, ∀ i, B'.repr x i = algebraMap B₁ L₁ (c i) := by
    have h_cons₁ (i : ι) : trace L₁ M (x * B₀ i) ∈ (algebraMap B₁ L₁).range := by
        rw [mem_traceDual] at hx
        specialize hx (B₀ i) ?_
        · refine mem_one.mpr ?_
          have h_cons₂ :  ∃ y, (algebraMap B₂ ↥L₂) y = b i := by
            rw [← mem_one, ← restrictScalars_mem A, hb]
            exact Submodule.subset_span (Set.mem_range_self i)
          refine ⟨?_, ?_⟩
          · exact algebraMap B₂ C h_cons₂.choose
          · dsimp
            have := h_cons₂.choose_spec
            rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B₂ L₂ M, this]
            erw [← b.ofLinearDisjointLeft_apply h₁ h₂]
            simp [B₀, B']
            refine congr_fun ?_ i
            rw [eq_comm, Basis.traceDual_eq_iff]
            intro i j
            simp [b']
            rw [b.ofLinearDisjointLeft_apply h₁ h₂ i,
              b.traceDual.ofLinearDisjointLeft_apply h₁ h₂ j, ← map_mul]
            have := h₁.trace_algebraMap_eq h₂ (b i * b.traceDual j)
            erw [this]
            simp
            rw [mul_comm, Basis.apply_traceDual]
            simp [eq_comm]
        · rwa [traceForm_apply] at hx
    refine ⟨?_, ?_⟩
    · intro i
      exact (h_cons₁ i).choose
    · intro i
      have := (h_cons₁ i).choose_spec
      rw [this]
      nth_rewrite 2 [← B'.sum_repr x]
      rw [Finset.sum_mul, map_sum]
      simp_rw [smul_mul_assoc, map_smul, mul_comm (B' _)]
      simp_rw [B₀, B'.apply_traceDual]
      simp
  obtain ⟨c, hc⟩ := this
  simp_rw [hc, Algebra.smul_def]
  have {x} : algebraMap L₁ M (algebraMap B₁ L₁ x) =
      algebraMap C M (algebraMap B₁ C x) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  simp_rw [this]
  simp_rw [← Algebra.smul_def]
  apply Submodule.sum_smul_mem
  intro i _
  apply Submodule.subset_span
  refine ⟨b' i, ?_, ?_⟩
  · rw [SetLike.mem_coe, ← mem_coe, coe_dual_one]
    have := Submodule.traceDual_span_of_basis A (K := K) (B := B₂) (1 : Submodule B₂ L₂) b hb
    change b' i ∈ (traceDual A K 1).restrictScalars A
    rw [this]
    apply subset_span
    exact Set.mem_range_self i
  · simp [B']
    have := b'.ofLinearDisjointLeft_apply h₁ h₂ i
    change algebraMap L₂ M (b' i) = _
    exact this.symm

example [Module.Free A B₂] [Module.Finite A B₂] [IsLocalization (algebraMapSubmonoid B₂ A⁰) L₂] :
    traceDual B₁ L₁ (1 : Submodule C M) ≤
      span C (algebraMap L₂ M '' (dual A K (1 : FractionalIdeal B₂⁰ L₂))) := by
  intro x hx
  rw [IntermediateField.linearDisjoint_iff'] at h₁
  let b := (Module.Free.chooseBasis A B₂).localizationLocalization K A⁰ L₂
  replace h₂ : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
    simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂
  let b' : Basis _ L₁ M := b.traceDual.ofLinearDisjointLeft h₁ h₂
  rw [← b'.sum_repr x]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rsuffices ⟨c, hc⟩ : b'.repr x i ∈ (algebraMap B₁ L₁).range := by
    have : (b.ofLinearDisjointLeft h₁ h₂).traceDual = b' := by
      rw [DFunLike.ext'_iff, Basis.traceDual_eq_iff]
      intro i j
      rw [b.ofLinearDisjointLeft_apply, b.traceDual.ofLinearDisjointLeft_apply, traceForm_apply,
        ← map_mul]
      change trace L₁.toSubalgebra M _ = _
      erw [h₁.trace_algebraMap_eq h₂, b.trace_traceDual_mul]
      simp
    rw [← this]
    rw [Basis.traceDual_repr_apply (K := L₁) (b.ofLinearDisjointLeft h₁ h₂) x i]
    refine mem_traceDual.mp hx (b.ofLinearDisjointLeft h₁ h₂ i) ?_
    sorry
  rw [← hc, ← algebra_compatible_smul L₁, algebra_compatible_smul C]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine ⟨b.traceDual i, ?_, by rw [Basis.ofLinearDisjointLeft_apply]; rfl⟩
  rw [SetLike.mem_coe, ← mem_coe, coe_dual_one, ← restrictScalars_mem A, traceDual_span_of_basis
    A _ b (by rw [Basis.localizationLocalization_span K A⁰ L₂]; ext; simp)]
  exact Submodule.subset_span <| Set.mem_range_self i

set_option maxHeartbeats 1000000 in
example [Module.Free A B₂] [Module.Finite A B₂] [IsLocalization (algebraMapSubmonoid B₂ A⁰) L₂] :
    differentIdeal B₁ C ∣ (differentIdeal A B₂).map (algebraMap B₂ C) := by

  let b₀ := Module.Free.chooseBasis A B₂
  let b := b₀.localizationLocalization K A⁰ L₂
  have : Algebra.IsSeparable L₁ M := isSeparable_tower_top_of_isSeparable K L₁ M
  have : Algebra.IsSeparable K L₂ := isSeparable_tower_bot_of_isSeparable K L₂ M
  have : FiniteDimensional L₁ M := Module.Finite.right K L₁ M
  have : FiniteDimensional K L₁ := Module.Finite.left K L₁ M
  have : FiniteDimensional K L₂ := Module.Finite.left K L₂ M
  suffices ((differentIdeal A B₂).map (algebraMap B₂ C) : FractionalIdeal C⁰ M) ≤
      (differentIdeal B₁ C : FractionalIdeal C⁰ M) by
    rw [← coe_le_coe] at this
    simp only [coe_coeIdeal, IsFractionRing.coeSubmodule_le_coeSubmodule] at this
    rwa [Ideal.dvd_iff_le]
  rw [coeIdeal_differentIdeal B₁ L₁]
  rw [← extended_coeIdeal_eq_map_algebraMap (K := L₂) M]
  rw [coeIdeal_differentIdeal A K]
  rw [extended_inv _ (by simp)]
  rw [le_inv_comm ( inv_ne_zero <| extended_ne_zero _ _ (FaithfulSMul.algebraMap_injective _ _)
    (by simp)) (by simp), inv_inv]
  rw [← coe_le_coe]
  rw [coe_dual _ _ (by simp), coe_extended_eq_span, coe_one]
  have := IsLocalization.algebraMap_eq_map_map_submonoid B₂⁰ C L₂ M
  erw [← this]

  intro x hx
  rw [IntermediateField.linearDisjoint_iff'] at h₁
  let b' := b.traceDual
  replace h₂ : L₁.toSubalgebra ⊔ L₂.toSubalgebra = ⊤ := by
    simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg toSubalgebra h₂
  let B' : Basis _ L₁ M := b'.ofLinearDisjointLeft h₁ h₂
  let B₀ := B'.traceDual
  rw [← B'.sum_repr x]
  have : ∃ c : _ → B₁, ∀ i, B'.repr x i = algebraMap B₁ L₁ (c i) := by
    have h_cons₁ (i) : trace L₁ M (x * B₀ i) ∈ (algebraMap B₁ L₁).range := by
        rw [mem_traceDual] at hx
        specialize hx (B₀ i) ?_
        · refine mem_one.mpr ?_
          have h_cons₂ :  ∃ y, (algebraMap B₂ ↥L₂) y = b i := by
            have := b₀.localizationLocalization_span K A⁰ L₂
            change b i ∈ LinearMap.range (IsScalarTower.toAlgHom A B₂ L₂)
            rw [← this]
            exact Submodule.subset_span (Set.mem_range_self i)
          refine ⟨?_, ?_⟩
          · exact algebraMap B₂ C h_cons₂.choose
          · dsimp
            have := h_cons₂.choose_spec
            rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B₂ L₂ M, this]
            erw [← b.ofLinearDisjointLeft_apply h₁ h₂]
            simp [B₀, B']
            refine congr_fun ?_ i
            rw [eq_comm, Basis.traceDual_eq_iff]
            intro i j
            simp [b']
            rw [b.ofLinearDisjointLeft_apply h₁ h₂ i,
              b.traceDual.ofLinearDisjointLeft_apply h₁ h₂ j, ← map_mul]
            have := h₁.trace_algebraMap_eq h₂ (b i * b.traceDual j)
            erw [this]
            simp
            rw [mul_comm, Basis.apply_traceDual]
            simp [eq_comm]
        · rwa [traceForm_apply] at hx
    refine ⟨?_, ?_⟩
    · intro i
      exact (h_cons₁ i).choose
    · intro i
      have := (h_cons₁ i).choose_spec
      rw [this]
      nth_rewrite 2 [← B'.sum_repr x]
      rw [Finset.sum_mul, map_sum]
      simp_rw [smul_mul_assoc, map_smul, mul_comm (B' _)]
      simp_rw [B₀, B'.apply_traceDual]
      simp
  obtain ⟨c, hc⟩ := this
  simp_rw [hc, Algebra.smul_def]
  have {x} : algebraMap L₁ M (algebraMap B₁ L₁ x) =
      algebraMap C M (algebraMap B₁ C x) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  simp_rw [this]
  simp_rw [← Algebra.smul_def]
  apply Submodule.sum_smul_mem
  intro i _
  apply Submodule.subset_span
  refine ⟨b' i, ?_, ?_⟩
  · rw [SetLike.mem_coe, ← mem_coe, coe_dual_one]
    have := b₀.localizationLocalization_span K A⁰ L₂
    have := Submodule.traceDual_span_of_basis A (K := K) (B := B₂) (1 : Submodule B₂ L₂) b
      (by rw [this]; ext; simp)
    change b' i ∈ (traceDual A K 1).restrictScalars A
    rw [this]
    apply subset_span
    exact Set.mem_range_self i
  · simp [B']
    have := b'.ofLinearDisjointLeft_apply h₁ h₂ i
    change algebraMap L₂ M (b' i) = _
    exact this.symm


#exit




end general_compositum

section numberfield

variable (M : Type*) [Field M] [NumberField M] (L₁ L₂ : IntermediateField ℚ M)
  (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)

example :
    (differentIdeal ℤ (𝓞 L₂)).map (algebraMap (𝓞 L₂) (𝓞 M)) ≤
      differentIdeal (𝓞 L₁) (𝓞 M) := by
  rw [← coeIdeal_le_coeIdeal M, coeIdeal_differentIdeal _ L₁,
    ← extended_coeIdeal_eq_map_algebraMap (K := L₂) M, coeIdeal_differentIdeal _ ℚ,
    extended_inv _ (by simp), le_inv_comm sorry sorry, inv_inv, ← coe_le_coe, coe_dual,
    coe_extended_eq_span, coe_one]
  have :=  IsLocalization.algebraMap_eq_map_map_submonoid (𝓞 L₂)⁰ (𝓞 M) L₂ M
  erw [← this]
  rw [show ↑(dual ℤ ℚ (1 :FractionalIdeal (𝓞 L₂)⁰ L₂)) =
    ((Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 L₂) L₂)).restrictScalars ℤ : Set L₂)
    by sorry]
  let b := integralBasis L₂
  have := Submodule.traceDual_span_of_basis ℤ (1 : Submodule (𝓞 L₂) L₂) b sorry
  rw [this]
  intro x hx




end numberfield

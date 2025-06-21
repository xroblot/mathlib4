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

theorem Basis.apply_traceDual {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L) (i j : ι) :
    Algebra.trace K L ((b.traceDual i) * (b j)) = if j = i then 1 else 0 :=
  (Algebra.traceForm K L).apply_dualBasis_left _ _ i j

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
    (b : Basis ι K L) (v : ι → L) :
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
  (h₁ : L₁.LinearDisjoint L₂) (h₂ : L₁ ⊔ L₂ = ⊤)

open Submodule

example {ι : Type*} (b : Basis ι K L₂) (hb : span A (Set.range b) = Set.range (algebraMap B₂ L₂)) :
    (differentIdeal A B₂).map (algebraMap B₂ C) ≤ differentIdeal B₁ C := by
  have : Algebra.IsSeparable L₁ M := sorry
  have : Algebra.IsSeparable K L₂ := sorry
  have : FiniteDimensional L₁ M := sorry
  have : FiniteDimensional K L₁ := sorry
  have : FiniteDimensional K L₂ := sorry
  suffices ((differentIdeal A B₂).map (algebraMap B₂ C) : FractionalIdeal C⁰ M) ≤
      (differentIdeal B₁ C : FractionalIdeal C⁰ M) by
    sorry
  rw [coeIdeal_differentIdeal B₁ L₁]
  rw [← extended_coeIdeal_eq_map_algebraMap (K := L₂) M]
  rw [coeIdeal_differentIdeal A K]
  rw [extended_inv _ (by simp)]
  rw [le_inv_comm sorry sorry, inv_inv]
  rw [← coe_le_coe]
  rw [coe_dual _ _ (by simp), coe_extended_eq_span, coe_one]
  have := IsLocalization.algebraMap_eq_map_map_submonoid B₂⁰ C L₂ M
  erw [← this]
  intro x hx
  refine (mem_span_image_iff_exists_fun C).mpr ?_
  


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

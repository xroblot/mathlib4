import Mathlib

-- theorem FractionalIdeal.extended_inv {A : Type*} [CommRing A] [IsDedekindDomain A]
--     {B : Type*} [CommRing B]
--     {f : A →+* B} {K : Type*} {M : Submonoid A} [CommRing K] [Algebra A K] [IsLocalization M K]
--     (L : Type*) {N : Submonoid B} [CommRing L] [Algebra B L] [IsLocalization N L]
--     (hf : M ≤ Submonoid.comap f N) (I : FractionalIdeal M K) :
--     extended L hf I⁻¹ = (extended L hf I)⁻¹ := sorry

open nonZeroDivisors

variable {A B C K L M : Type*}
variable [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
variable [CommRing B] [Field L] [Algebra B L] [IsFractionRing B L]

variable [IsDomain B] [IsIntegrallyClosed B] [IsNoetherianRing B]

variable [CommRing C] [Field M] [Algebra C M] [IsFractionRing C M]

variable [IsDomain C] [IsIntegrallyClosed C]

variable [Algebra L M]
variable [Algebra K L] [Algebra K M]
variable [Algebra B M] [Algebra B C]
variable [Algebra A B] [Algebra A C] [Algebra A L] [Algebra A M]
variable [IsScalarTower K L M]
variable [IsScalarTower A K L] [IsScalarTower A K M] [IsScalarTower A B L] [IsScalarTower A C M]
variable [IsScalarTower B L M] [IsScalarTower B C M]

variable [Algebra.IsIntegral B C]

-- variable [IsIntegralClosure C B M]
variable [NoZeroSMulDivisors B C]
variable [FiniteDimensional K M]

-- variable [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
-- variable [Algebra B C] [Algebra B E] [IsScalarTower B C E] [IsScalarTower B F E]
-- variable [Algebra A B] [Algebra A C] [IsScalarTower A B C]
-- variable [Algebra A F] [IsScalarTower A B F] [IsScalarTower A K F]
-- variable [Algebra A E] [IsScalarTower A C E] [IsScalarTower A K E]
-- variable [FiniteDimensional K E] [Algebra.IsSeparable K E]
-- variable [IsIntegralClosure B A F] [IsIntegralClosure C A E] [IsIntegralClosure C B E]
-- variable [NoZeroSMulDivisors B C]

example [Algebra.IsSeparable L M] {I : Submodule B L} :
    Submodule.span C (algebraMap L M '' Submodule.traceDual A K I) ≤
      Submodule.traceDual A K (Submodule.span C (algebraMap L M '' I)) := by
  have : Module.Finite K L := Module.Finite.left K L M
  have : Module.Finite L M := Module.Finite.right K L M
  have : IsIntegralClosure C B M := IsIntegralClosure.of_isIntegrallyClosed _ _ _
  have : Module.Finite B C := IsIntegralClosure.finite B L M C
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_traceDual] at hx ⊢
  intro y hy
  rw [Submodule.mem_span_image_iff_exists_fun] at hy
  obtain ⟨s, hs, c, rfl⟩ := hy
  rw [Algebra.traceForm_apply, ← Algebra.trace_trace (S := L), ← Algebra.smul_def, map_smul,
    smul_eq_mul]
  apply hx
  rw [map_sum]
  refine Submodule.sum_mem I fun i _ ↦ ?_
  rw [Algebra.smul_def, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul,
    ← Algebra.algebraMap_intTrace (A := B) (c i), mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (hs i.prop)

variable [IsDomain A] [IsIntegrallyClosed A] [IsIntegralClosure C A M] [Algebra.IsSeparable K M]
  [IsIntegralClosure B A L] [IsDedekindDomain B] [IsDedekindDomain C]

variable (B C) in
theorem zozo : B⁰ = Submonoid.comap (algebraMap B C) C⁰ := by
    ext x
    simp only [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Submonoid.mem_comap,
      FaithfulSMul.algebraMap_eq_zero_iff]

variable [FiniteDimensional K L] [Algebra.IsSeparable K L] -- Infer those

example {I : FractionalIdeal B⁰ L} (x : M)
    (h : IsLocalization (Algebra.algebraMapSubmonoid C B⁰) M) :
    FractionalIdeal.dual A K (I.extended M (zozo B C).le) =
      FractionalIdeal.extended M (zozo B C).le (FractionalIdeal.dual A K I) := by
  rw [FractionalIdeal.dual_eq_mul_inv _ _ I, FractionalIdeal.extended_mul]
  have : FractionalIdeal.extended M (zozo B C).le I⁻¹ =
    (FractionalIdeal.extended M (zozo B C).le I)⁻¹ := by sorry
  rw [this, eq_comm]
  rw [mul_inv_eq_iff_eq_mul₀]
  rw [FractionalIdeal.dual_mul_self]

#exit
  intro x hx
  simp only [FractionalIdeal.val_eq_coe, FractionalIdeal.mem_coe,
    FractionalIdeal.coe_extended_eq_span] at hx ⊢


  have : Module.Finite K L := Module.Finite.left K L M
  have : Module.Finite L M := Module.Finite.right K L M
  have : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L M
  have hI₁ : I ≠ 0 := sorry
  have hI₂ : (FractionalIdeal.extended M (zozo B C).le I) ≠ 0 := sorry
  have hI₃ : FractionalIdeal.dual A K I ≠ 0 := sorry
  have h₁ : ∀ c : C, Algebra.trace L M (c • x) ∈ FractionalIdeal.dual A K I := by
    intro c
    simp_rw [FractionalIdeal.mem_dual hI₁, FractionalIdeal.mem_dual hI₂,
      Algebra.traceForm_apply] at hx ⊢
    intro i hi
    have := hx (c • algebraMap L M i) ?_
    · rwa [Algebra.smul_def, ← mul_rotate', ← Algebra.smul_def, ← Algebra.trace_trace (S := L),
        map_smul, smul_eq_mul, mul_comm, mul_comm x, ← Algebra.smul_def] at this
    apply Submodule.smul_mem
    apply Submodule.subset_span
    have := IsLocalization.algebraMap_apply_eq_map_map_submonoid (R := B) (M := B⁰) (S := C)
      (Rₘ := L) (Sₘ := M)
    rw [this]
    exact Set.mem_image_of_mem _ hi
  have h₂ : ∀ c : C, (FractionalIdeal.spanSingleton B⁰ (Algebra.trace L M (c • x))) *
      (FractionalIdeal.dual A K I)⁻¹ ≤ 1 := by
    intro c
    rw [← FractionalIdeal.le_div_iff_mul_le, FractionalIdeal.div_eq_mul_inv, inv_inv, one_mul]
    exact FractionalIdeal.spanSingleton_le_iff_mem.mpr (h₁ c)
    exact inv_ne_zero hI₃
  have h₃ : ∀ i ∈ (FractionalIdeal.dual A K I)⁻¹, ∀ c : C,
      Algebra.trace L M (i • c • x) ∈ (algebraMap B L).range := sorry
  have h₄ :  ∀ i ∈ (FractionalIdeal.dual A K I)⁻¹, i • x ∈
      FractionalIdeal.dual A K (1 : FractionalIdeal C⁰ M) := sorry


--   rw [@FractionalIdeal.spanSingleton_mul_le_iff]


#exit

example {I : FractionalIdeal B⁰ F} (h : B⁰ ≤ Submonoid.comap (algebraMap B C) C⁰) :
    have : FiniteDimensional K F := sorry
    have : Algebra.IsSeparable K F := sorry
    FractionalIdeal.extended E h (FractionalIdeal.dual A K I) =
      FractionalIdeal.dual A K (I.extended E h) := by
  by_cases hI : I = 0
  · simp [hI]
  have hI' :  FractionalIdeal.extended E h I ≠ 0 := sorry
  apply FractionalIdeal.coeToSubmodule_injective
  simp only [FractionalIdeal.coe_extended_eq_span, FractionalIdeal.coe_dual _ _ hI']
  rw [toto, toto]











  have {a} : (IsLocalization.map E (algebraMap B C) h) a = algebraMap F E a := by
    have : IsLocalization (Algebra.algebraMapSubmonoid C B⁰) E := by
      have :  B⁰ = Submonoid.comap (algebraMap B C) C⁰ := sorry
      rw [Algebra.algebraMapSubmonoid, this]
      apply IsLocalization.isLocalization_of_submonoid_le

      have := Algebra.algebraMapSubmonoid_le_comap B⁰ (IsScalarTower.toAlgHom B C E)
      rw [this]
      rw [← @Submonoid.comap_map_comap]
      rw?
    rw [IsLocalization.algebraMap_apply_eq_map_map_submonoid (R := B) (S := C) (M := B⁰)]
    sorry
#exit

    (x : E) : 1 = 0 := by
  have : C⁰ = Algebra.algebraMapSubmonoid C B⁰ := sorry
  have : IsLocalization (Algebra.algebraMapSubmonoid C B⁰) E := sorry
  have : IsLocalization (Algebra.algebraMapSubmonoid C A⁰) E := sorry
  let _ : Algebra F E := localizationAlgebra B⁰ C
  let _ : Algebra K E := localizationAlgebra A⁰ C
  have : IsScalarTower K F E := sorry
  have : Module.Finite K E := sorry

  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite K F E
  have : Algebra.IsSeparable F E := Algebra.isSeparable_tower_top_of_isSeparable K F E
  have h : B⁰ ≤ Submonoid.comap (algebraMap B C) C⁰ := by
    refine nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (algebraMap B C) ?_
    refine NoZeroSMulDivisors.iff_algebraMap_injective.mp ?_
    infer_instance
  let J₀ := FractionalIdeal.extended E h (FractionalIdeal.dual A K I)
  let J₁ := FractionalIdeal.dual A K (I.extended E h)
  have : J₀ = J₁ := by
    unfold J₀ J₁
    by_cases hI : I = 0
    · simp [hI]
    ext x
    have : FractionalIdeal.extended E h I ≠ 0 := sorry
    simp_rw [FractionalIdeal.mem_dual this, FractionalIdeal.mem_extended_iff]
    constructor
    intro hx a ha
    induction hx, ha using Submodule.span_induction₂ with
    | mem_mem x y hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        rw [SetLike.mem_coe, FractionalIdeal.mem_dual hI] at ha
        specialize ha b hb
        rw [Algebra.traceForm_apply]
        have : (IsLocalization.map E (algebraMap B C) h) a = algebraMap F E a := by
          have : IsLocalization (Algebra.algebraMapSubmonoid C B⁰) E := by
            sorry
          have : C⁰ = Algebra.algebraMapSubmonoid C B⁰ := sorry
          have := localizationAlgebraMap_def (R := B) (S := C) (Sₘ := E) (Rₘ := F) (M := B⁰)
          have := (RingHom.congr_fun this a).symm
          convert this

          sorry
        rw [this]
        have : (IsLocalization.map E (algebraMap B C) h) b = algebraMap F E b := sorry
        rw [this]
        rw [← map_mul, ← Algebra.trace_trace (S := F), Algebra.trace_algebraMap]
        simp at ha
        obtain ⟨r, hr⟩ := ha
        refine ⟨Module.finrank F E • r, ?_⟩
        rw [map_nsmul, map_nsmul, hr]
    | zero_left y hy => sorry
    | zero_right x hx => sorry
    | add_left x y z hx hy hz _ _ => sorry
    | add_right x y z hx hy hz _ _ => sorry
    | smul_left r x y hx hy _ => sorry
    | smul_right r x y hx hy _ => sorry


#exit

  have : x ∈ FractionalIdeal.extended E h (FractionalIdeal.dual A K I) → x = 1 := by
    rw [FractionalIdeal.mem_extended_iff]
    intro hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, FractionalIdeal.mem_dual] at hx



      sorry

  sorry

#exit

variable {A K B E C F : Type*}
  [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [IsIntegrallyClosed A]
  [CommRing B] [Field E] [Algebra B E] [IsFractionRing B E]
  [CommRing C] [Field F] [Algebra C F] [IsFractionRing C F]
  [Algebra K E] [Algebra K F] [Algebra F E] [IsScalarTower K F E] [FiniteDimensional K E]
  [Algebra.IsSeparable K E]
  [Algebra A F] [IsScalarTower A K F] [IsIntegralClosure C A F]
  [Algebra A E] [IsScalarTower A K E] [IsIntegralClosure B A E]
  [Algebra A B] [IsScalarTower A B E]
  [Algebra C B] [Algebra C E] [IsScalarTower C F E] [IsScalarTower C B E]
  [Algebra A C] [IsScalarTower A K F] [IsScalarTower A C F]
  [IsDedekindDomain A]
  [IsIntegrallyClosed C]
  [FiniteDimensional F E]
  [IsIntegralClosure B C E]
  [Algebra.IsSeparable F E]
  [IsDedekindDomain B]
  [IsDedekindDomain C]
  [FiniteDimensional K F]
  [Algebra.IsSeparable K F]
  [NoZeroSMulDivisors C B]

open nonZeroDivisors

set_option maxHeartbeats 1000000 in
example : 1 = 0 := by
  let BEK := FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ E)
--  let BEK := Submodule.traceDual A K (1 : Submodule B E)
  let BEF := FractionalIdeal.dual C F (1 : FractionalIdeal B⁰ E)
--  let BEF := Submodule.traceDual C F (1 : Submodule B E)
  let CFK₀ := FractionalIdeal.dual A K (1 : FractionalIdeal C⁰ F)
  have h₀ : C⁰ ≤ Submonoid.comap (algebraMap C B) B⁰ := by
    refine nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (algebraMap C B) ?_
    refine NoZeroSMulDivisors.iff_algebraMap_injective.mp ?_
    infer_instance
  let CFK : FractionalIdeal B⁰ E := FractionalIdeal.extended E h₀ CFK₀
  have : BEK = BEF * CFK := by
    unfold BEK BEF CFK CFK₀
    apply le_antisymm
    · intro b hb
      dsimp at hb ⊢
      rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_dual] at hb
      rw [FractionalIdeal.mem_coe]
      rw [← FractionalIdeal.dual_inv, FractionalIdeal.mem_dual]



      sorry
    refine (FractionalIdeal.le_dual_iff A K ?_).mp ?_
    · sorry
    · intro z hz
      dsimp at hz ⊢
      rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_dual] at hz ⊢
      · intro x hx
        rw [FractionalIdeal.mem_extended_iff] at hx
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
        · sorry

        · simp
        · rintro _ _ _ _ ⟨x, hx⟩ ⟨y, hy⟩
          rw [map_add, ← hx, ← hy, ← map_add]
          exact ⟨x + y, rfl⟩
        · rintro b n hn ⟨y, hy⟩
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hn
          · rintro _ ⟨t, ht, rfl⟩
            have : (IsLocalization.map E (algebraMap C B) h₀) t = algebraMap F E t := sorry
            rw [this]
            simp
            rw [Algebra.smul_def, ← Algebra.trace_trace (S := F)]
            have : (algebraMap B E) b * (z * (algebraMap F E) t) =
              t • ((algebraMap B E b) * z) := sorry
            rw [this, map_smul, mul_comm]
            simp at hz
            specialize hz (algebraMap B E b) sorry
            obtain ⟨l, hl⟩ := hz
            rw [← hl]
            simp at hy


            sorry
          · sorry
          · sorry
          · sorry
      · sorry
      · exact one_ne_zero

#exit
    ext x


--    rw [FractionalIdeal.mul_def]
    simp [FractionalIdeal.mem_dual]
    constructor
    · intro h
      rw [← FractionalIdeal.mem_coe]
      simp

      sorry
    · intro hx
      rw [← FractionalIdeal.mem_coe] at hx
      simp at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro m hm n hn
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hn
        · rintro _ ⟨x, hx, rfl⟩ a ha
          rw [FractionalIdeal.mem_one_iff] at ha
          obtain ⟨y, rfl⟩ := ha
          rw [Submodule.mem_traceDual] at hm
          simp at hm
          obtain ⟨z, hz⟩ := hm y
          rw [SetLike.mem_coe, FractionalIdeal.mem_dual] at hx
          simp at hx
          specialize hx (algebraMap C F z) sorry
          obtain ⟨t, ht⟩ := hx
          refine ⟨t, ?_⟩
          rw [← Algebra.trace_trace (S := F)]
          have : m * (IsLocalization.map E (algebraMap C B) this) x * (algebraMap B E y) =
              x • ((algebraMap B E y) * m) := by
            have : IsLocalization (Algebra.algebraMapSubmonoid B C⁰) E := by
              exact IsIntegralClosure.isLocalization_of_isSeparable C F E B
            have := localizationAlgebraMap_def (R := C) (S := B) (Sₘ := E) (Rₘ := F) (M := C⁰)

            erw [← localizationAlgebraMap_def]
            rw [Algebra.smul_def]
            rw [mul_comm _ m, ← mul_assoc, mul_comm _ m]
            congr
            sorry
          rw [this, map_smul, mul_comm, ← hz, smul_eq_mul, ht]
          exact Ne.symm (zero_ne_one' (FractionalIdeal C⁰ F))
        · intro _ _
          refine ⟨0, by simp⟩
        · intro x y _ _ hx hy a ha
          obtain ⟨x₁, hx₁⟩ := hx a ha
          obtain ⟨y₁, hy₁⟩ := hy a ha
          refine ⟨x₁ + y₁, ?_⟩
          simp [hx₁, hy₁, mul_add, add_mul, map_add]
        · intro b x _ hx a ha
          obtain ⟨x₁, hx₁⟩ := hx a ha
          rw [Algebra.smul_def]

          sorry
      · sorry

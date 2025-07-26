import Mathlib

theorem RingEquiv.symm_apply_eq {R S : Type*} [Mul R] [Mul S] [Add R] [Add S] (e : R ≃+* S)
    {x : S} {y : R} : e.symm x = y ↔ x = e y := Equiv.symm_apply_eq _

theorem RingEquiv.eq_symm_apply {R S : Type*} [Mul R] [Mul S] [Add R] [Add S] (e : R ≃+* S)
    {x : S} {y : R} : y = e.symm x ↔ e y = x := Equiv.eq_symm_apply _

open Ideal

attribute [local instance] Ideal.Quotient.field

-- open UniqueFactorizationMonoid in
-- theorem Ideal.bddAbove_algebraMap_le_pow {R : Type*} [CommRing R] {S : Type*} [CommRing S]
--     [Algebra R S] [NoZeroSMulDivisors R S] [IsDedekindDomain S] {p : Ideal R} (hp : p ≠ ⊥)
--     (P : Ideal S) :
--     BddAbove {n | map (algebraMap R S) p ≤ P ^ n} := by
--   classical
--   have : map (algebraMap R S) p ≠ ⊥ := sorry
--   simp_rw [← Ideal.dvd_iff_le]
--   let v : IsDedekindDomain.HeightOneSpectrum S := sorry
--   have {n} {I} : P ^ n ∣ I → n ≤ Multiset.count v.asIdeal (normalizedFactors I) := by

--     sorry
--   use Multiset.count v.asIdeal (normalizedFactors (map (algebraMap R S) p))
--   intro n hn
--   dsimp at hn
--   exact this hn

-- theorem Ideal.ramificationIdx_map_le {R : Type*} [CommRing R] {S : Type*} [CommRing S]
--     (f : R →+* S) (p : Ideal R) (P : Ideal S) {T : Type*} [CommRing T] (g : S →+* T) :
--     ramificationIdx f p P ≤ ramificationIdx (g.comp f) p (map g P) := by
--   classical
--   unfold ramificationIdx
--   refine csSup_le_csSup' ?_ ?_
--   · sorry
--   · intro n hn
--     dsimp at hn ⊢
--     have := Ideal.map_mono (f := g) hn
--     rwa [map_map, Ideal.map_pow] at this

-- example {R : Type*} [CommRing R] {S : Type*} [CommRing S]
--     [Algebra R S] (p : Ideal R) (P : Ideal S) {T : Type*} [CommRing T] [Algebra R T]
--     {U : Type*} [CommRing U] [Algebra S U] [Algebra T U] [Algebra R U] [IsScalarTower R S U]
--     [IsScalarTower R T U] :
--     ramificationIdx (algebraMap R S) p P ≤ ramificationIdx (algebraMap T U)
--       (map (algebraMap R T) p) (map (algebraMap S U) P) := by
--   refine csSup_le_csSup' ?_ ?_
--   · refine bddAbove_def.mpr ?_
--     dsimp
--     sorry
--   · intro n hn
--     have := Ideal.map_mono (f := algebraMap S U) hn
--     rwa [Ideal.map_pow, map_map, ← IsScalarTower.algebraMap_eq,
--       IsScalarTower.algebraMap_eq R T U, ← map_map] at this






@[simp]
theorem equivQuotMaximalIdealOfIsLocalization_apply_mk {R : Type*} [CommRing R] (p : Ideal R)
    [p.IsMaximal] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    [IsLocalRing Rₚ] (x : R) :
    equivQuotMaximalIdealOfIsLocalization p Rₚ (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ (algebraMap R Rₚ x)) := rfl

@[simp]
theorem equivQuotMaximalIdealOfIsLocalization_symm_apply_mk {R : Type*} [CommRing R] (p : Ideal R)
    [p.IsMaximal] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    [IsLocalRing Rₚ] (x) (s : p.primeCompl) :
    (equivQuotMaximalIdealOfIsLocalization p Rₚ).symm
      (Ideal.Quotient.mk _ (IsLocalization.mk' Rₚ x s)) =
        (Ideal.Quotient.mk p x) * (Ideal.Quotient.mk p s)⁻¹ := by
  have h₁ : Ideal.Quotient.mk p ↑s ≠ 0 := by
    simpa [ne_eq, Quotient.eq_zero_iff_mem] using Ideal.mem_primeCompl_iff.mp s.prop
  have h₂ : equivQuotMaximalIdealOfIsLocalization p Rₚ (Ideal.Quotient.mk p ↑s) ≠ 0 := by
    rwa [RingEquiv.map_ne_zero_iff]
  rw [RingEquiv.symm_apply_eq, ← mul_left_inj' h₂, map_mul, mul_assoc, ← map_mul,
    inv_mul_cancel₀ h₁, map_one, mul_one, equivQuotMaximalIdealOfIsLocalization_apply_mk, ← map_mul,
    IsLocalization.mk'_spec, Quotient.mk_algebraMap, equivQuotMaximalIdealOfIsLocalization_apply_mk,
    Quotient.mk_algebraMap]

theorem Ideal.eq_bot_of_liesOver_bot {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    [Nontrivial A] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B] {p : Ideal A} (hp : p = ⊥)
    (P : Ideal B) [h : P.LiesOver p] :
    P = ⊥ := by
  rw [liesOver_iff, under_def] at h
  rw [h] at hp
  exact Ideal.eq_bot_of_comap_eq_bot hp

theorem Ideal.comap_map_eq_self_of_isMaximal (A : Type*) [CommSemiring A] (B : Type*)
    [Semiring B] [Algebra A B] {p : Ideal A} [hP' : p.IsMaximal]
    (hP : Ideal.map (algebraMap A B) p ≠ ⊤) :
    Ideal.comap (algebraMap A B) (Ideal.map (algebraMap A B) p) = p :=
  (IsCoatom.le_iff_eq hP'.out (comap_ne_top _ hP)).mp <| Ideal.le_comap_map

--   sorry

-- theorem Ideal.map_comap_eq_self_of_isMaximal (A : Type*) [CommSemiring A] (B : Type*)
--     [Semiring B] [Algebra A B] {P : Ideal B} [hP' : P.IsMaximal] :
--     -- (hP : Ideal.map (algebraMap A B) P ≠ ⊤) :
--     Ideal.map (algebraMap A B) (Ideal.comap (algebraMap A B) P) = P := by
--   rw [eq_comm, ← IsCoatom.le_iff_eq]
--   exact map_comap_le


  -- (IsCoatom.le_iff_eq hP'.out (comap_ne_top _ hP)).mp <| Ideal.le_comap_map

theorem Ideal.under_map {A B C D : Type*} [CommSemiring A] [CommSemiring B] [Algebra A B]
    (p : Ideal A) (P : Ideal B) [CommSemiring C] [Semiring D] [Algebra A C] [Algebra C D]
    [Algebra A D] [Algebra B D] [IsScalarTower A C D] [IsScalarTower A B D]
    (h₀ : p = under A P) (h₁ : (map (algebraMap A C) p).IsMaximal)
    (h₂ : map (algebraMap B D) P ≠ ⊤) :
    under C (map (algebraMap B D) P) = map (algebraMap A C) p := by
  rw [← IsCoatom.le_iff_eq (isMaximal_def.mp h₁) (comap_ne_top (algebraMap C D) h₂), h₀]
  apply le_comap_of_map_le
  rw [map_map, ← IsScalarTower.algebraMap_eq, map_le_iff_le_comap,
    IsScalarTower.algebraMap_eq A B D, ← comap_comap]
  exact comap_mono <| le_comap_map

variable {R : Type*} [CommRing R] (p : Ideal R) [hp : p.IsPrime]

local notation3 "Rₚ" => Localization.AtPrime p

variable {S : Type*} [CommRing S] [Algebra R S] (P : Ideal S) [hPp : P.LiesOver p]

local notation3 "Mₛ" => Algebra.algebraMapSubmonoid S p.primeCompl
local notation3 "Sₚ" => Localization Mₛ

attribute [local instance] Ideal.Quotient.field

instance [IsDomain R] [IsDomain S] [FaithfulSMul R S] : NoZeroSMulDivisors S Sₚ := by
  rw [NoZeroSMulDivisors.iff_algebraMap_injective]
  rw [IsLocalization.injective_iff_isRegular Mₛ]
  rintro ⟨x, hx⟩
  rw [isRegular_iff_ne_zero']
  refine ne_of_mem_of_not_mem hx ?_
  simp [Algebra.algebraMapSubmonoid]

-- instance : (map (algebraMap R Rₚ) p).IsMaximal := by
--   rw [Localization.AtPrime.map_eq_maximalIdeal]
--   exact IsLocalRing.maximalIdeal.isMaximal _

theorem Localization.AtPrime.not_isField [NoZeroDivisors R] [NeZero p] :
    ¬ IsField Rₚ := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal,
    map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R Rₚ)]
  exact NeZero.ne _

theorem Ideal.disjoint_primeCompl_of_liesOver :
    Disjoint (Algebra.algebraMapSubmonoid S p.primeCompl : Set S) (P : Set S) := by
  refine Set.disjoint_left.mpr fun x hx ↦ ?_
  rw [liesOver_iff, under_def] at hPp
  simp only [Algebra.algebraMapSubmonoid, Submonoid.coe_map, Set.mem_image, SetLike.mem_coe,
    mem_primeCompl_iff, hPp] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact ha

instance Localization.AtPrime.isPrime_algebraMap_of_liesOver [P.IsPrime] :
    (map (algebraMap S Sₚ) P).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint Mₛ _ _ inferInstance
    (disjoint_primeCompl_of_liesOver p P)

instance [Algebra.IsIntegral R S] : Algebra.IsIntegral Rₚ Sₚ :=
  Algebra.isIntegral_def.mpr <| isIntegral_localization

instance [P.IsPrime] :
    (map (algebraMap S Sₚ) P).LiesOver (IsLocalRing.maximalIdeal Rₚ) := by
  rw [liesOver_iff, eq_comm, ← Localization.AtPrime.map_eq_maximalIdeal]
  apply Ideal.under_map _ _ ((liesOver_iff _ _).mp hPp)
  · rw [Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.maximalIdeal.isMaximal Rₚ
  · exact IsPrime.ne_top inferInstance

set_option synthInstance.maxHeartbeats 50000

theorem quotEquivLocalizationQuotMapOfIsMaximal_aux [hP : P.IsMaximal]
    (x : Sₚ ⧸ map (algebraMap S Sₚ) P) :
    ∃ a, (algebraMap S (Sₚ ⧸ map (algebraMap S Sₚ) P)) a = x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective Mₛ x
  obtain ⟨s', hs⟩ := Ideal.Quotient.mk_surjective (I := P) (Ideal.Quotient.mk P s)⁻¹
  simp only [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ _),
    Quotient.algebraMap_eq, RingHom.comp_apply]
  use x * s'
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  have h₁ : s.1 ∉ P := (Set.disjoint_left.mp <| disjoint_primeCompl_of_liesOver p P) s.prop
  have h₂ : algebraMap S Sₚ s ∉ Ideal.map (algebraMap S Sₚ) P := by
    rwa [← Ideal.mem_comap, comap_map_eq_self_of_isMaximal _ _ IsPrime.ne_top']
  refine ((inferInstanceAs <|
      (Ideal.map (algebraMap S Sₚ) P).IsPrime).mem_or_mem ?_).resolve_left h₂
  rw [mul_sub, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mul_cancel_left,
    ← map_mul, ← map_sub, ← mem_comap, comap_map_eq_self_of_isMaximal _ _ IsPrime.ne_top',
    ← Ideal.Quotient.eq, map_mul, map_mul, hs, mul_comm,
    inv_mul_cancel_right₀ (Quotient.eq_zero_iff_mem.not.mpr h₁)]

/-- Doc. -/
noncomputable def quotEquivLocalizationQuotMapOfIsMaximal [hP : P.IsMaximal] :
    S ⧸ P ≃+* Sₚ ⧸ Ideal.map (algebraMap S Sₚ) P :=
  (Ideal.quotEquivOfEq (by
    rw [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ _), ← RingHom.comap_ker, Quotient.algebraMap_eq,
      mk_ker, comap_map_eq_self_of_isMaximal _ _ IsPrime.ne_top'])).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap S (Sₚ ⧸ _))
      fun x ↦ quotEquivLocalizationQuotMapOfIsMaximal_aux p P x)

@[simp]
theorem quotEquivLocalizationQuotMapOfIsMaximal_apply_mk [hP : P.IsMaximal] (x : S) :
    quotEquivLocalizationQuotMapOfIsMaximal p P (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ (algebraMap S Sₚ x)) := rfl

@[simp]
theorem quotEquivLocalizationQuotMapOfIsMaximal_symm_apply_mk [hP : P.IsMaximal] (x : S) (s : Mₛ) :
    (quotEquivLocalizationQuotMapOfIsMaximal p P).symm
      (Ideal.Quotient.mk _ (IsLocalization.mk' _ x s)) =
        (Ideal.Quotient.mk _ x) * (Ideal.Quotient.mk _ s.val)⁻¹ := by
  have h₁ : Ideal.Quotient.mk P ↑s ≠ 0 :=
    Quotient.eq_zero_iff_mem.not.mpr <|
      (Set.disjoint_left.mp <| disjoint_primeCompl_of_liesOver p P) s.prop
  have h₂ : quotEquivLocalizationQuotMapOfIsMaximal p P (Ideal.Quotient.mk P ↑s) ≠ 0 := by
    rwa [RingEquiv.map_ne_zero_iff]
  rw [RingEquiv.symm_apply_eq, ← mul_left_inj' h₂, map_mul, mul_assoc, ← map_mul,
    inv_mul_cancel₀ h₁, map_one, mul_one, quotEquivLocalizationQuotMapOfIsMaximal_apply_mk,
    ← map_mul, IsLocalization.mk'_spec, Quotient.mk_algebraMap,
    quotEquivLocalizationQuotMapOfIsMaximal_apply_mk, Quotient.mk_algebraMap]

theorem Localization.AtPrime.inertiaDeg_map_eq_inertiaDeg [p.IsMaximal] [P.IsMaximal] :
    (IsLocalRing.maximalIdeal Rₚ).inertiaDeg (map (algebraMap S Sₚ) P) = p.inertiaDeg P := by
  rw [inertiaDeg_algebraMap, inertiaDeg_algebraMap]
  refine Algebra.finrank_eq_of_equiv_equiv ?_ ?_ ?_
  · exact (equivQuotMaximalIdealOfIsLocalization p Rₚ).symm
  · exact (quotEquivLocalizationQuotMapOfIsMaximal p P).symm
  · ext x
    refine Localization.induction_on x fun ⟨r, s⟩ ↦ ?_
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      Quotient.algebraMap_mk_of_liesOver, Quotient.mk_algebraMap]
    rw [← Quotient.mk_algebraMap, Localization.mk_eq_mk', IsLocalization.algebraMap_mk' S]
    simp only [equivQuotMaximalIdealOfIsLocalization_symm_apply_mk, map_mul,
      Quotient.algebraMap_mk_of_liesOver, Quotient.mk_algebraMap, map_inv₀,
      quotEquivLocalizationQuotMapOfIsMaximal_symm_apply_mk]

theorem aux {R S : Type*} [CommRing R] [CommRing S] [IsPrincipalIdealRing S] [IsDomain S]
    (I : Ideal R) (f : R →+* S) (h₁ : map f I ≠ ⊥) (h₂ : map f I ≠ ⊤) :
    ramificationIdx f I (map f I) = 1 := by
  apply ramificationIdx_spec
  · simp
  · have : Submodule.IsPrincipal (map f I) := IsPrincipalIdealRing.principal (map f I)
    obtain ⟨x, hx⟩ := this
    rw [hx]
    by_contra!
    simp [span_singleton_pow] at this
    rw [span_singleton_le_span_singleton] at this
    nth_rewrite 2 [← pow_one x] at this
    rw [pow_dvd_pow_iff] at this
    · linarith
    · contrapose! h₁
      rw [hx, h₁, submodule_span_eq, span_singleton_eq_bot]
    · contrapose! h₂
      rwa [hx, submodule_span_eq, span_singleton_eq_top]

theorem Localization.AtPrime.ramificationIdx_map_eq_ramificationIdx
    [Module.Finite R S] [NeZero p] [IsDedekindDomain R] [P.IsPrime] (hP : P ≠ ⊥)
    [IsDedekindDomain S] [FaithfulSMul R S] :
    (IsLocalRing.maximalIdeal Rₚ).ramificationIdx (algebraMap Rₚ Sₚ) (P.map (algebraMap S Sₚ)) =
      p.ramificationIdx (algebraMap R S) P := by
  have hp : p ≠ ⊥ := NeZero.ne _
  have : NoZeroSMulDivisors R Sₚ := NoZeroSMulDivisors.trans_faithfulSMul R S Sₚ
  have h₁ : map (algebraMap S Sₚ) P ≠ ⊥ := map_ne_bot_of_ne_bot hP
  have h₂ : map (algebraMap R Sₚ) p ≠ ⊥ := map_ne_bot_of_ne_bot hp
  have h₅ : IsLocalRing.maximalIdeal Rₚ ≠ ⊥ :=
      IsLocalRing.isField_iff_maximalIdeal_eq.not.mp (Localization.AtPrime.not_isField p)
  have h₃ : map (algebraMap Rₚ Sₚ) (IsLocalRing.maximalIdeal Rₚ) ≠ ⊥ := map_ne_bot_of_ne_bot h₅
  have h₄ : map (algebraMap Rₚ Sₚ) (IsLocalRing.maximalIdeal Rₚ) ≤ map (algebraMap S Sₚ) P := by
    rw [map_le_iff_le_comap]
    apply le_of_eq
    rw [← under_def, ← liesOver_iff]
    infer_instance
  have t₁ := ramificationIdx_algebra_tower h₃ h₂ h₄
  have t₂ := ramificationIdx_algebra_tower h₁ h₂ le_rfl
  have main := t₁.symm.trans t₂
  have t₃ : ramificationIdx (algebraMap R Rₚ) p (IsLocalRing.maximalIdeal Rₚ) = 1 := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    apply aux
    · exact map_ne_bot_of_ne_bot hp
    · rw [Localization.AtPrime.map_eq_maximalIdeal]
      exact IsPrime.ne_top'
  have t₄ : ramificationIdx (algebraMap S Sₚ) P (map (algebraMap S Sₚ) P) = 1 := by
    apply aux
    · exact map_ne_bot_of_ne_bot hP
    · exact IsPrime.ne_top'
  rwa [t₃, t₄, one_mul, mul_one] at main


theorem Localization.AtPrime.mem_primesOver_of_isPrime {Q : Ideal Sₚ} [Q.IsPrime]
    [Algebra.IsIntegral R S] [IsDedekindRing Sₚ] (hQ : Q ≠ ⊥) :
    Q ∈ (IsLocalRing.maximalIdeal Rₚ).primesOver Sₚ := by
  refine ⟨inferInstance, ?_⟩
  rw [liesOver_iff, ← IsLocalRing.eq_maximalIdeal]
  have : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ inferInstance
  exact Ideal.IsMaximal.under Rₚ Q

theorem Localization.AtPrime.exists_primesOver_of_primesOver
    (Q : (IsLocalRing.maximalIdeal Rₚ).primesOver Sₚ) :
    ∃ q : p.primesOver S, map (algebraMap S Sₚ) q = Q := by
  refine ⟨⟨comap (algebraMap S Sₚ) Q, ⟨IsPrime.under _ _, ?_⟩⟩, ?_⟩
  · have : Q.1.LiesOver p := by
      have := Q.prop.2
      have : (IsLocalRing.maximalIdeal Rₚ).LiesOver p :=
          (liesOver_iff _ _).mpr Localization.AtPrime.comap_maximalIdeal.symm
      apply Ideal.LiesOver.trans Q.1 (IsLocalRing.maximalIdeal Rₚ) p
    have := Ideal.comap_liesOver Q.1 p (IsScalarTower.toAlgHom R S Sₚ)
    exact this
  · have := Q.prop.1
    have := Q.prop.2
    dsimp only
    apply le_antisymm
    · exact map_comap_le
    · intro x hx
      obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective Mₛ x
      rw [liesOver_iff, under_def] at this
      rw [IsLocalization.mk'_mem_iff] at hx
      have : x ∈ comap (algebraMap S Sₚ) Q := hx
      rw [IsLocalization.mk'_mem_map_algebraMap_iff]
      use s
      refine ⟨hs, ?_⟩
      apply Ideal.mul_mem_left
      exact this

variable (S)

/-- Doc. -/
noncomputable def Localization.AtPrime.primesOverEquivPrimesOver [Nontrivial S] [IsDedekindRing S]
    [NoZeroSMulDivisors R S] [NeZero p] :
    p.primesOver S ≃ (IsLocalRing.maximalIdeal Rₚ).primesOver Sₚ := by
  refine Equiv.ofBijective ?_ ⟨?_, ?_⟩
  · intro Q
    exact ⟨map (algebraMap S Sₚ) Q, inferInstance, inferInstance⟩
  · intro Q₁ Q₂ h
    have : Q₁.1.IsMaximal := by
      apply Ring.DimensionLEOne.maximalOfPrime
      apply ne_bot_of_mem_primesOver (R := R)
      exact NeZero.ne p
      exact Q₁.prop
      exact primesOver.isPrime p Q₁
    have : Q₂.1.IsMaximal := by
      apply Ring.DimensionLEOne.maximalOfPrime
      apply ne_bot_of_mem_primesOver (R := R)
      exact NeZero.ne p
      exact Q₂.prop
      exact primesOver.isPrime p Q₂
    simp only [Subtype.mk.injEq] at h
    have := congr_arg (comap (algebraMap S Sₚ) ·) h
    dsimp at this
    rw [Ideal.comap_map_eq_self_of_isMaximal, Ideal.comap_map_eq_self_of_isMaximal] at this
    rwa [SetCoe.ext_iff] at this
    exact IsPrime.ne_top'
    exact IsPrime.ne_top'
  · intro Q
    simp only [Subtype.ext_val_iff]
    exact Localization.AtPrime.exists_primesOver_of_primesOver p Q

@[simp]
theorem Localization.AtPrime.primesOverEquivPrimesOver_apply [Nontrivial S] [IsDedekindRing S]
    [NoZeroSMulDivisors R S] [NeZero p] (P : p.primesOver S) :
    Localization.AtPrime.primesOverEquivPrimesOver p S P = map (algebraMap S Sₚ) P := rfl

theorem Localization.AtPrime.primesOverEquivPrimesOver_inertiagDeg_eq [Nontrivial S]
    [IsDedekindRing S] [NoZeroSMulDivisors R S] [NeZero p] [p.IsMaximal] (P : p.primesOver S) :
    (IsLocalRing.maximalIdeal Rₚ).inertiaDeg
      (Localization.AtPrime.primesOverEquivPrimesOver p S P).val = p.inertiaDeg P.val := by
  convert Localization.AtPrime.inertiaDeg_map_eq_inertiaDeg p P.val
  apply Ring.DimensionLEOne.maximalOfPrime
  · have := P.prop.2
    apply ne_bot_of_liesOver_of_ne_bot (NeZero.ne p)
  · exact P.prop.1

theorem Localization.AtPrime.primesOverEquivPrimesOver_ramificationIdx_eq [IsDedekindDomain R]
    [Nontrivial S] [IsDedekindDomain S] [NoZeroSMulDivisors R S] [Module.Finite R S] [NeZero p]
    (P : p.primesOver S) :
    (IsLocalRing.maximalIdeal Rₚ).ramificationIdx (algebraMap Rₚ Sₚ)
      (Localization.AtPrime.primesOverEquivPrimesOver p S P).val =
        p.ramificationIdx (algebraMap R S) P.val := by
  convert Localization.AtPrime.ramificationIdx_map_eq_ramificationIdx p P.val ?_
  have := P.prop.2
  apply ne_bot_of_liesOver_of_ne_bot (NeZero.ne p)

-- theorem Localization.AtPrime.inertiaDeg_map_eq_inertiaDeg [p.IsMaximal] [P.IsMaximal] :
    -- (IsLocalRing.maximalIdeal Rₚ).inertiaDeg (map (algebraMap S Sₚ) P) = p. := by

#exit

theorem Localization.AtPrime.ramificationIdx_map_eq_ramificationIdx
    [Module.Finite R S] [NeZero p] [IsDedekindDomain R] [P.IsPrime] (hP : P ≠ ⊥)
    [IsDedekindDomain S] [FaithfulSMul R S] :
    (IsLocalRing.maximalIdeal Rₚ).ramificationIdx (algebraMap Rₚ Sₚ) (P.map (algebraMap S Sₚ)) =
      p.ramificationIdx (algebraMap R S) P := by

  refine Set.BijOn.equiv ?_ ⟨?_, ?_, ?_⟩
  · intro I
    exact map (algebraMap S Sₚ) I
  · intro Q hQ
    lift Q to using hQ
    have := hQ.1
    have := hQ.2
    refine ⟨inferInstance, ?_⟩


    sorry
  ·

    sorry
  ·
    sorry








#exit


        · intro x
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
          obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective Mₛ x
          obtain ⟨s', hs⟩ := Ideal.Quotient.mk_surjective (I := P) (Ideal.Quotient.mk P s)⁻¹
          simp only [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ _),
            Ideal.Quotient.algebraMap_eq, RingHom.comp_apply]
          use x * s'
          rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
          have : algebraMap S Sₚ s ∉ Ideal.map (algebraMap S Sₚ) P := by
--            rw [← Ideal.mem_comap, IsLocalization.AtPrime.comap_maximalIdeal Rₚ p]
--            exact s.prop
            sorry
          refine ((inferInstanceAs <|
            (Ideal.map (algebraMap S Sₚ) P).IsPrime).mem_or_mem ?_).resolve_left this
          rw [mul_sub, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mul_cancel_left,
            ← map_mul, ← map_sub, ← Ideal.mem_comap]
--          rw [IsLocalization.AtPrime.comap_maximalIdeal Rₚ p]
instance [IsDomain S] [IsDomain R] [FaithfulSMul R S] : Algebra (FractionRing Rₚ) (FractionRing Sₚ) :=
  FractionRing.liftAlgebra Rₚ (FractionRing Sₚ)

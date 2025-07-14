import Mathlib

section relNorm

attribute [local instance] FractionRing.liftAlgebra

open Algebra

theorem Algebra.intNorm_intNorm
    (A B C : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
    [IsDomain B] [IsIntegrallyClosed B] [CommRing C] [IsDomain C] [IsIntegrallyClosed C] [Algebra A B]
    [Algebra A C] [Algebra B C] [IsScalarTower A B C] [Module.Finite A B] [Module.Finite A C]
    [Module.Finite B C] [NoZeroSMulDivisors A B] [NoZeroSMulDivisors A C] [NoZeroSMulDivisors B C]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    [Algebra.IsSeparable (FractionRing B) (FractionRing C)]
    (x : C) :
    intNorm A B (intNorm B C x) = intNorm A C x := by
  apply FaithfulSMul.algebraMap_injective A (FractionRing A)
  have := Module.Free.of_divisionRing (FractionRing A) (FractionRing B)
  have := Module.Free.of_divisionRing (FractionRing B) (FractionRing C)
  rw [algebraMap_intNorm_fractionRing, algebraMap_intNorm_fractionRing,
    algebraMap_intNorm_fractionRing, Algebra.norm_norm]

open Ideal

attribute [local instance] FractionRing.liftAlgebra

variable (R : Type*) [CommRing R] [IsDomain R] {T S : Type*} [CommRing S] [IsDomain S]
  [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]
  [NoZeroSMulDivisors R S] [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
  [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [Algebra T S] [Algebra T R]
  [Module.Finite T S] [Module.Finite T R] [NoZeroSMulDivisors T S]
  [NoZeroSMulDivisors T R] [IsScalarTower T R S]
  [Algebra.IsSeparable (FractionRing T) (FractionRing S)]
  [Algebra.IsSeparable (FractionRing T) (FractionRing R)]

theorem Ideal.spanNorm_spanNorm_of_isPrincipal {I : Ideal S} (hI : Submodule.IsPrincipal I) :
    spanNorm T (spanNorm R I) = spanNorm T I := by
  obtain ⟨x, rfl⟩ := hI
  simp [intNorm_intNorm]

open nonZeroDivisors

set_option maxHeartbeats 1000000 in
theorem Ideal.spanNorm_spanNorm [IsDedekindDomain S] [IsDedekindDomain T] (I : Ideal S) :
    spanNorm T (spanNorm R I) = spanNorm T I := by
  refine eq_of_localization_maximal (fun P hP ↦ ?_)
  let P' := Algebra.algebraMapSubmonoid S P.primeCompl
  let P'' := Algebra.algebraMapSubmonoid R P.primeCompl
  let Tₚ := Localization.AtPrime P
  let Sₚ := Localization P'
  let Rₚ := Localization P''
  let _ : Algebra Tₚ Sₚ := localizationAlgebra P.primeCompl S
  have : IsScalarTower T Tₚ Sₚ := sorry
    -- IsScalarTower.of_algebraMap_eq (fun x =>
      -- (IsLocalization.map_eq (T := P') (Q := Localization P') P.primeCompl.le_comap_map x).symm)
  have h' : P' ≤ S⁰ :=
    map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
      P.primeCompl_le_nonZeroDivisors
  have h'' : P'' ≤ R⁰ :=
    map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
      P.primeCompl_le_nonZeroDivisors
  have : IsDomain Sₚ := IsLocalization.isDomain_localization h'
  have : IsDomain Rₚ := IsLocalization.isDomain_localization h''
  have : IsDedekindDomain Sₚ := IsLocalization.isDedekindDomain S h' _
  have : IsPrincipalIdealRing Sₚ :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime S P ?_
  have := NoZeroSMulDivisors_of_isLocalization T S Tₚ Sₚ P.primeCompl_le_nonZeroDivisors
  have := Module.Finite_of_isLocalization T S Tₚ Sₚ P.primeCompl
  let L := FractionRing S
  let g : Sₚ →+* L := IsLocalization.map _ (M := P') (T := S⁰) (RingHom.id S) h'
  algebraize [g]
  have : IsScalarTower S Sₚ (FractionRing S) := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHom.comp_id])
  have := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P' Sₚ (FractionRing S)
  have : Algebra.IsSeparable (FractionRing Tₚ) (FractionRing Sₚ) := by
    apply Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv Tₚ (FractionRing T)).symm.toRingEquiv
      (FractionRing.algEquiv Sₚ (FractionRing S)).symm.toRingEquiv
    apply IsLocalization.ringHom_ext T⁰
    ext
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply T Tₚ (FractionRing T), AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes, IsScalarTower.algebraMap_apply T S L,
      IsScalarTower.algebraMap_apply S Sₚ L, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    simp only [← IsScalarTower.algebraMap_apply]
  rw [← spanIntNorm_localization (R := T) (S := S)
    (Rₘ := Localization.AtPrime P) (Sₘ := Localization P') _ _ P.primeCompl_le_nonZeroDivisors]

  have : IsIntegralClosure Rₚ Rₚ (FractionRing Rₚ) := sorry
  let _ : Algebra Rₚ (Localization P') := sorry
  have : Module.Finite Rₚ (Localization P') := sorry
  have : NoZeroSMulDivisors Rₚ (Localization P') := sorry
  let _ : Algebra (FractionRing Rₚ) (FractionRing (Localization P')) := sorry
  have : Algebra.IsSeparable (FractionRing Rₚ) (FractionRing (Localization P')) := sorry

  have : Submodule.IsPrincipal (I.map (algebraMap S (Localization P'))) := by
    exact IsPrincipalIdealRing.principal (map (algebraMap S (Localization P')) I)

  rw [← Ideal.spanNorm_spanNorm_of_isPrincipal Rₚ this]


end relNorm

#exit

section associates

theorem Associates.count_mk_factors_eq_multiset_count {α : Type*} [CancelCommMonoidWithZero α]
    [UniqueFactorizationMonoid α] [Subsingleton αˣ] [DecidableEq (Associates α)] [DecidableEq α]
    [(p : Associates α) → Decidable (Irreducible p)] {p a : α} (hp : Irreducible p) (ha : a ≠ 0) :
    (Associates.mk p).count (Associates.mk a).factors =
      Multiset.count p (UniqueFactorizationMonoid.normalizedFactors a) := by
  rw [Associates.factors_mk _ ha, Associates.count_some (Associates.irreducible_mk.mpr hp),
    ← Multiset.count_map_eq_count' _ _ Subtype.val_injective, Associates.map_subtype_coe_factors',
    UniqueFactorizationMonoid.factors_eq_normalizedFactors,
    ← Multiset.count_map_eq_count' _ _ (Associates.mk_injective (M := α))]

end associates

section primesOver

theorem Ideal.ne_bot_of_mem_primesOver {A B : Type*} [CommRing A] [Ring B] [Algebra A B]
    [NoZeroSMulDivisors A B] [Nontrivial B] {p : Ideal A}
    (hp : p ≠ ⊥) {P : Ideal B} (hP : P ∈ p.primesOver B) :
    P ≠ ⊥ := @ne_bot_of_liesOver_of_ne_bot _ _ _ _ _ _ _ _ hp P hP.2

end primesOver

section primesplitting

open Ideal

@[simp]
theorem Ideal.pow_eq_top_iff {R : Type*} [CommSemiring R] (I : Ideal R) (n : ℕ) :
    I ^ n = ⊤ ↔ I = ⊤ ∨ n = 0 := by
  constructor
  · intro h
    refine or_iff_not_imp_right.mpr fun hn ↦ ?_
    rw [eq_top_iff_one] at h ⊢
    exact pow_le_self hn h
  · intro h
    obtain h | h := h
    · simp [h, top_pow]
    · simp [h]

theorem Ideal.liesOver_iff_dvd_map {A : Type*} [CommSemiring A] {B : Type*} [CommRing B]
    [IsDedekindDomain B] [Algebra A B] {P : Ideal B} {p : Ideal A} (hP : P ≠ ⊤) [p.IsMaximal] :
    P.LiesOver p ↔ P ∣ Ideal.map (algebraMap A B) p := by
  rw [liesOver_iff, dvd_iff_le, under_def, map_le_iff_le_comap,
    IsCoatom.le_iff_eq (by rwa [← isMaximal_def]) (comap_ne_top _ hP), eq_comm]

noncomputable instance {A : Type*} [CommRing A] (p : Ideal A) [hpm : p.IsMaximal] (B : Type*)
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
    [Algebra.IsIntegral A B] :
    Fintype (p.primesOver B) := Set.Finite.fintype (primesOver_finite p B)

variable {R S : Type*} [CommRing R] -- [IsDedekindDomain R]
  [CommRing S] -- [IsDedekindDomain S]
  [Algebra R S] [NoZeroSMulDivisors R S] -- [Algebra.IsIntegral R S]
  -- [Nontrivial S]

open Ideal

namespace IsDedekindDomain.HeightOneSpectrum

theorem maxPowDividing_ne_one_iff_mem_primesOver [IsDedekindDomain S] (v : HeightOneSpectrum S)
    (P : Ideal R) [P.IsMaximal] (hP : P ≠ 0) :
    maxPowDividing v (map (algebraMap R S) P) ≠ 1 ↔ v.asIdeal ∈ P.primesOver S := by
  classical
  simpa [maxPowDividing, one_eq_top, pow_eq_top_iff, IsPrime.ne_top',
      Associates.count_ne_zero_iff_dvd (map_ne_bot_of_ne_bot hP) (irreducible v), primesOver,
      liesOver_iff_dvd_map] using fun _ ↦ v.isPrime

theorem maxPowDividing_eq_pow_multiset_count [IsDedekindDomain S] [DecidableEq (Ideal S)]
    (v : HeightOneSpectrum S) {I : Ideal S} (hI : I ≠ 0) :
    maxPowDividing v I =
      v.asIdeal ^ Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) := by
  classical
  rw [maxPowDividing, Associates.count_mk_factors_eq_multiset_count (irreducible v) hI]



-- theorem Ideal.prod_heightOneSpectrum_factorization {R : Type*} [CommRing R] [IsDedekindDomain R]
--     {I : Ideal R} [NeZero I] :
--     ∏ v : {v : IsDedekindDomain.HeightOneSpectrum R | v.asIdeal ∣ I}, v.val.maxPowDividing I
--       = I := by
--   classical
--   have := finprod_heightOneSpectrum_factorization (NeZero.ne I)
--   convert this
--   rw [finprod_eq_finset_prod_of_mulSupport_subset (s := {v | v.asIdeal ∣ I}.toFinset),
--     ← Finset.prod_set_coe]
--   intro v hv
--   simp only [maxPowDividing, Function.mem_mulSupport, one_eq_top, ne_eq, pow_eq_top_iff,
--     IsPrime.ne_top', false_or] at hv
--   have := Associates.count_ne_zero_iff_dvd (NeZero.ne I) (irreducible v)
--   simp only [this] at hv
--   simp only [Set.coe_toFinset, Set.mem_setOf_eq, hv]

variable (S) in
def equiv :
    HeightOneSpectrum S ≃ {P : Ideal S // P.IsPrime ∧ P ≠ ⊥} where
  toFun v := ⟨v.asIdeal, v.isPrime, v.ne_bot⟩
  invFun P := ⟨P.val, P.prop.1, P.prop.2⟩

@[simp]
theorem equiv_apply (v : HeightOneSpectrum S) :
    equiv S v = v.asIdeal := rfl

-- variable (S) in
-- def ofPrimesOver {I : Ideal R} (hI : I ≠ ⊥) :
--     I.primesOver S → IsDedekindDomain.HeightOneSpectrum S :=
--   fun ⟨P, ⟨hP, _⟩⟩ ↦ ⟨P, hP, ne_bot_of_liesOver_of_ne_bot hI _⟩

-- @[simp]
-- theorem ofPrimesOver_asIdeal {I : Ideal R} (hI : I ≠ ⊥)
--     {P : Ideal S} (hP : P ∈ I.primesOver S) :
--     (ofPrimesOver S hI ⟨P, hP⟩).asIdeal = P := by
--   rw [ofPrimesOver]
--   · exact hP.1
--   · exact hP.2

-- theorem mem_ofPrimesOver_iff {I : Ideal R} (hI : I ≠ ⊥) {x : IsDedekindDomain.HeightOneSpectrum S} :
--     x ∈ Set.range (ofPrimesOver S hI) ↔ x.asIdeal ∈ I.primesOver S := by
--   simp [Set.mem_range, IsDedekindDomain.HeightOneSpectrum.ext_iff]

open IsDedekindDomain HeightOneSpectrum

noncomputable def equivPrimesOver [IsDedekindDomain S] {P : Ideal R}
    [P.IsMaximal] (hP : P ≠ 0) :
    {v : HeightOneSpectrum S // v.asIdeal ∣ map (algebraMap R S) P} ≃ (P.primesOver S) :=
  Set.BijOn.equiv asIdeal
    ⟨fun v hv ↦ ⟨v.isPrime, by rwa [liesOver_iff_dvd_map v.isPrime.ne_top]⟩,
    fun _ _ _ _ h ↦ HeightOneSpectrum.ext_iff.mpr h,
    fun Q hQ ↦ ⟨⟨Q, hQ.1, ne_bot_of_mem_primesOver hP hQ⟩,
      (liesOver_iff_dvd_map hQ.1.ne_top).mp hQ.2, rfl⟩⟩

@[simp]
theorem equivPrimesOver_apply [IsDedekindDomain S] {P : Ideal R} [P.IsMaximal] (hP : P ≠ 0)
    (v : {v : HeightOneSpectrum S // v.asIdeal ∣ map (algebraMap R S) P}) :
    equivPrimesOver hP v = v.1.asIdeal := rfl



end IsDedekindDomain.HeightOneSpectrum

variable [IsDedekindDomain S] [Algebra.IsIntegral R S]

open IsDedekindDomain HeightOneSpectrum

theorem Ideal.map_algebraMap_eq_finset_prod_pow (P : Ideal R) [P.IsMaximal] (hP : P ≠ 0) :
    map (algebraMap R S) P = ∏ Q ∈ P.primesOver S, Q ^ P.ramificationIdx (algebraMap R S) Q := by
  classical
  have h : map (algebraMap R S) P ≠ 0 := map_ne_bot_of_ne_bot hP
  rw [← finprod_heightOneSpectrum_factorization (I := P.map (algebraMap R S)) h]
  let hF : Fintype {v : HeightOneSpectrum S | v.asIdeal ∣ map (algebraMap R S) P} :=
    (finite_factors h).fintype
  rw [finprod_eq_finset_prod_of_mulSupport_subset
    (s := {v | v.asIdeal ∣ P.map (algebraMap R S)}.toFinset), ← Finset.prod_set_coe,
    ← Finset.prod_set_coe]
  · let _ : Fintype {v : HeightOneSpectrum S // v.asIdeal ∣ map (algebraMap R S) P} := hF
    refine Fintype.prod_equiv (equivPrimesOver hP) _ _ ?_
    intro ⟨v, hv⟩
    simp [maxPowDividing_eq_pow_multiset_count _ h,
      ramificationIdx_eq_factors_count h v.isPrime v.ne_bot]
  · intro v hv
    simpa? [maxPowDividing, Function.mem_mulSupport, IsPrime.ne_top _,
      Associates.count_ne_zero_iff_dvd h (irreducible v)] using hv




#exit
    refine Finset.prod_nbij asIdeal ?_ ?_ ?_ ?_
    · intro v hv

      sorry
    · exact fun _ _ _ _ h ↦ HeightOneSpectrum.ext_iff.mpr h
    · intro v hv
      sorry
    · sorry


#exit



  let T := {v : IsDedekindDomain.HeightOneSpectrum S | v.asIdeal ∣ P.map (algebraMap R S)}
  have : Fintype T := by
    refine Set.Finite.fintype ?_
    exact finite_factors h₁
  rw [finprod_eq_finset_prod_of_mulSupport_subset (s := T.toFinset)]
  · refine Finset.prod_nbij (fun v ↦ v.asIdeal) ?_ ?_ ?_ ?_
    · intro v hv
      rw [Set.mem_toFinset]
      refine ⟨v.isPrime, ?_⟩
      · rw [liesOver_iff_dvd_map _ _ IsPrime.ne_top']
        simp only [Set.mem_toFinset] at hv
        exact hv
    · apply Function.Injective.injOn
      intro _ _ _
      rwa [IsDedekindDomain.HeightOneSpectrum.ext_iff]
    · intro Q hQ
      simp at hQ
      simp only [Set.coe_toFinset, Set.mem_image]
      refine ⟨⟨Q, hQ.1, ne_bot_of_mem_primesOver hP hQ⟩, ?_, rfl⟩
      simp [T]
      have := hQ.2
      rwa [liesOver_iff_dvd_map] at this
      exact hQ.1.ne_top
    · intro v hv
      rw [maxPowDividing_eq_pow_multiset_count _ h₁,
        IsDedekindDomain.ramificationIdx_eq_factors_count h₁ v.isPrime v.ne_bot,
        UniqueFactorizationMonoid.factors_eq_normalizedFactors]
  · intro v hv
    simp [T]
    rw [Function.mem_mulSupport] at hv
    rw [maxPowDividing_ne_one_iff_mem_primesOver] at hv
    have := hv.2
    rwa [liesOver_iff_dvd_map] at this
    exact IsPrime.ne_top'
    exact hP

#exit

  let T : Finset (IsDedekindDomain.HeightOneSpectrum S) := by
    exact Finset.image (equiv S).symm (P.primesOver S).toFinset

    have hP : P ≠ ⊥ := sorry
    exact Finset.image (ofPrimesOver S hP) Finset.univ
  rw [finprod_eq_finset_prod_of_mulSupport_subset (s := T)] -- _ (s := (P.primesOver S).toFinset)]
  · let e : (P.primesOver S).toFinset ≃ T := by
      refine Equiv.ofBijective ?_ ⟨?_, ?_⟩
      · intro x

        have := over S h₁ x
        sorry
      · sorry
      · sorry
  · intro x hx
    rw [Fintype.coe_image_univ, mem_primesOverToIsDedekindDomainHeightOneSpectrum_iff]
    rw [primesOver, Set.mem_setOf_eq]
    refine ⟨x.isPrime, ?_⟩
    rw [liesOver_iff_dvd_map]
    rw [Function.mem_mulSupport] at hx
    rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing] at hx
    replace hx :
        (Associates.mk x.asIdeal).count (Associates.mk (map (algebraMap R S) P)).factors ≠ 0 := by
      rw [one_eq_top] at hx
      rw [ne_eq] at hx
      rw [pow_eq_top_iff, not_or] at hx
      exact hx.2
    rwa [Associates.count_ne_zero_iff_dvd] at hx
    · exact h₁
    exact IsDedekindDomain.HeightOneSpectrum.irreducible x
    exact IsPrime.ne_top'











end primesplitting

open Ideal Submodule

attribute [local instance] FractionRing.liftAlgebra

variable (R : Type*) [CommRing R] [IsDomain R] {S : Type*} [CommRing S] [IsDomain S]
  [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]
  [NoZeroSMulDivisors R S] [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
  [IsDedekindDomain R] [IsDedekindDomain S]

theorem lemm1 (Q : Ideal S) (hQ : IsMaximal Q) (P : Ideal R) [Q.LiesOver P]
    (h₁ : IsPrincipal Q) (h₂ : IsPrincipal P) [IsGalois (FractionRing R) (FractionRing S)] :
    relNorm R Q = P ^ P.inertiaDeg Q := by
  obtain ⟨a, rfl⟩ := h₁
  --obtain ⟨b, rfl⟩ := h₂
  simp only [submodule_span_eq, relNorm_singleton]
  have : Function.Injective (map (algebraMap R S)) := sorry
  apply this
  simp only [Ideal.map_span, Set.image_singleton]
  rw [Algebra.algebraMap_intNorm_of_isGalois]
  rw [← Ideal.prod_span_singleton]
  rw [← Ideal.mapHom_apply, map_pow]
  simp
  have := finprod_heightOneSpectrum_factorization (I := Ideal.map (algebraMap R S) P)





  sorry

variable [Module.Free ℤ R] [Module.Free ℤ S] [Module.Finite ℤ S] [Module.Finite ℤ R]

open UniqueFactorizationMonoid

theorem lemm2 (I : Ideal S) :
    absNorm (relNorm R I) = absNorm I := by
  by_cases hI : I = ⊥
  · simp [hI]
  rw [← prod_normalizedFactors_eq_self hI]
  refine Multiset.prod_induction (fun I ↦ absNorm (relNorm R I) = absNorm I) _ ?_ ?_ ?_
  · intro _ _ hx hy
    rw [map_mul, map_mul, map_mul, hx, hy]
  · simp
  · intro Q hQ
    have hQ' : Q ≠ ⊥ := by
      contrapose! hQ
      simpa [hQ] using zero_notMem_normalizedFactors _
    rw [Ideal.mem_normalizedFactors_iff hI] at hQ
    have : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ' hQ.1
    let P := under R Q
    let p := absNorm (under ℤ P)
    have : Q.LiesOver P := by simp [liesOver_iff, P]
    have : P.LiesOver (span {(p : ℤ)}) := sorry
    have : Q.LiesOver (span {(p : ℤ)}) := sorry
    have : (span {(p : ℤ)}).IsMaximal := sorry
    have hp : Prime (p : ℤ) := sorry
    rw [lemm1 R Q P, map_pow, absNorm_eq_pow_inertiaDeg Q hp, absNorm_eq_pow_inertiaDeg P hp,
      inertiaDeg_algebra_tower (span {(p : ℤ)}) P Q, pow_mul]

theorem lemm3  (K L : Type*) [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [IsFractionRing S L] [Algebra K L] [Module.Finite K L] (I : Ideal R) :
    relNorm R (map (algebraMap R S) I) = I ^ Module.finrank K L := by
  by_cases hI : I = ⊥
  · rw [hI, Ideal.map_bot, relNorm_bot, ← Ideal.zero_eq_bot, zero_pow Module.finrank_pos.ne']
  rw [← prod_normalizedFactors_eq_self hI]
  refine Multiset.prod_induction
    (fun I ↦ relNorm R (map (algebraMap R S) I) = I ^ Module.finrank K L) _ ?_ ?_ ?_
  sorry

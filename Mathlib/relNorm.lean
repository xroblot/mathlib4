import Mathlib

set_option linter.style.header false

attribute [local instance] FractionRing.liftAlgebra

open Algebra


theorem step11 {R S T : Type*} [CommRing R] [IsDomain R] {S : Type*} [CommRing S] [IsDomain S]
    [CommRing T] [IsDomain T]
    [IsIntegrallyClosed R] [IsIntegrallyClosed S] [IsIntegrallyClosed T]
    [Algebra R S] [Algebra R T] [Algebra S T] [Module.Finite R S] [Module.Finite R T]
    [Module.Finite S T] [NoZeroSMulDivisors R S] [NoZeroSMulDivisors R T] [NoZeroSMulDivisors S T]
    [IsScalarTower R S T]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    [Algebra.IsSeparable (FractionRing R) (FractionRing T)] (x : S)
    {E : Type*} [Field E] [IsAlgClosed E] [Algebra (FractionRing S) E]
    [Algebra (FractionRing R) E] [IsScalarTower (FractionRing R) (FractionRing S) E]
    [FaithfulSMul (FractionRing S) E] :
    ∃ y : S, algebraMap R S (intNorm R S x) = x * y := by
  classical
  let K := FractionRing R
  let L := FractionRing S
  let τ := IsScalarTower.toAlgHom K L E
  let u := ∏ σ ∈ Finset.univ.erase τ, σ ((algebraMap S (FractionRing S)) x)
  let _ : Algebra S E := by
    refine RingHom.toAlgebra ?_
    exact (algebraMap L E).comp (algebraMap S L)
  have : u ∈ (algebraMap S E).range := by
    apply Subring.prod_mem
    intro i _
    simp only [RingHom.mem_range]
    refine ⟨sorry, ?_⟩
    rw [RingHom.algebraMap_toAlgebra]
    simp only [RingHom.coe_comp, Function.comp_apply]


  obtain ⟨y, hy⟩ := this

-- #exit
--   refine ⟨sorry, ?_⟩
--   apply FaithfulSMul.algebraMap_injective S (FractionRing S)
--   apply FaithfulSMul.algebraMap_injective (FractionRing S) E
--   have := algebraMap_intNorm (A := R) (K := FractionRing R) (L := FractionRing S) (B := S) x
--   rw [← IsScalarTower.algebraMap_apply R S]
--   rw [IsScalarTower.algebraMap_apply R (FractionRing R)]
--   rw [this]
--   rw [← IsScalarTower.algebraMap_apply]
--   rw [norm_eq_prod_embeddings]
--   let τ := IsScalarTower.toAlgHom K L E
--   let u := ∏ σ ∈ Finset.univ.erase τ, σ ((algebraMap S (FractionRing S)) x)
--   rw [← Finset.univ.mul_prod_erase (a := τ)]
--   unfold τ
--   rw [map_mul]

-- #exit

  -- let u : T := sorry

  -- have h₁ : algebraMap R T (intNorm R S x) = (algebraMap S T x) * u := by
  --   have := Algebra.algebraMap_intNorm_of_isGalois R T (x := algebraMap S T x)

  -- have h₂ : u ∈ (algebraMap S T).range := sorry
  -- obtain ⟨y, hy⟩ := h₂
  -- refine ⟨y, ?_⟩
  -- have : Function.Injective (algebraMap S T) := sorry
  -- apply this
  -- rw [← IsScalarTower.algebraMap_apply, h₁, map_mul, hy]



variable (A : Type*) (B : Type*) [CommRing A] [CommRing B] [Algebra A B] [IsDomain A]
  [IsIntegrallyClosed A] [IsDomain B] [IsIntegrallyClosed B] [Module.Finite A B]
  [NoZeroSMulDivisors A B]

theorem step1 [IsGalois (FractionRing A) (FractionRing B)] (x : B) :
    ∃ y : B, algebraMap A B (intNorm A B x) = x * y := by
  classical
  refine ⟨(∏ σ ∈ Finset.univ.erase (AlgEquiv.refl : B ≃ₐ[A] B), σ x), ?_⟩
  calc
    _ = (AlgEquiv.refl : B ≃ₐ[A] B) x *
          ∏ σ ∈ Finset.univ.erase (AlgEquiv.refl : B ≃ₐ[A] B), σ x := by sorry
    _ = ∏ σ : B ≃ₐ[A] B, σ x := sorry
    _ = algebraMap A B (intNorm A B x) := (algebraMap_intNorm_of_isGalois A B).symm

theorem step2 [Algebra.IsSeparable (FractionRing A) (FractionRing B)] (x : B) :
    ∃ y : B, algebraMap A B (intNorm A B x) = x * y := by
  let E := FractionRing A
  let F := FractionRing B

  let L := AlgebraicClosure (FractionRing B)
  let N := IntermediateField.normalClosure (FractionRing A) (FractionRing B)
    (AlgebraicClosure (FractionRing B))
  let C := integralClosure B N


theorem step01 {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]
    [NoZeroSMulDivisors R S] [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    [IsGalois (FractionRing R) (FractionRing S)]
    {I : Ideal S} {x : S} (hx : x ∈ I) :
    algebraMap R S ((Algebra.intNorm R S) x) ∈ I := by
  sorry

theorem step110 {R S T : Type*} [CommRing R] [IsDomain R] {S : Type*} [CommRing S] [IsDomain S]
    [CommRing T] [IsDomain T]
    [IsIntegrallyClosed R] [IsIntegrallyClosed S] [IsIntegrallyClosed T]
    [Algebra R S] [Algebra R T] [Algebra S T] [Module.Finite R S] [Module.Finite R T]
    [Module.Finite S T] [NoZeroSMulDivisors R S] [NoZeroSMulDivisors R T] [NoZeroSMulDivisors S T]
    [IsScalarTower R S T]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    [Algebra.IsSeparable (FractionRing R) (FractionRing T)]
    [Algebra.IsSeparable (FractionRing S) (FractionRing T)]
    [IsGalois (FractionRing R) (FractionRing T)]
    {I : Ideal S} [I.IsMaximal] {x : S} (hx : x ∈ I) :
    (algebraMap R S) ((Algebra.intNorm R S) x) ∈ I := by
  have := step01 (R := R) (Ideal.mem_map_of_mem (algebraMap S T) hx)
  rw [IsScalarTower.algebraMap_apply R S T] at this
  rw [← Ideal.mem_comap] at this
  rw [Ideal.comap_map_eq_self_of_isMaximal] at this
  rw [Algebra.intNorm_intNorm]



theorem step10 {R : Type*} [CommRing R] [IsDomain R] {S : Type*} [CommRing S] [IsDomain S]
    [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]
    [NoZeroSMulDivisors R S] [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    [IsGalois (FractionRing R) (FractionRing S)]
    {I : Ideal S} :
    spanNorm R I ≤ comap (algebraMap R S) I := by
  classical
  rw [spanNorm]
  rw [Ideal.map]
  rw [Ideal.span_le]
  rw [← @Submodule.span_le]
  apply Submodule.span_induction
  · rintro _ ⟨x, hx, rfl⟩
    rw [Ideal.mem_comap]
    rw [Algebra.algebraMap_intNorm_of_isGalois, ← Finset.prod_erase_mul _ _
      (Finset.mem_univ AlgEquiv.refl), AlgEquiv.coe_refl, Ideal.mem_span_singleton]

    sorry
  · sorry
  · sorry
  · sorry


  obtain ⟨x, rfl⟩ := hI
  rw [submodule_span_eq, spanNorm_singleton, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap,
    Algebra.algebraMap_intNorm_of_isGalois, ← Finset.prod_erase_mul _ _
    (Finset.mem_univ AlgEquiv.refl), AlgEquiv.coe_refl, Ideal.mem_span_singleton]
  exact dvd_mul_left x _

theorem step2 {R : Type*} [CommRing R] [IsDomain R] {S : Type*} [CommRing S] [IsDomain S]
    [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]
    [NoZeroSMulDivisors R S] [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    [IsGalois (FractionRing R) (FractionRing S)]
    {I : Ideal S} :
    spanNorm R I ≤ comap (algebraMap R S) I := by
  sorry

attribute [local instance] FractionRing.liftAlgebra

variable (R : Type*) [CommRing R] {S : Type*} [CommRing S] [Algebra R S] [Module.Finite R S]
 [IsDomain R] [IsDomain S] [FaithfulSMul R S] [IsDedekindDomain S]

variable (p : Ideal R) (Q Q' : p.primesOver S)

variable [IsDedekindDomain R] [IsIntegrallyClosed R]

variable {R p} in
open Classical in
theorem Ideal.card_stabilizer_eq_ramificationIdxIn_mul_inertiaDegIn [p.IsMaximal]
    [IsGalois (FractionRing R) (FractionRing S)] (hp : p ≠ ⊥) :
    Fintype.card (MulAction.stabilizer (S ≃ₐ[R] S) Q) =
      p.ramificationIdxIn S * p.inertiaDegIn S := by
  have := Ideal.isPretransitive_of_isGalois p (B := S) (FractionRing R) (FractionRing S)
  rw [← mul_right_inj' (primesOver_ncard_ne_zero p S),
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp S (FractionRing R) (FractionRing S),
    ← Nat.card_coe_set_eq, ← MulAction.index_stabilizer_of_transitive (S ≃ₐ[R] S) Q,
    ← Nat.card_eq_fintype_card, Subgroup.index_mul_card, Nat.card_eq_fintype_card,
    ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  exact Fintype.ofEquiv_card (galRestrict R (FractionRing R) (FractionRing S) S).toEquiv

variable [IsIntegrallyClosed S]

open nonZeroDivisors

theorem relNorm_eq_pow_of_isMaximal'' [IsGalois (FractionRing R) (FractionRing S)] (P : Ideal S)
    [P.IsMaximal] {p : Ideal R} [p.IsMaximal] [P.LiesOver p] (hp : p ≠ ⊥) (hP : IsPrincipal P) :
    relNorm R P = p ^ p.inertiaDeg P := by
  classical
  have hPp : P ∈ p.primesOver S := ⟨IsMaximal.isPrime' _, inferInstance⟩
  refine (map_algebraMap_injective R S).eq_iff.mp ?_
  rw [show Ideal.map (algebraMap R S) ((relNorm R) P) = ∏ g : S ≃ₐ[R] S, g • P by
    obtain ⟨a, ha⟩ := hP
    simp [relNorm_singleton, Set.image_singleton, Algebra.algebraMap_intNorm_of_isGalois,
      ← Ideal.prod_span_singleton, ha, pointwise_smul_def, Ideal.map_span]]
  rw [Ideal.map_pow, map_algebraMap_eq_finset_prod_pow S hp, Finset.prod_eq_multiset_prod,
    Finset.prod_multiset_count, ← inertiaDegIn_eq_inertiaDeg p P (FractionRing R) (FractionRing S),
    ← Finset.prod_pow]
  have {Q} (hQ : Q ∈ (p.primesOver S).toFinset) :
      ramificationIdx (algebraMap R S) p Q = p.ramificationIdxIn S := by
    lift Q to (p.primesOver S) using Set.mem_toFinset.mp hQ
    rw [ramificationIdxIn_eq_ramificationIdx p Q (FractionRing R) (FractionRing S)]
  simp_rw +contextual [this, ← pow_mul]
  lift P to (p.primesOver S) using hPp
  refine Finset.prod_congr (Finset.ext fun Q ↦ ?_) fun Q hQ ↦ ?_
  · simp only [Multiset.mem_toFinset, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and,
      Set.mem_toFinset]
    refine ⟨?_, fun hQ ↦ ?_⟩
    · rintro ⟨σ, rfl⟩
      exact (σ • P).prop
    · lift Q to (p.primesOver S) using hQ
      simp_rw [← coe_smul_primesOver, Subtype.coe_inj]
      have := Ideal.isPretransitive_of_isGalois p (B := S) (FractionRing R) (FractionRing S)
      exact MulAction.exists_smul_eq ..
  · lift Q to (p.primesOver S) using Set.mem_toFinset.mp hQ
    have : Fintype.card {g : S ≃ₐ[R] S // Q.val = g • P.val} =
        Fintype.card (MulAction.stabilizer (S ≃ₐ[R] S) Q) := by
      simp_rw [← coe_smul_primesOver, Subtype.coe_inj]
      have := Ideal.isPretransitive_of_isGalois p (B := S) (FractionRing R) (FractionRing S)
      obtain ⟨σ, rfl⟩ := MulAction.exists_smul_eq (S ≃ₐ[R] S) Q P
      rw [Fintype.subtype_card, Fintype.subtype_card _ (fun _ ↦ by simp)]
      refine Finset.card_equiv (Equiv.mulRight σ) fun _ ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulRight,
        MulAction.mem_stabilizer_iff, eq_comm, smul_smul]
    rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val, ← Fintype.card_subtype, this,
      ← card_stabilizer_eq_ramificationIdxIn_mul_inertiaDegIn Q hp]

attribute [local instance] Ideal.Quotient.field

attribute [-instance] instAlgebraAtPrimeFractionRing

open IsLocalization.AtPrime in
theorem relNorm_eq_pow_of_isMaximal' [IsGalois (FractionRing R) (FractionRing S)] (P : Ideal S)
    [P.IsMaximal] (p : Ideal R) [p.IsMaximal] [P.LiesOver p] (hp : p ≠ ⊥) :
    relNorm R P = p ^ p.inertiaDeg P := by
  refine eq_of_localization_maximal (fun q hq ↦ ?_)
  let Rₚ := Localization.AtPrime q
  let Mₛ := Algebra.algebraMapSubmonoid S q.primeCompl
  let Sₚ := Localization Mₛ
  by_cases hq : p = q
  · subst hq
    have : NeZero p := ⟨hp⟩
    have hP : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp P
    have : IsScalarTower R Sₚ (FractionRing S) := .trans_right R S Sₚ (FractionRing S)
    have : NoZeroSMulDivisors S Sₚ := noZeroSMulDivisors_localization p Sₚ
    have : IsGalois (FractionRing Rₚ) (FractionRing Sₚ) := by
      apply IsGalois.of_equiv_equiv (F := FractionRing R) (E := FractionRing S)
        (f := ((FractionRing.algEquiv Rₚ (FractionRing R)).restrictScalars R).symm)
        (g := ((FractionRing.algEquiv Sₚ (FractionRing S)).restrictScalars R).symm)
      ext x
      obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective R⁰ x
      simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        IsFractionRing.mk'_eq_div, map_div₀, ← IsScalarTower.algebraMap_apply,
        AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    have : (Ideal.map (algebraMap S Sₚ) P).IsMaximal := by
      apply Ring.DimensionLEOne.maximalOfPrime
      · exact Ideal.map_ne_bot_of_ne_bot hP
      · exact isPrime_algebraMap_of_liesOver p P Sₚ
    have : (Ideal.map (algebraMap R Rₚ) p).IsMaximal := map_isMaximal p Rₚ
    have : (Ideal.map (algebraMap S Sₚ) P).LiesOver (IsLocalRing.maximalIdeal Rₚ) :=
      liesOver_map_of_liesOver p P Rₚ Sₚ
    have : (Ideal.map (algebraMap S Sₚ) P).LiesOver (Ideal.map (algebraMap R Rₚ) p) := by
      rwa [map_eq_maximalIdeal p Rₚ]
    rw [← spanNorm_eq, ← spanIntNorm_localization (R := R) (Sₘ := Sₚ) (M := p.primeCompl) _
      (primeCompl_le_nonZeroDivisors p), spanNorm_eq, Ideal.map_pow]
    rw [relNorm_eq_pow_of_isMaximal'' _ (Ideal.map (algebraMap S Sₚ) P)
      (p := Ideal.map (algebraMap R Rₚ) p)]
    · rw [Localization.AtPrime.map_eq_maximalIdeal]
      rw [IsLocalization.AtPrime.inertiaDeg_map_eq_inertiaDeg p]
    · exact map_ne_bot_of_ne_bot hp
    exact IsPrincipalIdealRing.principal _
    -- case q ≠ p
  · let Mₛ := Algebra.algebraMapSubmonoid S q.primeCompl
    let Sₚ := Localization Mₛ
    obtain ⟨x, hx₁, hx₂⟩ : ∃ x ∈ p, x ∈ q.primeCompl :=
      SetLike.not_le_iff_exists.mp <|
        (Ring.DimensionLeOne.prime_le_prime_iff_eq hp).not.mpr <| ne_comm.mp (Ne.symm hq)
    have h₁ : Ideal.map (algebraMap R Rₚ) p = ⊤ :=
      eq_top_of_isUnit_mem _ (mem_map_of_mem _ hx₁) <|
        (IsLocalization.AtPrime.isUnit_to_map_iff _ _ _).mpr hx₂
    have h₂ : Ideal.map (algebraMap S Sₚ) P = ⊤ := by
      have : algebraMap R S x ∈ Mₛ := Algebra.mem_algebraMapSubmonoid_of_mem ⟨_, hx₂⟩
      refine eq_top_of_isUnit_mem _ ?_ <| IsLocalization.map_units _ ⟨_, this⟩
      rw [← IsScalarTower.algebraMap_apply]
      exact mem_map_of_mem _ (by simpa [← Ideal.mem_of_liesOver P p])
    rw [← spanNorm_eq, ← spanIntNorm_localization R (Sₘ := Sₚ) _ _
      (primeCompl_le_nonZeroDivisors q), spanNorm_eq, Ideal.map_pow, h₁, h₂, relNorm_top, top_pow]

theorem relNorm_eq_pow_of_isMaximal [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (P : Ideal S) [P.IsMaximal] (p : Ideal R) [p.IsMaximal] [hP₁ : P.LiesOver p] :
    relNorm R P = p ^ p.inertiaDeg P := by
  by_cases hp : p = ⊥
  · rw [hp] at hP₁
    rw [liesOver_iff, under_def, eq_comm] at hP₁



    sorry

  · sorry

#exit

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

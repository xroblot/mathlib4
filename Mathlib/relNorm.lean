import Mathlib

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

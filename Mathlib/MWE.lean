module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.NumberTheory.RamificationInertia.Basic

open Ideal

theorem ramificationIdx_algebra_tower' {R S T : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [Module.IsTorsionFree R S]
    [Module.IsTorsionFree S T] [Module.IsTorsionFree R T]
    [IsScalarTower R S T] [IsDedekindDomain S]
    [IsDedekindDomain T] {p : Ideal R} {P : Ideal S} {Q : Ideal T} [hpm : P.IsPrime]
    [hqm : Q.IsPrime] [Q.LiesOver P] [P.LiesOver p] (hp : p ≠ ⊥) :
    ramificationIdx (algebraMap R T) p Q =
      ramificationIdx (algebraMap R S) p P * ramificationIdx (algebraMap S T) P Q :=
  have hP : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
  ramificationIdx_algebra_tower (map_ne_bot_of_ne_bot hP) (map_ne_bot_of_ne_bot hp)
    <| map_le_iff_le_comap.mpr <| le_of_eq <| over_def Q P

@[expose] public section

theorem Ideal.ramificationIdx_eq_finrank_of_finrank_le {R : Type*} [CommRing R] (T : Type*)
    [CommRing T]
    [IsDedekindDomain T] [Algebra R T] (K : Type*) (L : Type*) [Field K] [Field L]
    [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] [Algebra T L] [IsFractionRing T L]
    [Algebra K L] [FiniteDimensional K L]
    [Algebra R L] [IsScalarTower R T L] [IsScalarTower R K L] [Module.Finite R T]
    [NoZeroSMulDivisors R T] {p : Ideal R} [p.IsMaximal] {Q : Ideal T} [hQ₁ : Q.IsPrime]
    [hQ₂ : Q.LiesOver p]
    (S F : Type*) [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Algebra S T] [NoZeroSMulDivisors R S] [Module.Finite R S]
    [NoZeroSMulDivisors S T] [Module.Finite S T] [IsScalarTower R S T]
    [Algebra S L] [Field F] [Algebra S F] [IsFractionRing S F]
    [Algebra K F] [Algebra F L] [FiniteDimensional F L]
    [Algebra R F]
    [IsScalarTower R K F]
    [IsScalarTower R S F]
    [IsScalarTower S T L] [IsScalarTower S F L] [IsScalarTower K F L]
    (P : Ideal S)
    [P.IsMaximal] [Q.LiesOver P] [P.LiesOver p]
    (h : Module.finrank K L ≤ ramificationIdx (algebraMap R T) p Q) :
    ramificationIdx (algebraMap R S) p P = Module.finrank K F := by
  by_cases hp : p = ⊥
  · rw [hp, ramificationIdx_bot] at h
    have : 0 < Module.finrank K L := Module.finrank_pos
    grind
  have hP : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
  suffices Module.finrank K F ≤ ramificationIdx (algebraMap R S) p P by
    exact le_antisymm (ramificationIdx_le_finrank _ _ _ _) this
  contrapose! h
  have := ramificationIdx_algebra_tower (p := p) (P := P) (Q := Q) ?_ ?_ ?_
  · rw [this]
    rw [← Module.finrank_mul_finrank K F L]
    refine Nat.mul_lt_mul_of_lt_of_le h ?_ ?_
    · apply ramificationIdx_le_finrank
    · exact Module.finrank_pos
  · exact map_ne_bot_of_ne_bot hP
  · exact map_ne_bot_of_ne_bot hp
  · rw [map_le_iff_le_comap]


    sorry

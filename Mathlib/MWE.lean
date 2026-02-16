import Mathlib.NumberTheory.RamificationInertia.Basic

theorem Ideal.inertiaDeg_le_inertiaDeg {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Module.Finite R T]
    (p : Ideal R) (P : Ideal S) (Q : Ideal T) [P.LiesOver p] [Q.LiesOver P] [p.IsPrime] :
    Ideal.inertiaDeg P Q ≤ Ideal.inertiaDeg p Q := by
  have : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  rw [inertiaDeg_algebraMap, inertiaDeg_algebraMap]
  have : IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ Q) := IsScalarTower.of_algebraMap_eq <| by
    rintro ⟨x⟩; exact congr_arg _ (IsScalarTower.algebraMap_apply R S T x)
  exact Module.finrank_top_le_finrank_of_isScalarTower _ _ _

theorem Ideal.ramificationIdx_le_ramificationIdx {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] (p : Ideal R) (P : Ideal S) (Q : Ideal T) (f : R →+* S) (g : S →+* T)
    (hp : p = Ideal.comap f P) (h : BddAbove {n | map (g.comp f) p ≤ Q ^ n}) :
    Ideal.ramificationIdx g P Q ≤ Ideal.ramificationIdx (g.comp f) p Q := by
  refine csSup_le_csSup' h fun n hn ↦ ?_
  rw [Set.mem_setOf_eq, ← map_map, map_le_iff_le_comap, map_le_iff_le_comap, hp]
  refine Ideal.comap_mono <| by rwa [← Ideal.map_le_iff_le_comap]

theorem Ideal.IsDedekindDomain.ramificationIdx_le_ramificationIdx {R S T : Type*} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.IsTorsionFree R T] [IsDomain R] [IsDedekindDomain T] (p : Ideal R) (P : Ideal S)
    (Q : Ideal T) [Q.LiesOver p] [P.LiesOver p] [Q.IsPrime] (hp : p ≠ ⊥) :
    Ideal.ramificationIdx (algebraMap S T) P Q ≤ Ideal.ramificationIdx (algebraMap R T) p Q := by
  rw [IsScalarTower.algebraMap_eq R S T]
  refine Ideal.ramificationIdx_le_ramificationIdx p P Q (algebraMap R S) (algebraMap S T) ?_ ?_
  · rwa [← under_def, ← liesOver_iff]
  · rw [← IsScalarTower.algebraMap_eq R S T]
    suffices ramificationIdx (algebraMap R T) p Q ≠ 0 by
      contrapose! this
      exact ramificationIdx_eq_zero (by rwa [not_bddAbove_iff] at this)
    exact ramificationIdx_ne_zero_of_liesOver _ hp

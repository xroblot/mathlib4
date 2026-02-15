import Mathlib.NumberTheory.RamificationInertia.Galois

theorem Algebra.isInvariant_of_equiv (A B B' G : Type*) [CommSemiring A] [Semiring B] [Algebra A B]
    [Semiring B'] [Algebra A B'] [Group G] [MulSemiringAction G B] [MulSemiringAction G B']
    [hA : Algebra.IsInvariant A B G] {F : Type*} [EquivLike F B B']
    [hf : MulActionHomClass F G B B']
    (f : F) (hf : ∀ a, f (algebraMap A B a) = algebraMap A B' a) :
    Algebra.IsInvariant A B' G := by
  refine ⟨fun b' hg ↦ ?_⟩
  have : Function.Surjective f := EquivLike.surjective f
  obtain ⟨b, rfl⟩ := this b'
  have := hA.isInvariant b ?_
  · obtain ⟨a, rfl⟩ := this
    refine ⟨a, ?_⟩
    rw [hf]
  · intro g
    specialize hg g
    rw [← map_smul] at hg
    have : Function.Injective f := by exact EquivLike.injective f
    apply this at hg
    exact hg

theorem IsGaloisGroup.of_equiv (G A B B' : Type*) [Group G] [CommSemiring A] [Semiring B]
    [Algebra A B] [MulSemiringAction G B] [Semiring B'] [Algebra A B'] [MulSemiringAction G B']
    [hG : IsGaloisGroup G A B] {F : Type*} [EquivLike F B B'] [MulActionHomClass F G B B']
    [AlgHomClass F A B B'] (f : F) :
    IsGaloisGroup G A B' := by
  refine { faithful := ?_, commutes := ?_, isInvariant := ?_ }
  · have := hG.faithful
    apply FaithfulSMul.of_injective (M' := G) (X := B) (F := F) f ?_
    exact EquivLike.injective f
  · have := hG.commutes
    refine Function.Injective.smulCommClass (f := (f : B ≃ B').symm) (M := G) (N := A) ?_ ?_ ?_
    · exact Equiv.injective _
    · sorry
    · sorry
  · have := hG.isInvariant
    apply Algebra.isInvariant_of_equiv A B B' G f
    exact fun a ↦ AlgHomClass.commutes f a



theorem Nat.eq_eq_of_mul_le_mul {a b c d : ℕ} (ha : a ≤ c) (hb : b ≤ d) (hc : 0 < c) (hd : 0 < d)
    (h : c * d ≤ a * b) : a = c ∧ b = d :=
  ⟨le_antisymm ha <| Nat.le_of_mul_le_mul_right (h.trans <| Nat.mul_le_mul_left a hb) hd,
    le_antisymm hb <| Nat.le_of_mul_le_mul_left (h.trans <| Nat.mul_le_mul_right b ha) hc⟩

theorem Ideal.inertiaDeg_le_inertiaDeg {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [Module.Finite R T]
    (p : Ideal R) (P : Ideal S) (Q : Ideal T) [P.LiesOver p] [Q.LiesOver P] [p.IsMaximal] :
    Ideal.inertiaDeg P Q ≤ Ideal.inertiaDeg p Q := by
  have : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  unfold Ideal.inertiaDeg
  rw [dif_pos (by rwa [← Ideal.under_def, eq_comm, ← Ideal.liesOver_iff]),
    dif_pos (by rwa [← Ideal.under_def, eq_comm, ← Ideal.liesOver_iff])]
  have : IsScalarTower (R ⧸ p) (S ⧸ P) (T ⧸ Q) := IsScalarTower.of_algebraMap_eq <| by
    rintro ⟨x⟩; exact congr_arg _ (IsScalarTower.algebraMap_apply R S T x)
  exact Module.finrank_top_le_finrank_of_isScalarTower _ _ _

theorem Ideal.ramificationIdx_le_ramificationIdx {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] (p : Ideal R) (P : Ideal S) (Q : Ideal T) (f : R →+* S) (g : S →+* T)
    (hp : p = Ideal.comap f P) (h : BddAbove {n | map (g.comp f) p ≤ Q ^ n}) :
    Ideal.ramificationIdx g P Q ≤ Ideal.ramificationIdx (g.comp f) p Q := by
  unfold Ideal.ramificationIdx
  refine csSup_le_csSup' h fun n hn ↦ ?_
  rw [Set.mem_setOf_eq, ← map_map, map_le_iff_le_comap, map_le_iff_le_comap, hp]
  apply Ideal.comap_mono
  rwa [← Ideal.map_le_iff_le_comap]

theorem Ideal.IsDedekindDomain.ramificationIdx_le_ramificationIdx {R S T : Type*} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Module.IsTorsionFree R T] [IsDomain R] [IsDedekindDomain T]
    (p : Ideal R) (P : Ideal S) (Q : Ideal T) [Q.LiesOver p] [P.LiesOver p] [Q.IsPrime]
    (hp : p ≠ ⊥) :
    Ideal.ramificationIdx (algebraMap S T) P Q ≤ Ideal.ramificationIdx (algebraMap R T) p Q := by
  rw [IsScalarTower.algebraMap_eq R S T]
  refine Ideal.ramificationIdx_le_ramificationIdx p P Q (algebraMap R S) (algebraMap S T) ?_ ?_
  · rwa [← under_def, ← liesOver_iff]
  · rw [← IsScalarTower.algebraMap_eq R S T]
    suffices ramificationIdx (algebraMap R T) p Q ≠ 0 by
      contrapose! this
      exact ramificationIdx_eq_zero (by rwa [not_bddAbove_iff] at this)
    exact ramificationIdx_ne_zero_of_liesOver _ hp

noncomputable section

open MulAction Pointwise Ideal

set_option linter.unusedSectionVars false

variable (A K L : Type*) {B : Type*} [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A K]
  [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [IsScalarTower A B L] [IsDomain A] [IsFractionRing A K] [IsFractionRing B L]

variable (G : Type*) [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [MulSemiringAction G B] [SMulDistribClass G B L] [IsIntegrallyClosed A] [Algebra.IsIntegral A B]
  [IsGaloisGroup G A B]

variable (p : Ideal A) (P : Ideal B) [P.LiesOver p]

/-- Def. -/
def decompField : IntermediateField K L := FixedPoints.intermediateField (stabilizer G P)

/-- Def. -/
abbrev decompRing : Subalgebra A (decompField K L G P) := integralClosure A (decompField K L G P)

local notation3 "LD" => decompField K L G P
local notation3 "𝓞D" => decompRing A K L G P

variable [IsIntegralClosure B A L]

instance : IsScalarTower A 𝓞D L :=
  IsScalarTower.of_algebraMap_eq' rfl

instance : Algebra 𝓞D B := (IsIntegralClosure.lift A (S := 𝓞D) B L).toRingHom.toAlgebra

/-- Def. -/
abbrev decompPrime : Ideal 𝓞D := comap (algebraMap (decompRing A K L G P) B) P

local notation3 "𝓟D" => decompPrime A K L G P

variable [FiniteDimensional K L] [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [p.IsMaximal] [P.IsMaximal] [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]

theorem rank_decompField_left (hp : p ≠ ⊥) :
    Module.finrank LD L = p.ramificationIdxIn B * p.inertiaDegIn B := by
  rw [← card_stabilizer_eq (G := G) p hp P]
  exact IsGaloisGroup.finrank_fixedPoints_eq_card_subgroup G K L (stabilizer G P)

theorem rank_decompField_right (hp : p ≠ ⊥) :
    Module.finrank K LD = (p.primesOver B).ncard := by
  refine mul_left_injective₀ (b := Module.finrank (decompField K L G P) L) ?_ ?_
  · exact Nat.pos_iff_ne_zero.mp <| Module.finrank_pos
  · dsimp only
    rw [Module.finrank_mul_finrank, rank_decompField_left A K L G p P hp,
      ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B G,
      IsGaloisGroup.card_eq_finrank G K L]

instance : IsFractionRing 𝓞D LD :=
  integralClosure.isFractionRing_of_finite_extension K _

variable [Algebra.IsSeparable K L]

instance : IsDedekindDomain 𝓞D :=
  integralClosure.isDedekindDomain A K LD

instance : Module.IsTorsionFree A LD :=
  Module.IsTorsionFree.trans_faithfulSMul A K LD

instance : IsScalarTower 𝓞D B L := by
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  change _ = algebraMap B L (IsIntegralClosure.lift A (S := 𝓞D) B L x)
  simp only [IsIntegralClosure.algebraMap_lift]

instance : SMulDistribClass (stabilizer G P) B L := ⟨by simp [subgroup_smul_def, smul_distrib_smul]⟩

instance : IsIntegralClosure B 𝓞D L :=
  IsIntegralClosure.tower_top (R := A)

instance : Algebra.IsIntegral 𝓞D B :=
  IsIntegralClosure.isIntegral_algebra 𝓞D L

instance : IsGaloisGroup (stabilizer G P) LD L :=
  IsGaloisGroup.subgroup G K L (stabilizer G P)

instance : IsGaloisGroup (stabilizer G P) 𝓞D B :=
  IsGaloisGroup.of_isFractionRing (stabilizer G P) _ B LD L

instance : Module.Finite A 𝓞D :=
  IsIntegralClosure.finite A K LD _

instance : Module.Finite 𝓞D B :=
  IsIntegralClosure.finite _ LD L _

instance : Module.IsTorsionFree 𝓞D B :=
  IsIntegralClosure.isTorsionFree _ L

theorem primesOver_decompPrime : primesOver 𝓟D B = {P} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨IsMaximal.isPrime' P, over_under P⟩, ?_⟩
  rintro Q ⟨_, _⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝓟D P Q (stabilizer G P)
  exact σ.prop

theorem decompPrime_ne_bot (hp : p ≠ ⊥) :
    decompPrime A K L G P ≠ ⊥ :=
  under_ne_bot (decompRing A K L G P) <| ne_bot_of_liesOver_of_ne_bot hp P

theorem decompPrime_ramficationIdxIn_mul_inertiaDegIn (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟D B * inertiaDegIn 𝓟D B = p.ramificationIdxIn B * p.inertiaDegIn B := by
  have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (decompPrime_ne_bot A K L G p P hp) B (stabilizer G P)
  rw [primesOver_decompPrime, Set.ncard_singleton, one_mul] at this
  rw [this, IsGaloisGroup.card_eq_finrank (stabilizer G P) LD L,
    rank_decompField_left A K L G p P hp]

theorem ramificationIdxIn_decompPrime (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B := by
  refine (Nat.eq_eq_of_mul_le_mul ?_ ?_ ?_ ?_
    (decompPrime_ramficationIdxIn_mul_inertiaDegIn A K L G p P hp).symm.le).1
  · rw [ramificationIdxIn_eq_ramificationIdx p P G,
      ramificationIdxIn_eq_ramificationIdx _ P (stabilizer G P)]
    exact IsDedekindDomain.ramificationIdx_le_ramificationIdx _ _ _ hp
  · rw [inertiaDegIn_eq_inertiaDeg p P G, inertiaDegIn_eq_inertiaDeg _ P (stabilizer G P)]
    exact inertiaDeg_le_inertiaDeg p 𝓟D P
  · exact Nat.pos_of_ne_zero <| ramificationIdxIn_ne_zero G hp
  · exact Nat.pos_of_ne_zero <| inertiaDegIn_ne_zero G

theorem inertiaDegIn_decompPrime (hp : p ≠ ⊥) :
    inertiaDegIn 𝓟D B = p.inertiaDegIn B := by
  refine (Nat.eq_eq_of_mul_le_mul ?_ ?_ ?_ ?_
    (decompPrime_ramficationIdxIn_mul_inertiaDegIn A K L G p P hp).symm.le).2
  · rw [ramificationIdxIn_eq_ramificationIdx p P G,
      ramificationIdxIn_eq_ramificationIdx _ P (stabilizer G P)]
    exact IsDedekindDomain.ramificationIdx_le_ramificationIdx _ _ _ hp
  · rw [inertiaDegIn_eq_inertiaDeg p P G, inertiaDegIn_eq_inertiaDeg _ P (stabilizer G P)]
    exact inertiaDeg_le_inertiaDeg p (decompPrime A K L G P) P
  · exact Nat.pos_of_ne_zero <| ramificationIdxIn_ne_zero G hp
  · exact Nat.pos_of_ne_zero <| inertiaDegIn_ne_zero G

theorem ramificationIdx_decompPrime (hp : p ≠ ⊥) :
    ramificationIdx (algebraMap A 𝓞D) p 𝓟D = 1 := by
  have := ramificationIdx_algebra_tower (p := p) (P := 𝓟D) (Q := P) ?_ ?_ map_comap_le
  · rwa [← ramificationIdxIn_eq_ramificationIdx 𝓟D P (stabilizer G P),
    ramificationIdxIn_decompPrime A K L G p P hp, ramificationIdxIn_eq_ramificationIdx p P G,
    right_eq_mul₀] at this
    exact IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp
  · exact map_ne_bot_of_ne_bot <| decompPrime_ne_bot A K L G p P hp
  · exact map_ne_bot_of_ne_bot hp

/-- Def. -/
def inertiaField : IntermediateField K L := FixedPoints.intermediateField (inertia G P)

/-- Def. -/
abbrev inertiaRing : Subalgebra A (inertiaField K L G P) := integralClosure A (inertiaField K L G P)

local notation3 "LI" => inertiaField K L G P
local notation3 "𝓞I" => inertiaRing A K L G P

instance : IsScalarTower A 𝓞I L := IsScalarTower.of_algebraMap_eq' rfl

instance : Algebra 𝓞I B :=
  (IsIntegralClosure.lift A (S := inertiaRing A K L G P) B L).toRingHom.toAlgebra

/-- Def. -/
abbrev inertiaPrime : Ideal 𝓞I :=
  comap (algebraMap (inertiaRing A K L G P) B) P

local notation3 "𝓟I" => inertiaPrime A K L G P

theorem rank_inertiaField_left (hp : p ≠ ⊥) :
    Module.finrank LI L = p.ramificationIdxIn B := by
  rw [← card_inertia_eq_ramificationIdxIn (G := G) p hp P]
  exact IsGaloisGroup.finrank_fixedPoints_eq_card_subgroup G K L (inertia G P)

theorem rank_inertiaField_right (hp : p ≠ ⊥) :
    Module.finrank K LI = (p.primesOver B).ncard * p.inertiaDegIn B := by
  refine mul_left_injective₀ (b := Module.finrank LI L) ?_ ?_
  · exact Nat.pos_iff_ne_zero.mp <| Module.finrank_pos
  · dsimp only
    rw [Module.finrank_mul_finrank, rank_inertiaField_left A K L G p P hp, mul_assoc,
      mul_comm (p.inertiaDegIn B), ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B G,
      IsGaloisGroup.card_eq_finrank G K L]

instance : IsFractionRing 𝓞I LI :=
  integralClosure.isFractionRing_of_finite_extension K _

instance : IsDedekindDomain 𝓞I :=
  integralClosure.isDedekindDomain A K LI

instance : IsScalarTower 𝓞I B L := by
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  change _ = algebraMap B L (IsIntegralClosure.lift A (S := 𝓞I) B L x)
  simp only [IsIntegralClosure.algebraMap_lift]

instance : SMulDistribClass (inertia G P) B L := ⟨by simp [subgroup_smul_def, smul_distrib_smul]⟩

instance : IsIntegralClosure B 𝓞I L :=
  IsIntegralClosure.tower_top (R := A)

instance : Algebra.IsIntegral 𝓞I B :=
  IsIntegralClosure.isIntegral_algebra 𝓞I L

instance : IsGaloisGroup (inertia G P) LI L :=
  IsGaloisGroup.subgroup G K L (inertia G P)

instance : IsGaloisGroup (inertia G P) 𝓞I B :=
  IsGaloisGroup.of_isFractionRing (inertia G P) _ B LI L

instance : Algebra LD LI :=
  haveI : decompField K L G P ≤ inertiaField K L G P :=
    IsGaloisGroup.fixedPoints_le_of_le _ _ _ _ _ (inertia_le_stabilizer P)
  (IntermediateField.inclusion this).toRingHom.toAlgebra

instance : IsScalarTower A 𝓞D LI :=
  IsScalarTower.of_algebraMap_eq' rfl

instance : IsIntegralClosure 𝓞I 𝓞D LI :=
  IsIntegralClosure.tower_top (R := A)

instance : Algebra 𝓞D 𝓞I :=
  (IsIntegralClosure.lift A _ LI).toRingHom.toAlgebra

instance : IsScalarTower 𝓞D LI L :=
  IsScalarTower.of_algebraMap_eq' rfl

instance : IsScalarTower A 𝓞D 𝓞I :=
  IsScalarTower.of_algHom (IsIntegralClosure.lift A 𝓞I LI)

instance : IsScalarTower 𝓞D 𝓞I L := by
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  change _ = algebraMap 𝓞I L (IsIntegralClosure.lift A (S := 𝓞D) _ _ x)
  rw [IsScalarTower.algebraMap_apply 𝓞I LI L]
  simp only [IsIntegralClosure.algebraMap_lift]
  rw [← IsScalarTower.algebraMap_apply]

instance : IsScalarTower 𝓞D 𝓞I B :=
  IsScalarTower.to₁₂₃ _ _ _ L

example (hp : p ≠ ⊥) : ramificationIdx (algebraMap A B) p P * inertiaDeg p P =
      ramificationIdx (algebraMap (inertiaRing A K L G P) B) (inertiaPrime A K L G P) P *
        inertiaDeg (decompPrime A K L G P) (inertiaPrime A K L G P) := by

  sorry

example (hp : p ≠ ⊥) :
    ramificationIdx (algebraMap 𝓞I B) 𝓟I P = ramificationIdx (algebraMap A B) p P := by
  have : ramificationIdx (algebraMap A B) p P * inertiaDeg p P =
      ramificationIdx (algebraMap (inertiaRing A K L G P) B) (inertiaPrime A K L G P) P *
        inertiaDeg (decompPrime A K L G P) (inertiaPrime A K L G P) := sorry
  refine (Nat.eq_eq_of_mul_le_mul ?_ ?_ ?_ ?_ this.le).1
  · exact IsDedekindDomain.ramificationIdx_le_ramificationIdx p (inertiaPrime A K L G P) P hp
  · have := inertiaDeg_le_inertiaDeg (R := decompRing A K L G P) (S := inertiaRing A K L G P)
      (T := B)
    sorry
  · sorry
  · sorry

example : (inertiaPrime A K L G P).inertiaDegIn B = 1 := by
  have := card_stabilizer_eq (G := G) p ?_ P
  · rw [ramificationIdxIn_eq_ramificationIdx (inertiaPrime A K L G P) P (P.inertia G)] at this

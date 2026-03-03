/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

public import Mathlib.ExtendTop

/-!

# Decomposition and Inertia fields

In this file, we develop Hilbert Theory on the splitting of prime ideals in a Galois extension.

Let `L/K` be a Galois extension of fields. Let `A` and `B` be subrings of `K` `L` respectively with
`A` integrally closed, `K` fraction field of `A`, `L` fraction field of `B` and `B` the integral
closure of `A` in `L`.

For `P` a prime ideal of `B`, the decomposition field `D` of `P` in `L/K` is the subfield of
elements of `L` fixed by the stabilizer of `P` in `Gal(L/K)`, and the inertia field `E` of `P`
in `L/K` is the subfield of elements of `L` fixed by the inertia group of `P` in `Gal(L/K)`.

-/

@[expose] public section

variable (A K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L] [CommRing A] [CommRing B]
  [Algebra A B] {p : Ideal A} (P : Ideal B) [P.LiesOver p]

open MulAction Pointwise Ideal

noncomputable section defs

variable (D : Type*) [Field D] [Algebra D L]

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of `B`. The decomposition
field of `P` in `L/K` is the subfield fixed the decomposition subgroup of `P`, that is the
stabilizer of `P` in `Gal(L/K)`.
-/
@[mk_iff]
class IsDecompositionField [MulSemiringAction Gal(L/K) B] extends
    IsGaloisGroup (stabilizer Gal(L/K) P) D L

variable (E : Type*) [Field E] [Algebra E L]

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of `B`. The inertia field
of `P` in `L/K` is the subfield fixed the inertia subgroup of `P` in `Gal(L/K)`.
-/
@[mk_iff]
class IsInertiaField [MulSemiringAction Gal(L/K) B] extends
    IsGaloisGroup (inertia Gal(L/K) P) E L

instance [IsGalois K L] [MulSemiringAction Gal(L/K) B] :
    IsDecompositionField K L P
      (FixedPoints.intermediateField (stabilizer Gal(L/K) P) : IntermediateField K L) where
  toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (stabilizer Gal(L/K) P)

instance [IsGalois K L] [MulSemiringAction Gal(L/K) B] :
    IsInertiaField K L P
      (FixedPoints.intermediateField (inertia Gal(L/K) P) : IntermediateField K L) where
  toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (inertia Gal(L/K) P)

end defs

section rank

attribute [local instance] Ideal.Quotient.field

variable [MulSemiringAction Gal(L/K) B] [FiniteDimensional K L] [IsGaloisGroup Gal(L/K) A B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B] [Module.IsTorsionFree A B]
  [Ring.HasFiniteQuotients A] [p.IsMaximal] [P.IsMaximal]

variable (D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D]

include K P in
theorem IsDecompositionField.rank_left (hp : p ≠ ⊥) :
    Module.finrank D L = p.ramificationIdxIn B * p.inertiaDegIn B := by
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L, card_stabilizer_eq p hp]

include P in
theorem IsDecompositionField.rank_right [Algebra K D] [IsScalarTower K D L] [IsGalois K L]
    (hp : p ≠ ⊥) :
    Module.finrank K D = (p.primesOver B).ncard := by
  have : FiniteDimensional D L := FiniteDimensional.right K D L
  refine mul_left_injective₀ (b := Module.finrank D L) ?_ ?_
  · exact Nat.pos_iff_ne_zero.mp <| Module.finrank_pos
  · dsimp only
    rw [Module.finrank_mul_finrank, rank_left A K L P D hp,
      ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B Gal(L/K),
      IsGaloisGroup.card_eq_finrank Gal(L/K) K L]

variable (E : Type*) [Field E] [Algebra E L] [IsInertiaField K L P E]

include K P in
theorem IsInertiaField.rank_left (hp : p ≠ ⊥) :
    Module.finrank E L = p.ramificationIdxIn B := by
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank (inertia Gal(L/K) P) E L,
    card_inertia_eq_ramificationIdxIn p hp]

include P in
theorem IsInertiaField.rank_right [Algebra K E] [IsScalarTower K E L] [IsGalois K L] (hp : p ≠ ⊥) :
    Module.finrank K E = (p.primesOver B).ncard * p.inertiaDegIn B := by
  have : FiniteDimensional E L := FiniteDimensional.right K E L
  refine mul_left_injective₀ (b := Module.finrank E L) ?_ ?_
  · exact Nat.pos_iff_ne_zero.mp <| Module.finrank_pos
  · dsimp only
    rw [Module.finrank_mul_finrank, rank_left A K L P E hp, mul_assoc, mul_comm (p.inertiaDegIn B),
      ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B Gal(L/K),
      IsGalois.card_aut_eq_finrank]

include P in
theorem IsInertiaField.rank_decompositionField [Algebra K D] [Algebra K E] [Algebra D E]
    [IsScalarTower K D E] [IsScalarTower K E L] [IsScalarTower K D L] [IsGalois K L]
    (hp : p ≠ ⊥) :
    Module.finrank D E = p.inertiaDegIn B := by
  have := Module.finrank_mul_finrank K D E
  rwa [IsInertiaField.rank_right A K L P E hp, IsDecompositionField.rank_right A K L P D hp,
    mul_right_inj'] at this
  exact primesOver_ncard_ne_zero p B

end rank

section splitting

variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L] [Algebra B L]
  [IsScalarTower A B L] [IsFractionRing B L] [MulSemiringAction Gal(L/K) B]
  [SMulDistribClass Gal(L/K) B L]

namespace IsDecompositionField

variable (D 𝓞D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D] [CommRing 𝓞D]
  [Algebra 𝓞D D] [IsFractionRing 𝓞D D] [Algebra 𝓞D B] [Algebra 𝓞D L] [IsScalarTower 𝓞D D L]
  [IsScalarTower 𝓞D B L] (𝓟D : Ideal 𝓞D) [hD : P.LiesOver 𝓟D]

include K L D in
theorem primesOver_eq_singleton [hP : P.IsPrime] [Finite (stabilizer Gal(L/K) P)]
    [IsIntegrallyClosed 𝓞D] [Algebra.IsIntegral 𝓞D B] :
    primesOver 𝓟D B = {P} := by
  have := IsGaloisGroup.of_isFractionRing (stabilizer Gal(L/K) P) 𝓞D B D L
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hP, hD⟩, ?_⟩
  rintro Q ⟨_, _⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝓟D P Q (stabilizer Gal(L/K) P)
  exact σ.prop

variable [FiniteDimensional K L] [IsGalois K L] [IsDedekindDomain A] [IsDedekindDomain B]
  [Ring.HasFiniteQuotients A] [Module.Finite A B] [Module.IsTorsionFree A B] [Algebra A 𝓞D]
  [Module.Finite A 𝓞D] [IsScalarTower A 𝓞D B] [IsDedekindDomain 𝓞D] [𝓟D.IsMaximal]
  [P.IsMaximal] [p.IsMaximal]

include K L P D in
private theorem ramficationIdxIn_eq_inertiaDegIn_eq (hp : p ≠ ⊥) (hP : 𝓟D ≠ ⊥)
    (h₀ : 𝓟D.ramificationIdxIn B ≤ p.ramificationIdxIn B)
    (h₁ : 𝓟D.inertiaDegIn B ≤ p.inertiaDegIn B) :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B ∧ inertiaDegIn 𝓟D B = p.inertiaDegIn B := by
  have : Module.IsTorsionFree 𝓞D B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have : Module.Finite 𝓞D B := Module.Finite.right A 𝓞D B
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B := .of_isFractionRing _ _ _ D L
  have : p.ramificationIdxIn B * p.inertiaDegIn B ≤ 𝓟D.ramificationIdxIn B * 𝓟D.inertiaDegIn B := by
    have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hP B (stabilizer Gal(L/K) P)
    rw [primesOver_eq_singleton K L P D 𝓞D, Set.ncard_singleton, one_mul] at this
    rw [this, IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L,
      IsDecompositionField.rank_left A K L P D hp]
  refine ⟨le_antisymm h₀ ?_, le_antisymm h₁ ?_⟩
  · refine Nat.le_of_mul_le_mul_right (this.trans (Nat.mul_le_mul_left _ h₁)) ?_
    exact Nat.pos_iff_ne_zero.mpr <| inertiaDegIn_ne_zero Gal(L/K)
  · refine Nat.le_of_mul_le_mul_left (this.trans (Nat.mul_le_mul_right _ h₀)) ?_
    exact Nat.pos_of_ne_zero <| ramificationIdxIn_ne_zero Gal(L/K) hp

variable [𝓟D.LiesOver p]

include K L D P in
theorem ramificationIdxIn_eq (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B := by
  have : Module.Finite 𝓞D B := Module.Finite.right A 𝓞D B
  have : Module.IsTorsionFree 𝓞D B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have : Module.IsTorsionFree A 𝓞D := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B := .of_isFractionRing _ _ _ D L
  refine (ramficationIdxIn_eq_inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp ?_ ?_ ?_).1
  · exact Ideal.ne_bot_of_liesOver_of_ne_bot hp 𝓟D
  · rw [ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
      ramificationIdxIn_eq_ramificationIdx _ P (stabilizer Gal(L/K) P)]
    exact IsDedekindDomain.ramificationIdx_le_ramificationIdx _ _ _ hp
  · rw [inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
      inertiaDegIn_eq_inertiaDeg _ P (stabilizer Gal(L/K) P)]
    exact inertiaDeg_le_inertiaDeg p 𝓟D P

include K L D P in
theorem inertiaDegIn_eq (hp : p ≠ ⊥) :
    inertiaDegIn 𝓟D B = p.inertiaDegIn B := by
  have : Module.Finite 𝓞D B := Module.Finite.right A 𝓞D B
  have : Module.IsTorsionFree 𝓞D B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have : Module.IsTorsionFree A 𝓞D := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B := .of_isFractionRing _ _ _ D L
  refine (ramficationIdxIn_eq_inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp ?_ ?_ ?_).2
  · exact Ideal.ne_bot_of_liesOver_of_ne_bot hp 𝓟D
  · rw [ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
      ramificationIdxIn_eq_ramificationIdx _ P (stabilizer Gal(L/K) P)]
    exact IsDedekindDomain.ramificationIdx_le_ramificationIdx _ _ _ hp
  · rw [inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
      inertiaDegIn_eq_inertiaDeg _ P (stabilizer Gal(L/K) P)]
    exact inertiaDeg_le_inertiaDeg p 𝓟D P

include K L D P in
theorem ramificationIdx_eq (hp : p ≠ ⊥) :
    ramificationIdx (algebraMap A 𝓞D) p 𝓟D = 1 := by
  have : Module.Finite 𝓞D B := Module.Finite.right A 𝓞D B
  have : Module.IsTorsionFree 𝓞D B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have : Module.IsTorsionFree A 𝓞D := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B := .of_isFractionRing _ _ _ D L
  have := ramificationIdx_algebra_tower (p := p) (P := 𝓟D) (Q := P) ?_ ?_ ?_
  · rwa [← ramificationIdxIn_eq_ramificationIdx 𝓟D P (stabilizer Gal(L/K) P),
      ramificationIdxIn_eq A K L P D 𝓞D 𝓟D hp, ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
      right_eq_mul₀] at this
    exact IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp
  · exact map_ne_bot_of_ne_bot <| Ideal.ne_bot_of_liesOver_of_ne_bot hp 𝓟D
  · exact map_ne_bot_of_ne_bot hp
  · exact map_le_iff_le_comap.mpr <| le_of_eq <| (liesOver_iff P 𝓟D).mp inferInstance

include K L D P in
theorem inertiaDeg_eq (hp : p ≠ ⊥) :
    inertiaDeg p 𝓟D = 1 := by
  have : Module.Finite 𝓞D B := Module.Finite.right A 𝓞D B
  have : Module.IsTorsionFree 𝓞D B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have : Module.IsTorsionFree A 𝓞D := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B := .of_isFractionRing _ _ _ D L
  have := inertiaDeg_algebra_tower p 𝓟D P
  rwa [← inertiaDegIn_eq_inertiaDeg p P Gal(L/K), ← inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp,
    ← inertiaDegIn_eq_inertiaDeg 𝓟D P (stabilizer Gal(L/K) P), right_eq_mul₀] at this
  exact inertiaDegIn_ne_zero (stabilizer Gal(L/K) P)

end IsDecompositionField

namespace IsInertiaField

attribute [local instance] Ideal.Quotient.field

variable (E 𝓞E : Type*) [Field E] [Algebra E L] [IsInertiaField K L P E] [CommRing 𝓞E]
  [Algebra 𝓞E E] [IsFractionRing 𝓞E E] [Algebra 𝓞E B] [Algebra 𝓞E L] [IsScalarTower 𝓞E E L]
  [IsScalarTower 𝓞E B L] (𝓟E : Ideal 𝓞E) [P.LiesOver 𝓟E]

include L K E in
theorem primesOver_eq_singleton [IsIntegrallyClosed 𝓞E] [Algebra.IsIntegral 𝓞E B] [P.IsPrime]
    [Finite (inertia Gal(L/K) P)] :
    primesOver 𝓟E B = {P} := by
  have : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  rintro Q ⟨_, _⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝓟E P Q (inertia Gal(L/K) P)
  exact inertia_le_stabilizer _ σ.prop

include K L P E in
theorem inertiaDegIn_eq [Ring.HasFiniteQuotients B] [IsIntegrallyClosed 𝓞E]
    [Algebra.IsIntegral 𝓞E B] [P.IsMaximal] [𝓟E.IsMaximal] [Finite (inertia Gal(L/K) P)]
    (hP : P ≠ ⊥) :
    inertiaDegIn 𝓟E B = 1 := by
  have : Finite (B ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
  have : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  rw [inertiaDegIn_eq_inertiaDeg 𝓟E P (inertia Gal(L/K) P), inertiaDeg_algebraMap,
    ← IsGalois.card_aut_eq_finrank,
    ← Nat.card_congr (Quotient.stabilizerQuotientInertiaEquiv (inertia Gal(L/K) P) 𝓟E P).toEquiv]
  simp

variable [FiniteDimensional K L] [IsGalois K L] [Algebra.IsIntegral A B] [Algebra.IsIntegral 𝓞E B]

include K L E P in
theorem inertiaDeg_eq [IsIntegrallyClosed A] [Ring.HasFiniteQuotients B] [IsIntegrallyClosed 𝓞E]
    [Algebra A 𝓞E] [IsScalarTower A 𝓞E B] [𝓟E.LiesOver p] [P.IsMaximal] [𝓟E.IsMaximal]
    [p.IsMaximal] (hP : P ≠ ⊥) :
    inertiaDeg p 𝓟E = p.inertiaDegIn B := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  have := inertiaDeg_algebra_tower p 𝓟E P
  rwa [← inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
    ← inertiaDegIn_eq_inertiaDeg 𝓟E P (inertia Gal(L/K) P), inertiaDegIn_eq K L P E 𝓞E _ hP,
    mul_one, eq_comm] at this

variable [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]
  [IsDedekindDomain 𝓞E] [Module.Finite 𝓞E B] [Module.IsTorsionFree 𝓞E B]

include L K P E in
theorem ramificationIdxIn_eq [Ring.HasFiniteQuotients A] [Ring.HasFiniteQuotients B] [p.IsMaximal]
    [P.IsMaximal] [𝓟E.IsMaximal] (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟E B = p.ramificationIdxIn B := by
  have hP : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  have : 𝓟E ≠ ⊥ := by
    rw [over_def P 𝓟E]
    exact under_ne_bot 𝓞E <| ne_bot_of_liesOver_of_ne_bot hp _
  have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn this B (inertia Gal(L/K) P)
  rwa [primesOver_eq_singleton K L P E 𝓞E, Set.ncard_singleton, one_mul,
    inertiaDegIn_eq K L P E _ _ hP, mul_one, card_inertia_eq_ramificationIdxIn p hp] at this

variable [Algebra A 𝓞E] [Module.IsTorsionFree A 𝓞E] [IsScalarTower A 𝓞E B] [𝓟E.LiesOver p]

include K L E P in
theorem ramificationIdx_eq [Ring.HasFiniteQuotients A] [Ring.HasFiniteQuotients B] [𝓟E.IsMaximal]
    [P.IsMaximal] [p.IsMaximal] (hp : p ≠ ⊥) :
    ramificationIdx (algebraMap A 𝓞E) p 𝓟E = 1 := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  have := ramificationIdx_algebra_tower (p := p) (P := 𝓟E) (Q := P) ?_ ?_ ?_
  · rwa [← ramificationIdxIn_eq_ramificationIdx 𝓟E P (inertia Gal(L/K) P),
      ramificationIdxIn_eq A K L P E 𝓞E 𝓟E hp, ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
      right_eq_mul₀] at this
    exact IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp
  · exact map_ne_bot_of_ne_bot <| Ideal.ne_bot_of_liesOver_of_ne_bot hp 𝓟E
  · exact map_ne_bot_of_ne_bot hp
  · exact map_le_iff_le_comap.mpr <| le_of_eq <| (liesOver_iff P 𝓟E).mp inferInstance

end IsInertiaField

end splitting

namespace IntermediateField

open IntermediateField

variable [MulSemiringAction Gal(L/K) B] [FiniteDimensional K L] [IsGalois K L]
  {F : IntermediateField K L}

theorem isDecompositionField_iff_fixingSubgroup :
    IsDecompositionField K L P F ↔ F.fixingSubgroup = stabilizer Gal(L/K) P := by
  rw [isDecompositionField_iff, IsGaloisGroup.subgroup_iff, ← IntermediateField.fixedField,
    IsGalois.fixedField_eq_iff_fixingSubgroup_eq]

theorem isInertiaField_iff_fixingSubgroup :
    IsInertiaField K L P F ↔ F.fixingSubgroup = inertia Gal(L/K) P := by
  rw [isInertiaField_iff, IsGaloisGroup.subgroup_iff, ← IntermediateField.fixedField,
    IsGalois.fixedField_eq_iff_fixingSubgroup_eq]

variable (D E : IntermediateField K L) (𝓞D 𝓞E : Type*) [hD : IsDecompositionField K L P D]
  [IsInertiaField K L P E] [Algebra B L] [hSD : SMulDistribClass Gal(L/K) B L]

variable (F)

/--
Let `D` be the decomposition field of `P` in `L/K` and let `F` be a subextension of `L/K`.
Then, the decomposition field of `P` in `L/F` is the compositum `DF`.
-/
instance isDecompositionField_sup [FaithfulSMul B L] [MulSemiringAction Gal(L/F) B]
    [SMulDistribClass Gal(L/F) B L] :
    IsDecompositionField F L P (D ⊔ F : IntermediateField K L) := by
  let H : Subgroup Gal(L/K) := stabilizer Gal(L/K) P ⊓ F.fixingSubgroup
  have : IsGaloisGroup H ↥(D ⊔ F) L := by
    rw [IsGaloisGroup.subgroup_iff, ← fixedField, IsGalois.fixedField_eq_iff_fixingSubgroup_eq,
      fixingSubgroup_sup, (isDecompositionField_iff_fixingSubgroup K L P).mp inferInstance]
  let e : stabilizer Gal(L/F) P ≃* H := by
    refine (MulEquiv.trans ?_ ((stabilizer F.fixingSubgroup P).equivMapOfInjective _
      F.fixingSubgroup.subtype_injective)).trans <| MulEquiv.subgroupCongr <| by ext; simp [H]
    refine stabilizerEquiv P F.fixingSubgroupEquiv.symm fun σ x ↦ ?_
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul', fixingSubgroupEquiv_symm_apply_apply]
  exact (isDecompositionField_iff _ _ P _).mpr <| IsGaloisGroup.of_mulEquiv e fun g x ↦ rfl

/--
Let `E` be the inertia field of `P` in `L/K` and let `F` be a subextension of `L/K`.
Then, the inertia field of `P` in `L/F` is the compositum `EF`.
-/
instance isInertiaField_sup [FaithfulSMul B L] [MulSemiringAction Gal(L/F) B]
    [SMulDistribClass Gal(L/F) B L] :
    IsInertiaField F L P (E ⊔ F : IntermediateField K L) := by
  let H : Subgroup Gal(L/K) := inertia Gal(L/K) P ⊓ F.fixingSubgroup
  have : IsGaloisGroup H ↥(E ⊔ F) L := by
    rw [IsGaloisGroup.subgroup_iff, ← fixedField, IsGalois.fixedField_eq_iff_fixingSubgroup_eq,
      fixingSubgroup_sup, (isInertiaField_iff_fixingSubgroup K L P).mp inferInstance]
  let e : inertia Gal(L/F) P ≃* H := by
    refine (MulEquiv.trans ?_ ((inertia F.fixingSubgroup P).equivMapOfInjective _
      F.fixingSubgroup.subtype_injective)).trans <| MulEquiv.subgroupCongr <| by ext; simp [H]
    refine inertiaEquiv P F.fixingSubgroupEquiv.symm fun _ _ ↦ ?_
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul', fixingSubgroupEquiv_symm_apply_apply]
  exact (isInertiaField_iff _ _ P _).mpr <| IsGaloisGroup.of_mulEquiv e fun g x ↦ rfl

variable [IsFractionRing B L] (𝓞F : Type*) [CommRing 𝓞F] [IsIntegrallyClosed 𝓞F] [Algebra 𝓞F F]
  [IsFractionRing 𝓞F F] [Algebra 𝓞F B] [Algebra.IsIntegral 𝓞F B] [Algebra 𝓞F L]
  [IsScalarTower 𝓞F F L] [IsScalarTower 𝓞F B L] (𝓟F : Ideal 𝓞F) [P.LiesOver 𝓟F]

/--
Let `D` be the decomposition field of `P` in `L/K` and let `F` be a subextension of `L/K`.
Then, `D` is a subfield of `F` iff `P` is the only prime ideal above the prime `𝓟F` of `F`
below `P`.
-/
theorem isDecompositionField_le_iff [P.IsPrime] :
    D ≤ F ↔ primesOver 𝓟F B = {P} := by
  have : IsGaloisGroup F.fixingSubgroup 𝓞F B := by
      have : IsGaloisGroup F.fixingSubgroup F L := IsGaloisGroup.intermediateField _ _ _ _
      exact IsGaloisGroup.of_isFractionRing _ 𝓞F B F L
  have : P ∈ 𝓟F.primesOver B := ⟨inferInstance, inferInstance⟩
  simp only [← IsGalois.intermediateFieldEquivSubgroup.le_iff_le,
    IsGalois.intermediateFieldEquivSubgroup_apply, OrderDual.toDual_le_toDual,
    (isDecompositionField_iff_fixingSubgroup K L P).mp hD, Set.eq_singleton_iff_unique_mem,
    SetLike.le_def, this, true_and]
  refine ⟨fun h Q ⟨hQ₁, hQ₂⟩ ↦ ?_, fun h σ hσ ↦ h (σ • P) ⟨IsPrime.smul σ, ?_⟩⟩
  · obtain ⟨σ, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup 𝓟F P Q F.fixingSubgroup
    exact h σ.prop
  · exact Ideal.LiesOver.smul (⟨σ, hσ⟩ : F.fixingSubgroup)

variable [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain 𝓞F] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra A 𝓞F] [IsIntegralClosure B 𝓞F L] [IsScalarTower A 𝓞F B]
  [FaithfulSMul 𝓞F B] [Ring.HasFiniteQuotients 𝓞F]

include A in
/--
Let `E` be the inertia field of `P` in `L/K` and let `F` be a subextension of `L/K`.
Then, `E` is a subfield of `F` iff `𝓟F` is totally ramified in `L` where `𝓟F` is the
prime of `F` below `P`.
-/
theorem isInertiaField_le_iff [P.IsMaximal] [𝓟F.IsMaximal] (hp : p ≠ ⊥) :
    E ≤ F ↔ ramificationIdx (algebraMap 𝓞F B) 𝓟F P = Module.finrank F L := by
  let := IsIntegralClosure.MulSemiringAction 𝓞F F L B
  have : IsGaloisGroup Gal(L/F) 𝓞F B := .of_isFractionRing _ _ _ F L
  let : Algebra F ↥(E ⊔ F) := (inclusion le_sup_right).toAlgebra
  have : IsScalarTower F ↥(E ⊔ F) L := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite 𝓞F B := Module.Finite.right A 𝓞F B
  have : Module.IsTorsionFree A 𝓞F := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have : 𝓟F.LiesOver p := LiesOver.tower_bot P 𝓟F p
  have hPF : 𝓟F ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
  rw [← sup_eq_right, eq_comm, eq_of_le_iff_finrank_eq' le_sup_right,
    IsInertiaField.rank_left 𝓞F F L P ↥(E ⊔ F) hPF,
    ramificationIdxIn_eq_ramificationIdx 𝓟F P Gal(L/F), eq_comm]

variable [Ring.HasFiniteQuotients A] [Algebra A K] [IsFractionRing A K] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]

include P in
/--
Let `D` be the decomposition field of `P` in `L/K` and let `F` be a subextension of `L/K`.
Then, `F` is a subfield of `D` iff `p` is totally split in `F`.
-/
theorem le_isDecompositionField_iff [p.IsMaximal] [P.IsMaximal] [𝓟F.IsMaximal] (hp : p ≠ ⊥) :
    F ≤ D ↔ ramificationIdx (algebraMap A 𝓞F) p 𝓟F = 1 ∧ inertiaDeg p 𝓟F = 1 := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  let := IsIntegralClosure.MulSemiringAction 𝓞F F L B
  have : IsGaloisGroup Gal(L/F) 𝓞F B := .of_isFractionRing _ _ _ F L
  let : Algebra F ↥(D ⊔ F) := (inclusion le_sup_right).toAlgebra
  have : IsScalarTower F ↥(D ⊔ F) L := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite 𝓞F B := Module.Finite.right A 𝓞F B
  have : Module.IsTorsionFree A 𝓞F := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have : 𝓟F.LiesOver p := LiesOver.tower_bot P 𝓟F p
  have hPF : 𝓟F ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
  rw [← sup_eq_right, sup_comm, eq_comm, eq_of_le_iff_finrank_eq' le_sup_left,
    IsDecompositionField.rank_left A K L P D hp, IsDecompositionField.rank_left 𝓞F F L P _ hPF,
    ramificationIdxIn_eq_ramificationIdx p P Gal(L/K), inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
    ramificationIdxIn_eq_ramificationIdx 𝓟F P Gal(L/F), inertiaDegIn_eq_inertiaDeg 𝓟F P Gal(L/F),
    ramificationIdx_algebra_tower' p 𝓟F P, inertiaDeg_algebra_tower p 𝓟F P, mul_rotate, mul_assoc,
    mul_right_inj' (IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hPF), mul_rotate,
    mul_assoc, mul_eq_left₀ (inertiaDeg_ne_zero 𝓟F P), mul_eq_one]

include P in
/--
Let `E` be the inertia field of `P` in `L/K` and let `F` be a subextension of `L/K`.
Then, `F` is a subfield of `E` iff `p` is unramified in `F`.
-/
theorem le_isInertiaField_iff [P.IsMaximal] [𝓟F.IsMaximal] [p.IsMaximal] (hp : p ≠ ⊥) :
    F ≤ E ↔ ramificationIdx (algebraMap A 𝓞F) p 𝓟F = 1 := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  let := IsIntegralClosure.MulSemiringAction 𝓞F F L B
  have : IsGaloisGroup Gal(L/F) 𝓞F B := .of_isFractionRing _ _ _ F L
  have : Module.Finite 𝓞F B := Module.Finite.right A 𝓞F B
  have : Module.IsTorsionFree A 𝓞F := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have : 𝓟F.LiesOver p := LiesOver.tower_bot P 𝓟F p
  have hPF : 𝓟F ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
  rw [← sup_eq_right, sup_comm, eq_comm, eq_of_le_iff_finrank_eq' le_sup_left,
    IsInertiaField.rank_left A K L P E hp, IsInertiaField.rank_left 𝓞F F L P _ hPF,
    ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
    ramificationIdxIn_eq_ramificationIdx 𝓟F P Gal(L/F), ramificationIdx_algebra_tower' p 𝓟F P,
    mul_eq_right₀ (IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hPF)]

end IntermediateField

section applications

open IntermediateField

variable [FiniteDimensional K L]
  {A} [Ring.HasFiniteQuotients A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]
  (F₁ F₂ : IntermediateField K L) {B₁ B₂ C : Type*} [CommRing B₁] [CommRing B₂] [CommRing C]
  [IsDedekindDomain C] [Algebra C L] [IsFractionRing C L]
  [Algebra A C] [Algebra A L] [Module.Finite A C] [Module.IsTorsionFree A C] [IsScalarTower A K L]
  [IsScalarTower A C L]
  [Ring.HasFiniteQuotients B] [IsDedekindDomain B] [Algebra B ↥(F₁ ⊔ F₂)]
  [IsFractionRing B ↥(F₁ ⊔ F₂)]
  [Ring.HasFiniteQuotients B₁] [IsDedekindDomain B₁] [Algebra B₁ F₁] [IsFractionRing B₁ F₁]
  [Ring.HasFiniteQuotients B₂] [IsDedekindDomain B₂] [Algebra B₂ F₂] [IsFractionRing B₂ F₂]
  [Algebra B L] [Algebra B C] [IsScalarTower A B C] [IsScalarTower B ↥(F₁ ⊔ F₂) L]
  [IsScalarTower B C L] [Module.IsTorsionFree B C]
  [Algebra A B₁] [Algebra B₁ L] [Algebra B₁ C] [IsScalarTower A B₁ C] [IsScalarTower B₁ F₁ L]
  [IsScalarTower B₁ C L]
  [Module.IsTorsionFree B₁ C]
  [Algebra A B₂] [Algebra B₂ L] [Algebra B₂ C] [IsScalarTower A B₂ C] [IsScalarTower B₂ F₂ L]
  [IsScalarTower B₂ C L]
  [Module.IsTorsionFree B₂ C]
  {p : Ideal A} {P₁ : Ideal B₁} {P₂ : Ideal B₂} (P : Ideal B) (Q : Ideal C)
  [p.IsMaximal] [P₁.IsMaximal] [P₂.IsMaximal] [P.IsMaximal] [Q.IsMaximal]
  [Q.LiesOver p] [Q.LiesOver P₁] [Q.LiesOver P₂] [Q.LiesOver P]

include F₁ F₂ C Q in
theorem Ideal.ramificationIdx_sup_eq_one_of_isGalois [IsGalois K L] [MulSemiringAction Gal(L/K) C]
    [SMulDistribClass Gal(L/K) C L]
    (h₁ : ramificationIdx (algebraMap A B₁) p P₁ = 1)
    (h₂ : ramificationIdx (algebraMap A B₂) p P₂ = 1) (hp : p ≠ ⊥) :
    ramificationIdx (algebraMap A B) p P = 1 := by
  have : Module.Finite B₁ C := Module.Finite.right A B₁ C
  have : Module.Finite B₂ C := Module.Finite.right A B₂ C
  have : Module.Finite B C := Module.Finite.right A B C
  let E : IntermediateField K L := FixedPoints.intermediateField (inertia Gal(L/K) Q)
  rw [← IntermediateField.le_isInertiaField_iff _ K _ (E := E) (B := C) (p := p)
    (P := Q) (F := F₁) _ _ hp] at h₁
  rw [← IntermediateField.le_isInertiaField_iff _ K _ (E := E) (B := C)  (p := p)
    (P := Q) (F := F₂) _ _ hp] at h₂
  have := sup_le h₁ h₂
  rwa [IntermediateField.le_isInertiaField_iff _ K _ (E := E) (B := C)  (p := p)
    (P := Q) (𝓟F := P) (F := F₁ ⊔ F₂) _ hp] at this

set_option maxHeartbeats 500000 in
-- This result needs some help to compile
include F₁ F₂ C Q in
theorem Ideal.ramificationIdx_sup_eq_one [PerfectField K] [PerfectField L]
    [IsScalarTower A B ↥(F₁ ⊔ F₂)]
    [Ring.HasFiniteQuotients C] (h₁ : ramificationIdx (algebraMap A B₁) p P₁ = 1)
    (h₂ : ramificationIdx (algebraMap A B₂) p P₂ = 1) (hp : p ≠ ⊥) :
    ramificationIdx (algebraMap A B) p P = 1 := by
  let F : IntermediateField K L := F₁ ⊔ F₂
  let N := IntermediateField.normalClosure K L (AlgebraicClosure L)
  let : Algebra L N := normalClosure.algebra K L (AlgebraicClosure L)
  algebraize [(algebraMap L N).comp (algebraMap C L)]
  have : FiniteDimensional L N := Module.Finite.right K L N
  let C₀ := integralClosure C N
  have : Module.Finite C C₀ := IsIntegralClosure.finite C L N _
  have : FaithfulSMul C N := (faithfulSMul_iff_algebraMap_injective C N).mpr <|
      (FaithfulSMul.algebraMap_injective L N).comp (FaithfulSMul.algebraMap_injective C L)
  have : IsDedekindDomain C₀ := integralClosure.isDedekindDomain C L N
  have : IsFractionRing C₀ N := integralClosure.isFractionRing_of_finite_extension L N
  have : FaithfulSMul C C₀ := Module.IsTorsionFree.to_faithfulSMul
  algebraize [(algebraMap C C₀).comp (algebraMap A C)]
  algebraize [(algebraMap C C₀).comp (algebraMap B C)]
  algebraize [(algebraMap C C₀).comp (algebraMap B₁ C)]
  algebraize [(algebraMap C C₀).comp (algebraMap B₂ C)]
  algebraize [(algebraMap F N).comp (algebraMap B F)]
  algebraize [(algebraMap F₁ N).comp (algebraMap B₁ F₁)]
  algebraize [(algebraMap F₂ N).comp (algebraMap B₂ F₂)]
  have : Module.IsTorsionFree A C₀ := Module.IsTorsionFree.trans_faithfulSMul _ C C₀
  have : IsScalarTower A L N := IsScalarTower.to₁₃₄ A K L N
  have : IsScalarTower A C N := IsScalarTower.to₁₂₄ A C L N
  have : IsScalarTower A C₀ N := IsScalarTower.to₁₃₄ A C C₀ N
  have : IsScalarTower A F N := IsScalarTower.to₁₃₄ A K F N
  have : IsScalarTower A B N := IsScalarTower.to₁₂₄ A B F N
  have : Module.Finite A C₀ := Module.Finite.trans C C₀
  let : MulSemiringAction Gal(N/K) C₀ := IsIntegralClosure.MulSemiringAction A K N C₀
  let F' := (F₁.extendTop N) ⊔ (F₂.extendTop N)
  let e : (F.extendTop N) ≃ₐ[K] F' := equivOfEq <| F₁.map_sup F₂ (Algebra.algHom K L N)
  algebraize [e.toRingHom.comp (algebraMap B (F.extendTop N))]
  have : IsFractionRing B F' :=
    .of_algEquiv B (F.extendTop N) _ <| (e.restrictScalars A).extendScalars B
  have : IsScalarTower B F' N := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B L N := IsScalarTower.to₁₃₄ B F L N
  have : IsScalarTower A C N := IsScalarTower.to₁₂₄ A C L N
  have : IsScalarTower A B C₀ := IsScalarTower.to₁₂₄ A B C C₀
  have : IsScalarTower B C N := IsScalarTower.to₁₂₄ B C L N
  have : IsScalarTower B C₀ N := IsScalarTower.to₁₃₄ B C C₀ N
  have : IsScalarTower B₁ L N := IsScalarTower.to₁₃₄ B₁ F₁ L N
  have : IsScalarTower B₁ C N := IsScalarTower.to₁₂₄ B₁ C L N
  have : IsScalarTower B₁ C₀ N := IsScalarTower.to₁₃₄ B₁ C C₀ N
  have : IsScalarTower B₂ L N := IsScalarTower.to₁₃₄ B₂ F₂ L N
  have : IsScalarTower B₂ C N := IsScalarTower.to₁₂₄ B₂ C L N
  have : IsScalarTower B₂ C₀ N := IsScalarTower.to₁₃₄ B₂ C C₀ N
  have : IsScalarTower A B C₀ := IsScalarTower.to₁₂₄ A B C C₀
  have : IsScalarTower A B₁ C₀ := IsScalarTower.to₁₂₄ A B₁ C C₀
  have : IsScalarTower A B₂ C₀ := IsScalarTower.to₁₂₄ A B₂ C C₀
  have : Module.IsTorsionFree B C₀ := Module.IsTorsionFree.trans_faithfulSMul _ C C₀
  have : Module.IsTorsionFree B₁ C₀ := Module.IsTorsionFree.trans_faithfulSMul _ C C₀
  have : Module.IsTorsionFree B₂ C₀ := Module.IsTorsionFree.trans_faithfulSMul _ C C₀
  obtain ⟨Q₀, _, _⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := C₀) Q
  have : Q₀.LiesOver p := LiesOver.trans Q₀ Q p
  have : Q₀.LiesOver P₁ := LiesOver.trans Q₀ Q P₁
  have : Q₀.LiesOver P₂ := LiesOver.trans Q₀ Q P₂
  have : Q₀.LiesOver P := LiesOver.trans Q₀ Q P
  exact ramificationIdx_sup_eq_one_of_isGalois K N (F₁.extendTop N) (F₂.extendTop N) P Q₀ h₁ h₂ hp

include F₁ F₂ Q in
theorem Ideal.ramificationIdx_inertiaDeg_sup_eq_one_of_isGalois [IsGalois K L]
    [MulSemiringAction Gal(L/K) C] [SMulDistribClass Gal(L/K) C L]
    (h₁ : ramificationIdx (algebraMap A B₁) p P₁ = 1 ∧ inertiaDeg p P₁ = 1)
    (h₂ : ramificationIdx (algebraMap A B₂) p P₂ = 1 ∧ inertiaDeg p P₂ = 1)
    (hp : p ≠ ⊥) :
    ramificationIdx (algebraMap A B) p P = 1 ∧ inertiaDeg p P = 1 := by
  have : Module.Finite B₁ C := Module.Finite.right A B₁ C
  have : Module.Finite B₂ C := Module.Finite.right A B₂ C
  have : Module.Finite B C := Module.Finite.right A B C
  let D : IntermediateField K L := FixedPoints.intermediateField (stabilizer Gal(L/K) Q)
  let : Algebra A D := D.algebra'
  let 𝓞D := integralClosure A D
  have : IsDedekindDomain 𝓞D := integralClosure.isDedekindDomain A K D
  have : IsFractionRing 𝓞D D := integralClosure.isFractionRing_of_finite_extension K D
  let : Algebra 𝓞D L := 𝓞D.toAlgebra
  let : Algebra 𝓞D C := (galRestrict' A 𝓞D C D.val).toRingHom.toAlgebra
  have : Module.IsTorsionFree 𝓞D C := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have : IsScalarTower A 𝓞D C := IsScalarTower.of_algHom _
  have : IsScalarTower 𝓞D C L := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    have := algebraMap_galRestrict'_apply A 𝓞D C D.val x
    rw [RingHom.algebraMap_toAlgebra (galRestrict' A 𝓞D C D.val).toRingHom, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, algebraMap_galRestrict'_apply, IsScalarTower.algebraMap_apply 𝓞D D L,
      Subalgebra.algebraMap_apply, IntermediateField.algebraMap_apply, IntermediateField.coe_val]
  rw [← IntermediateField.le_isDecompositionField_iff _ K _ (D := D) (B := C) (𝓞D := 𝓞D) (p := p)
    (P := Q) (F := F₁) _ _ hp] at h₁
  rw [← IntermediateField.le_isDecompositionField_iff _ K _ (D := D) (B := C) (𝓞D := 𝓞D) (p := p)
    (P := Q) (F := F₂) _ _ hp] at h₂
  have := sup_le h₁ h₂
  rwa [IntermediateField.le_isDecompositionField_iff _ K _ (D := D) (B := C) (𝓞D := 𝓞D) (p := p)
    (P := Q) (𝓟F := P) (F := F₁ ⊔ F₂) _ hp] at this

set_option maxHeartbeats 600000 in
-- This result needs some help to compile
include F₁ F₂ C Q in
theorem Ideal.ramificationIdx_inertiaDeg_sup_eq_one [PerfectField K] [PerfectField L]
    [Ring.HasFiniteQuotients C]
    (h₁ : ramificationIdx (algebraMap A B₁) p P₁ = 1 ∧ inertiaDeg p P₁ = 1)
    (h₂ : ramificationIdx (algebraMap A B₂) p P₂ = 1 ∧ inertiaDeg p P₂ = 1) (hp : p ≠ ⊥) :
    ramificationIdx (algebraMap A B) p P = 1 ∧ inertiaDeg p P = 1 := by
  let F : IntermediateField K L := F₁ ⊔ F₂
  let N := IntermediateField.normalClosure K L (AlgebraicClosure L)
  let : Algebra L N := normalClosure.algebra K L (AlgebraicClosure L)
  algebraize [(algebraMap L N).comp (algebraMap C L)]
  have : FiniteDimensional L N := Module.Finite.right K L N
  let C₀ := integralClosure C N
  have : Module.Finite C C₀ := IsIntegralClosure.finite C L N _
  have : Ring.HasFiniteQuotients C₀ := Ring.HasFiniteQuotients.of_module_finite C C₀
  have : FaithfulSMul C N := (faithfulSMul_iff_algebraMap_injective C N).mpr <|
      (FaithfulSMul.algebraMap_injective L N).comp (FaithfulSMul.algebraMap_injective C L)
  have : IsDedekindDomain C₀ := integralClosure.isDedekindDomain C L N
  have : IsFractionRing C₀ N := integralClosure.isFractionRing_of_finite_extension L N
  have : FaithfulSMul C C₀ := Module.IsTorsionFree.to_faithfulSMul
  algebraize [(algebraMap C C₀).comp (algebraMap A C)]
  algebraize [(algebraMap C C₀).comp (algebraMap B C)]
  algebraize [(algebraMap C C₀).comp (algebraMap B₁ C)]
  algebraize [(algebraMap C C₀).comp (algebraMap B₂ C)]
  algebraize [(algebraMap F N).comp (algebraMap B F)]
  algebraize [(algebraMap F₁ N).comp (algebraMap B₁ F₁)]
  algebraize [(algebraMap F₂ N).comp (algebraMap B₂ F₂)]
  have : Module.IsTorsionFree A C₀ := Module.IsTorsionFree.trans_faithfulSMul _ C C₀
  have : IsScalarTower A L N := IsScalarTower.to₁₃₄ A K L N
  have : IsScalarTower A C₀ N := IsScalarTower.of_algebraMap_eq fun _ ↦ by
    rw [IsScalarTower.algebraMap_apply A C C₀, ← IsScalarTower.algebraMap_apply C C₀ N,
        IsScalarTower.algebraMap_apply C L N, ← IsScalarTower.algebraMap_apply A C L,
        ← IsScalarTower.algebraMap_apply A L N]
  have : IsScalarTower A F N := IsScalarTower.to₁₃₄ A K F N
  have : IsScalarTower A B N := IsScalarTower.to₁₂₄ A B F N
  have : Module.Finite A C₀ := Module.Finite.trans C C₀
  let : MulSemiringAction Gal(N/K) C₀ := IsIntegralClosure.MulSemiringAction A K N C₀
  let F' := (F₁.extendTop N) ⊔ (F₂.extendTop N)
  let e : (F.extendTop N) ≃ₐ[K] F' := equivOfEq <| F₁.map_sup F₂ (Algebra.algHom K L N)
  algebraize [e.toRingHom.comp (algebraMap B (F.extendTop N))]
  have : IsFractionRing B F' :=
    .of_algEquiv B (F.extendTop N) _ <| (e.restrictScalars A).extendScalars B
  have : IsScalarTower A B F' := e.symm.toEquiv.isScalarTower A B
  have : IsScalarTower A F₁ N := IsScalarTower.to₁₃₄ A K F₁ N
  have : IsScalarTower A F₂ N := IsScalarTower.to₁₃₄ A K F₂ N
  have : IsScalarTower A B₁ N := IsScalarTower.to₁₂₄ A B₁ F₁ N
  have : IsScalarTower A B₂ N := IsScalarTower.to₁₂₄ A B₂ F₂ N
  have : IsScalarTower B F' N := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B L N := IsScalarTower.to₁₃₄ B F L N
  have : IsScalarTower B C₀ N := IsScalarTower.of_algebraMap_eq fun _ ↦ by
    rw [IsScalarTower.algebraMap_apply B C C₀, ← IsScalarTower.algebraMap_apply C C₀ N,
        IsScalarTower.algebraMap_apply C L N, ← IsScalarTower.algebraMap_apply B C L,
        ← IsScalarTower.algebraMap_apply B L N]
  have : IsScalarTower B₁ L N := IsScalarTower.to₁₃₄ B₁ F₁ L N
  have : IsScalarTower B₁ C₀ N := IsScalarTower.of_algebraMap_eq fun _ ↦ by
    rw [IsScalarTower.algebraMap_apply B₁ C C₀, ← IsScalarTower.algebraMap_apply C C₀ N,
        IsScalarTower.algebraMap_apply C L N, ← IsScalarTower.algebraMap_apply B₁ C L,
        ← IsScalarTower.algebraMap_apply B₁ L N]
  have : IsScalarTower B₂ L N := IsScalarTower.to₁₃₄ B₂ F₂ L N
  have : IsScalarTower B₂ C₀ N := IsScalarTower.of_algebraMap_eq fun _ ↦ by
    rw [IsScalarTower.algebraMap_apply B₂ C C₀, ← IsScalarTower.algebraMap_apply C C₀ N,
        IsScalarTower.algebraMap_apply C L N, ← IsScalarTower.algebraMap_apply B₂ C L,
        ← IsScalarTower.algebraMap_apply B₂ L N]
  have : IsScalarTower A F₁ N := IsScalarTower.to₁₃₄ A B₁ F₁ N
  have : IsScalarTower A F₂ N := IsScalarTower.to₁₃₄ A B₂ F₂ N
  have : IsScalarTower A B C₀ := IsScalarTower.to₁₂₄ A B C C₀
  have : IsScalarTower A B₁ C₀ := IsScalarTower.to₁₂₄ A B₁ C C₀
  have : IsScalarTower A B₂ C₀ := IsScalarTower.to₁₂₄ A B₂ C C₀
  have : Module.IsTorsionFree B C₀ := Module.IsTorsionFree.trans_faithfulSMul _ C C₀
  have : Module.IsTorsionFree B₁ C₀ := Module.IsTorsionFree.trans_faithfulSMul _ C C₀
  have : Module.IsTorsionFree B₂ C₀ := Module.IsTorsionFree.trans_faithfulSMul _ C C₀
  have : IsIntegralClosure B A F' := .of_algEquiv B (e.restrictScalars A) rfl
  obtain ⟨Q₀, _, _⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := C₀) Q
  have : Q₀.LiesOver p := LiesOver.trans Q₀ Q p
  have : Q₀.LiesOver P₁ := LiesOver.trans Q₀ Q P₁
  have : Q₀.LiesOver P₂ := LiesOver.trans Q₀ Q P₂
  have : Q₀.LiesOver P := LiesOver.trans Q₀ Q P
  exact ramificationIdx_inertiaDeg_sup_eq_one_of_isGalois K N (F₁.extendTop N) (F₂.extendTop N)
    P Q₀ h₁ h₂ hp

open NumberField

example {K : Type*} [Field K] [NumberField K] (F₁ F₂ : IntermediateField ℚ K)
    (p : Ideal ℤ) (P₁ : Ideal (𝓞 F₁)) (P₂ : Ideal (𝓞 F₂)) (P : Ideal (𝓞 ↥(F₁ ⊔ F₂)))
    (Q : Ideal (𝓞 K)) [p.IsMaximal] [P₁.IsMaximal] [P₂.IsMaximal] [P.IsMaximal] [Q.IsMaximal]
    [Q.LiesOver p] [Q.LiesOver P₁] [Q.LiesOver P₂] [Q.LiesOver P]
    (h₁ : ramificationIdx (algebraMap ℤ (𝓞 F₁)) p P₁ = 1)
    (h₂ : ramificationIdx (algebraMap ℤ (𝓞 F₂)) p P₂ = 1) (hp : p ≠ ⊥) :
    ramificationIdx (algebraMap ℤ (𝓞 ↥(F₁ ⊔ F₂))) p P = 1 :=
  Ideal.ramificationIdx_sup_eq_one ℚ K F₁ F₂ P Q h₁ h₂ hp

theorem NumberField.not_dvd_discr_finsetSup_of_not_dvd_discr (ι K : Type*) [Field K] [NumberField K]
    (F : ι → IntermediateField ℚ K) [∀ i, NumberField (F i)] {p : ℕ} (hp : p.Prime) (s : Finset ι)
    (hF : ∀ i ∈ s, ¬ (p : ℤ) ∣ discr (F i)) :
    ¬ (p : ℤ) ∣ discr (s.sup F : IntermediateField ℚ K) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sup_empty, discr_eq_discr_of_algEquiv _ (IntermediateField.botEquiv ℚ K),
        Rat.numberField_discr, Int.natCast_dvd_ofNat]
      exact hp.not_dvd_one
  | insert i s hi h =>
      let F₁ := F i
      let F₂ : IntermediateField ℚ K := s.sup F
      let : Algebra F₁ ↥(F₁ ⊔ F₂) := (IntermediateField.inclusion le_sup_left).toAlgebra
      let : Algebra F₂ ↥(F₁ ⊔ F₂) := (IntermediateField.inclusion le_sup_right).toAlgebra
      have : IsScalarTower F₁ ↥(F₁ ⊔ F₂) K := IsScalarTower.of_algebraMap_eq' rfl
      have : IsScalarTower F₂ ↥(F₁ ⊔ F₂) K := IsScalarTower.of_algebraMap_eq' rfl
      rw [Finset.sup_insert,
        not_dvd_discr_iff_forall_liesOver _ (𝓞 ↥(F₁ ⊔ F₂)) (Nat.prime_iff_prime_int.mp hp)]
      intro P hP₁ hP₂
      have hP : P ≠ ⊥ := IsMaximal.ne_bot_of_isIntegral_int P
      refine (Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP).mpr ?_
      let p := under ℤ P
      have hp' : p ≠ ⊥ := under_ne_bot ℤ hP
      let P₁ := under (𝓞 F₁) P
      let P₂ := under (𝓞 F₂) P
      obtain ⟨Q, _, _⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) P
      have : Q.LiesOver p := LiesOver.trans Q P p
      have : Q.LiesOver P₁ := LiesOver.trans Q P P₁
      have : Q.LiesOver P₂ := LiesOver.trans Q P P₂
      refine Ideal.ramificationIdx_sup_eq_one ℚ K F₁ F₂ P Q (P₁ := P₁) (P₂ := P₂) ?_ ?_ hp'
      · have hP₁ : P₁ ≠ ⊥ := under_ne_bot (𝓞 F₁) hP
        rw [← over_def P p, over_def P₁ p, ← Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP₁]
        apply (not_dvd_discr_iff_forall_liesOver _ (𝓞 F₁)
          (Nat.prime_iff_prime_int.mp hp)).mp <| hF i (Finset.mem_insert_self i s)
        · infer_instance
        · infer_instance
      · have hP₂ : P₂ ≠ ⊥ := under_ne_bot (𝓞 F₂) hP
        rw [← over_def P p, over_def P₂ p, ← Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP₂]
        apply (not_dvd_discr_iff_forall_liesOver _ (𝓞 F₂)
          (Nat.prime_iff_prime_int.mp hp)).mp <| h fun _ h ↦ hF _ (Finset.mem_insert_of_mem h)
        · infer_instance
        · infer_instance

instance {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Field A] [Algebra K A] :
    NumberField (IntermediateField.normalClosure K L A) where
  to_finiteDimensional := FiniteDimensional.trans ℚ K _

open IntermediateField
theorem NumberField.dvd_discr_iff_dvd_discr_normalClosure (K A : Type*) [Field K] [NumberField K]
    [Field A] [NumberField A] [Algebra K A] [IsScalarTower ℚ K A] {p : ℕ} (hp : p.Prime) :
    (p : ℤ) ∣ discr K ↔ (p : ℤ) ∣ discr (normalClosure ℚ K A) := by
  refine ⟨?_, ?_⟩
  · intro h
    exact Int.dvd_trans h <| discr_dvd_discr K (normalClosure ℚ K A)
  · intro h
    contrapose! h
    have := NumberField.not_dvd_discr_finsetSup_of_not_dvd_discr (K →ₐ[ℚ] A) A
      (fun f ↦ f.fieldRange) hp (s := Finset.univ) ?_
    · rwa [Finset.sup_univ_eq_iSup, ← normalClosure_def] at this
    · intro f _
      dsimp
      let e : K ≃+* f.fieldRange := by
        refine RingEquiv.ofBijective (f.codRestrict _ <| by simp).toRingHom ⟨?_, ?_⟩
        · exact RingHom.injective _
        · intro ⟨_, ⟨x, rfl⟩⟩
          refine ⟨x, rfl⟩
      rwa [discr_eq_discr_of_ringEquiv _ e.symm]

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 500000 in
theorem NumberField.linearDisjoint_of_isCoprime_discr (L : Type*) [Field L]
    [NumberField L] (K₁ K₂ : IntermediateField ℚ L) (h : IsCoprime (discr K₁) (discr K₂)) :
    K₁.LinearDisjoint K₂ := by
  let M := IntermediateField.normalClosure ℚ L (AlgebraicClosure L)
  let F₁ := K₁.map (Algebra.algHom ℚ L M)
  let F₂ := K₂.map (Algebra.algHom ℚ L M)
  suffices F₁.LinearDisjoint F₂ by
    apply this.algEquiv_of_isAlgebraic _ _ (K₁.equivMap (Algebra.algHom ℚ L M)).symm
      (K₂.equivMap (Algebra.algHom ℚ L M)).symm
    left
    exact isAlgebraic_tower_bot
  let N₁ := (IntermediateField.normalClosure ℚ F₁ M).restrictScalars ℚ
  suffices N₁.LinearDisjoint F₂ by
    refine this.of_le_left ?_
    rintro _ ⟨x, hx, rfl⟩
    apply F₁.val.fieldRange_le_normalClosure
    rw [fieldRange_val]
    exact ⟨x, hx, rfl⟩
  have : IsGalois ℚ N₁ := IsGalois.normalClosure ℚ F₁ M
  apply linearDisjoint_of_isGalois_isCoprime_discr
  rw [discr_eq_discr_of_algEquiv F₂ (K₂.equivMap (Algebra.algHom ℚ L _)).symm]
  rw [Int.isCoprime_iff_nat_coprime] at h ⊢
  refine Nat.coprime_of_dvd' fun p hp hp₁ hp₂ ↦ ?_
  have : N₁ = normalClosure ℚ F₁ M := rfl
  rw [← Int.natCast_dvd, this, ← dvd_discr_iff_dvd_discr_normalClosure _ _ hp,
    discr_eq_discr_of_algEquiv F₁ (K₁.equivMap (Algebra.algHom ℚ L _)).symm,
    Int.natCast_dvd] at hp₁
  have : p ∣ (discr K₁).natAbs.gcd (discr K₂).natAbs := Nat.dvd_gcd hp₁ hp₂
  rwa [h] at this

end applications

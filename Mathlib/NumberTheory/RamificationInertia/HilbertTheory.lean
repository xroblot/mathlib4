/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.RingTheory.NormalClosure
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

public import Mathlib.MWE

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
  [IsInertiaField K L P E] [Algebra B L] [FaithfulSMul B L] [hSD : SMulDistribClass Gal(L/K) B L]

variable (F)

theorem isDecompositionField_sup [MulSemiringAction Gal(L/F) B] [SMulDistribClass Gal(L/F) B L] :
    IsDecompositionField F L P (D ⊔ F : IntermediateField K L) := by
  rw [isDecompositionField_iff]
  let H : Subgroup Gal(L/K) := stabilizer Gal(L/K) P ⊓ F.fixingSubgroup
  have : IsGaloisGroup H ↥(D ⊔ F) L := by
    rw [IsGaloisGroup.subgroup_iff, ← fixedField, IsGalois.fixedField_eq_iff_fixingSubgroup_eq,
      fixingSubgroup_sup, (isDecompositionField_iff_fixingSubgroup K L P).mp inferInstance]
  have : IsGaloisGroup F.fixingSubgroup F L := IsGaloisGroup.intermediateField Gal(L/K) K L F
  have : SMulDistribClass F.fixingSubgroup B L := ⟨fun g ↦ hSD.smul_distrib_smul g⟩
  let e : stabilizer Gal(L/F) P ≃* H := by
    refine (MulEquiv.trans ?_ ((stabilizer F.fixingSubgroup P).equivMapOfInjective _
      F.fixingSubgroup.subtype_injective)).trans <| MulEquiv.subgroupCongr <| by ext; simp [H]
    refine stabilizerEquiv P F.fixingSubgroupEquiv.symm fun _ _ ↦ ?_
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul', fixingSubgroupEquiv_symm_apply_apply]
  exact IsGaloisGroup.of_mulEquiv e fun g x ↦ rfl

theorem isInertiaField_sup [MulSemiringAction Gal(L/F) B] [SMulDistribClass Gal(L/F) B L] :
    IsInertiaField F L P (E ⊔ F : IntermediateField K L) := by
  rw [isInertiaField_iff]
  let H : Subgroup Gal(L/K) := inertia Gal(L/K) P ⊓ F.fixingSubgroup
  have : IsGaloisGroup H ↥(E ⊔ F) L := by
    rw [IsGaloisGroup.subgroup_iff, ← fixedField, IsGalois.fixedField_eq_iff_fixingSubgroup_eq,
      fixingSubgroup_sup, (isInertiaField_iff_fixingSubgroup K L P).mp inferInstance]
  have : IsGaloisGroup F.fixingSubgroup F L := IsGaloisGroup.intermediateField Gal(L/K) K L F
  have : SMulDistribClass F.fixingSubgroup B L := ⟨fun g ↦ hSD.smul_distrib_smul g⟩
  let e : inertia Gal(L/F) P ≃* H := by
    refine (MulEquiv.trans ?_ ((inertia F.fixingSubgroup P).equivMapOfInjective _
      F.fixingSubgroup.subtype_injective)).trans <| MulEquiv.subgroupCongr <| by ext; simp [H]
    refine inertiaEquiv P F.fixingSubgroupEquiv.symm fun _ _ ↦ ?_
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul', fixingSubgroupEquiv_symm_apply_apply]
  exact IsGaloisGroup.of_mulEquiv e fun g x ↦ rfl

variable [IsFractionRing B L] (𝓞F : Type*) [CommRing 𝓞F] [IsIntegrallyClosed 𝓞F] [Algebra 𝓞F F]
  [IsFractionRing 𝓞F F] [Algebra 𝓞F B] [Algebra.IsIntegral 𝓞F B] [Algebra 𝓞F L]
  [IsScalarTower 𝓞F F L] [IsScalarTower 𝓞F B L] (𝓟F : Ideal 𝓞F) [P.LiesOver 𝓟F]

theorem isDecompositionField_le_iff [P.IsPrime] :
    D ≤ F ↔ primesOver 𝓟F B = {P} := by
  rw [← OrderIso.le_iff_le IsGalois.intermediateFieldEquivSubgroup,
      IsGalois.intermediateFieldEquivSubgroup_apply, IsGalois.intermediateFieldEquivSubgroup_apply,
      OrderDual.toDual_le_toDual, (isDecompositionField_iff_fixingSubgroup K L P).mp hD,
      Set.eq_singleton_iff_unique_mem, SetLike.le_def]
  have : P ∈ 𝓟F.primesOver B := ⟨inferInstance, inferInstance⟩
  simp only [this, true_and]
  refine ⟨fun h Q ⟨hQ₁, hQ₂⟩ ↦ ?_, fun h σ hσ ↦ h (σ • P) ⟨IsPrime.smul σ, ?_⟩⟩
  · have : IsGaloisGroup F.fixingSubgroup 𝓞F B := by
      have : IsGaloisGroup F.fixingSubgroup F L := IsGaloisGroup.intermediateField _ _ _ _
      exact IsGaloisGroup.of_isFractionRing _ 𝓞F B F L
    obtain ⟨σ, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup 𝓟F P Q F.fixingSubgroup
    exact h σ.prop
  · refine (liesOver_iff _ _).mpr <| Ideal.ext_iff.mpr fun x ↦ ?_
    suffices σ⁻¹ • algebraMap 𝓞F B x = algebraMap 𝓞F B x by
      rw [mem_comap, mem_pointwise_smul_iff_inv_smul_mem, this, ← mem_comap, ← under_def,
        (liesOver_iff P 𝓟F).mp inferInstance]
    apply FaithfulSMul.algebraMap_injective B L
    rw [algebraMap.smul', inv_smul_eq_iff, AlgEquiv.smul_def, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply 𝓞F F L, (mem_fixingSubgroup_iff _ _).mp hσ]
    exact SetLike.coe_mem _

variable [Ring.HasFiniteQuotients A] [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
  [IsScalarTower A B L] [IsDedekindDomain 𝓞F] [Algebra A 𝓞F] [IsIntegralClosure B 𝓞F L]

variable [CommRing 𝓞D] [IsDedekindDomain 𝓞D] [Algebra 𝓞D D] [IsFractionRing 𝓞D D] [Algebra A 𝓞D]
  [Algebra 𝓞D B] [Module.IsTorsionFree 𝓞D B]
  [IsScalarTower A 𝓞D B] [Algebra 𝓞D L] [IsScalarTower 𝓞D D L] [IsScalarTower 𝓞D B L]
  [IsScalarTower A 𝓞D D] [IsIntegralClosure 𝓞D A D]

variable [Ring.HasFiniteQuotients 𝓞F] [IsDomain 𝓞F] [IsIntegralClosure 𝓞F A F]
  [Module.IsTorsionFree 𝓞F B] [IsScalarTower A 𝓞F F] [IsScalarTower A 𝓞F B]

include 𝓞D P in
theorem le_isDecompositionField_iff [p.IsMaximal] [P.IsMaximal] [𝓟F.IsMaximal] (hp : p ≠ ⊥) :
    F ≤ D ↔ ramificationIdx (algebraMap A 𝓞F) p 𝓟F = 1 ∧ inertiaDeg p 𝓟F = 1 := by
  have hF : 𝓟F ≠ ⊥ := by
    rw [over_def P 𝓟F]
    exact under_ne_bot 𝓞F <| ne_bot_of_liesOver_of_ne_bot hp _
  have : 𝓟F.LiesOver p := LiesOver.tower_bot P 𝓟F p
  have : Module.IsTorsionFree A 𝓞D := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have : Module.Finite A 𝓞D := Module.Finite.left A 𝓞D B
  have : Module.Finite 𝓞F B := Module.Finite.right A 𝓞F B
  have : Module.Finite 𝓞D B := Module.Finite.right A 𝓞D B
  refine ⟨?_, ?_⟩
  · intro h
    let 𝓟D := under 𝓞D P
    let : Algebra 𝓞F 𝓞D := (galRestrict' A 𝓞F 𝓞D (inclusion h)).toRingHom.toAlgebra
    have : IsScalarTower A 𝓞F 𝓞D := IsScalarTower.of_algHom _
    have : IsScalarTower 𝓞F 𝓞D B := by
      refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
      apply FaithfulSMul.algebraMap_injective B L
      rw [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
      simp [IsScalarTower.algebraMap_apply 𝓞D D L, algebraMap_galRestrict'_apply,
        IsScalarTower.algebraMap_apply 𝓞F F L]
    have : Module.IsTorsionFree 𝓞F 𝓞D := Module.IsTorsionFree.of_faithfulSMul _ _ B
    have : 𝓟D.LiesOver 𝓟F := by
      refine (liesOver_iff 𝓟D 𝓟F).mpr ?_
      rw [over_def P 𝓟F]
      exact (under_under P).symm
    have : 𝓟D.IsMaximal := isMaximal_comap_of_isIntegral_of_isMaximal P
    refine ⟨?_, ?_⟩
    · have := ramificationIdx_algebra_tower (Q := 𝓟D) (map_ne_bot_of_ne_bot hF)
        (map_ne_bot_of_ne_bot hp) ?_
      · rw [IsDecompositionField.ramificationIdx_eq A K L P D 𝓞D 𝓟D hp, eq_comm] at this
        exact Nat.eq_one_of_mul_eq_one_right this
      · rw [Ideal.map_le_iff_le_comap, ← under_def, ← over_def 𝓟D 𝓟F]
    · have := inertiaDeg_algebra_tower p 𝓟F 𝓟D
      rw [IsDecompositionField.inertiaDeg_eq A K L P D 𝓞D 𝓟D hp, eq_comm] at this
      exact Nat.eq_one_of_mul_eq_one_right this
  · intro h
    let := IsIntegralClosure.MulSemiringAction 𝓞F F L B
    have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
    have : IsGaloisGroup Gal(L/F) 𝓞F B := .of_isFractionRing _ _ _ F L
    have := isDecompositionField_sup K L P F D
    refine le_of_sup_eq' ?_
    rw [eq_comm]
    refine IntermediateField.eq_of_le_of_finrank_eq' le_sup_left ?_
    rw [IsDecompositionField.rank_left A K L P D hp,
      IsDecompositionField.rank_left 𝓞F F L P ↥(D ⊔ F) hF,
      ramificationIdxIn_eq_ramificationIdx p P Gal(L/K), inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
      ramificationIdx_algebra_tower (map_ne_bot_of_ne_bot hF) (map_ne_bot_of_ne_bot hp), h.1,
      inertiaDeg_algebra_tower p 𝓟F P, h.2, one_mul, one_mul,
      ramificationIdxIn_eq_ramificationIdx 𝓟F P Gal(L/F), inertiaDegIn_eq_inertiaDeg 𝓟F P Gal(L/F)]
    rw [Ideal.map_le_iff_le_comap, ← under_def, ← over_def P 𝓟F]

variable [Ring.HasFiniteQuotients B] [p.IsMaximal] [P.IsMaximal] [𝓟F.IsMaximal]

variable [CommRing 𝓞E] [IsDedekindDomain 𝓞E] [Algebra 𝓞E E] [IsFractionRing 𝓞E E] [Algebra A 𝓞E]
  [Algebra 𝓞E B] [Module.IsTorsionFree 𝓞E B] [IsScalarTower A 𝓞E B] [Algebra 𝓞E L]
  [IsScalarTower 𝓞E E L] [IsScalarTower 𝓞E B L] [IsScalarTower A 𝓞E E] [IsIntegralClosure 𝓞E A E]

attribute [local instance] Ideal.Quotient.field

include A 𝓞E in
theorem isInertiaField_le_iff [P.IsPrime] (hp : p ≠ ⊥) :
    E ≤ F ↔ ramificationIdx (algebraMap 𝓞F B) 𝓟F P = Module.finrank F L := by
  have : Module.Finite 𝓞E B := Module.Finite.right A 𝓞E B
  have : Module.Finite 𝓞F B := Module.Finite.right A 𝓞F B
  have : Module.Finite A 𝓞F := Module.Finite.left A 𝓞F B
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  have : IsGaloisGroup (fixingSubgroup F) 𝓞F B := by
    have : IsGaloisGroup F.fixingSubgroup F L := IsGaloisGroup.intermediateField _ _ _ _
    apply IsGaloisGroup.of_isFractionRing _ _ _ F L
  have : Module.IsTorsionFree A 𝓞E := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have : Module.IsTorsionFree A 𝓞F := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have hPF : 𝓟F ≠ ⊥ := by
    have : 𝓟F.LiesOver p := LiesOver.tower_bot P 𝓟F p
    exact ne_bot_of_liesOver_of_ne_bot hp 𝓟F
  refine ⟨?_, ?_⟩
  · intro h
    let : Algebra E F := (inclusion h).toRingHom.toAlgebra
    have : IsScalarTower E F L := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra 𝓞E 𝓞F := (galRestrict' A 𝓞E 𝓞F (inclusion h)).toRingHom.toAlgebra
    let : Algebra 𝓞E F := ((algebraMap 𝓞F F).comp (algebraMap 𝓞E 𝓞F)).toAlgebra
    have : IsScalarTower 𝓞E 𝓞F F := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower 𝓞E 𝓞F B := by
      refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
      apply FaithfulSMul.algebraMap_injective B L
      rw [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
      simp [IsScalarTower.algebraMap_apply 𝓞E E L, algebraMap_galRestrict'_apply,
        IsScalarTower.algebraMap_apply 𝓞F F L]
    have : IsScalarTower 𝓞E E F := by
      refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
      apply FaithfulSMul.algebraMap_injective F L
      rw [← IsScalarTower.algebraMap_apply E F L, IsScalarTower.algebraMap_apply 𝓞E 𝓞F F,
        ← IsScalarTower.algebraMap_apply 𝓞F F L, IsScalarTower.algebraMap_apply 𝓞F B L,
        ← IsScalarTower.algebraMap_apply 𝓞E 𝓞F B, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply] -- That look's fishy
    have : Module.Finite 𝓞E 𝓞F := Module.Finite.left 𝓞E 𝓞F B
    have : Module.IsTorsionFree 𝓞E 𝓞F := Module.IsTorsionFree.of_faithfulSMul _ _ B
    let 𝓟E := under 𝓞E 𝓟F
    have : P.LiesOver 𝓟E := by
      refine (liesOver_iff _ _).mpr ?_
      rw [← under_under (B := 𝓞F) P, ← over_def P 𝓟F]
    refine ramificationIdx_eq_finrank_of_finrank_le' E F L 𝓟F ?_ (Q := P) (p := 𝓟E)
    rw [IsInertiaField.rank_left A K L P E hp,
      ← ramificationIdxIn_eq_ramificationIdx 𝓟E P (inertia Gal(L/K) P),
      IsInertiaField.ramificationIdxIn_eq A K L P E 𝓞E 𝓟E hp]
  · intro h
    let := IsIntegralClosure.MulSemiringAction 𝓞F F L B
    have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
    have : IsGaloisGroup Gal(L/F) 𝓞F B := .of_isFractionRing _ _ _ F L
    have := isInertiaField_sup K L P F E
    refine le_of_sup_eq ?_
    rw [eq_comm]
    refine IntermediateField.eq_of_le_of_finrank_eq' le_sup_right ?_
    rw [← h]
    have := IsInertiaField.rank_left 𝓞F F L P ↥(E ⊔ F) (p := 𝓟F) hPF
    rw [this, ramificationIdxIn_eq_ramificationIdx 𝓟F P (fixingSubgroup F)]

include 𝓞E P in
theorem le_isInertiaField_iff
     (hp : p ≠ ⊥) :
    F ≤ E ↔ ramificationIdx (algebraMap A 𝓞F) p 𝓟F = 1 := by
  have : Module.Finite A 𝓞E := Module.Finite.left A 𝓞E B
  have : Module.Finite 𝓞E B := Module.Finite.right A 𝓞E B
  have : Module.Finite 𝓞F B := Module.Finite.right A 𝓞F B
  have : Module.IsTorsionFree A 𝓞E := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have hP : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  have : Finite (B ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
  have : 𝓟F.LiesOver p := LiesOver.tower_bot P 𝓟F p
  have hF : 𝓟F ≠ ⊥ := by
    rw [over_def P 𝓟F]
    exact under_ne_bot 𝓞F <| ne_bot_of_liesOver_of_ne_bot hp _
  refine ⟨?_, ?_⟩
  · intro h
    let : Algebra 𝓞F 𝓞E := (galRestrict' A 𝓞F 𝓞E (inclusion h)).toRingHom.toAlgebra
    have : IsScalarTower 𝓞F 𝓞E B := by
      refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
      apply FaithfulSMul.algebraMap_injective B L
      rw [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
      simp [IsScalarTower.algebraMap_apply 𝓞E E L, algebraMap_galRestrict'_apply,
        IsScalarTower.algebraMap_apply 𝓞F F L]
    have : Algebra.IsIntegral 𝓞F 𝓞E := by
      have : Module.Finite 𝓞F 𝓞E := by
        apply Module.Finite.right A 𝓞F 𝓞E
      refine Algebra.IsIntegral.of_finite 𝓞F 𝓞E
    have : FaithfulSMul 𝓞F 𝓞E := FaithfulSMul.tower_bot 𝓞F 𝓞E B
    let 𝓟E := under 𝓞E P
    have := ramificationIdx_algebra_tower (p := p) (P := 𝓟F) (Q := 𝓟E) ?_ ?_ ?_
    · rw [IsInertiaField.ramificationIdx_eq A K L P E 𝓞E 𝓟E hp, eq_comm] at this
      exact Nat.eq_one_of_mul_eq_one_right this
    · exact map_ne_bot_of_ne_bot hF
    · exact map_ne_bot_of_ne_bot hp
    · rw [Ideal.map_le_iff_le_comap,  ← under_def, ← over_def 𝓟E 𝓟F]
  · intro h
    let := IsIntegralClosure.MulSemiringAction 𝓞F F L B
    have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
    have : IsGaloisGroup Gal(L/F) 𝓞F B := .of_isFractionRing _ _ _ F L
    have := isInertiaField_sup K L P F E
    refine le_of_sup_eq' ?_
    rw [eq_comm]
    refine IntermediateField.eq_of_le_of_finrank_eq' le_sup_left ?_
    rw [IsInertiaField.rank_left A K L P E hp,
      IsInertiaField.rank_left 𝓞F F L P ↥(E ⊔ F) hF,
      ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
      ramificationIdx_algebra_tower (map_ne_bot_of_ne_bot hF) (map_ne_bot_of_ne_bot hp), h,
      one_mul, ramificationIdxIn_eq_ramificationIdx 𝓟F P Gal(L/F)]
    rw [Ideal.map_le_iff_le_comap, ← under_def, ← over_def P 𝓟F]

end IntermediateField

section applications

theorem Ideal.ramificationIdx_sup_eq_one_of_isGalois (K L : Type*) [Field K] [Field L] [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L]
    (F₁ F₂ : IntermediateField K L) {A B₁ B₂ B C : Type*} [CommRing A] [CommRing B₁]
    [CommRing B₂] [CommRing B] [CommRing C] [Ring.HasFiniteQuotients A] [IsDedekindDomain A]
    [Ring.HasFiniteQuotients C] [IsDedekindDomain C]
    [Algebra A K] [IsFractionRing A K]
    [Algebra C L] [IsFractionRing C L]
    [Algebra B₁ F₁] [IsFractionRing B₁ F₁] [Ring.HasFiniteQuotients B₁] [IsDedekindDomain B₁]
    [Algebra B₂ F₂] [IsFractionRing B₂ F₂] [Ring.HasFiniteQuotients B₂] [IsDedekindDomain B₂]
    [Algebra B ↥(F₁ ⊔ F₂)] [IsFractionRing B ↥(F₁ ⊔ F₂)] [Ring.HasFiniteQuotients B]
    [IsDedekindDomain B]
    [MulSemiringAction Gal(L/K) C] [SMulDistribClass Gal(L/K) C L]
    [Algebra A B₁] [Algebra A B₂] [Algebra A B]
    [Algebra A C] [Algebra B₁ C] [Algebra B₂ C] [Algebra B C]
    [Module.Finite A C] [Module.IsTorsionFree A C]
    [Algebra A L] [IsScalarTower A K L] [IsScalarTower A C L]
    [Algebra B₁ L] [IsScalarTower B₁ F₁ L] [IsScalarTower B₁ C L]
    [Algebra B₂ L] [IsScalarTower B₂ F₂ L] [IsScalarTower B₂ C L]
    [Algebra B L] [IsScalarTower B ↥(F₁ ⊔ F₂) L] [IsScalarTower B C L]
    [Module.IsTorsionFree B₁ C] [Module.IsTorsionFree B₂ C] [Module.IsTorsionFree B C]
    [IsIntegralClosure B₁ A F₁] [IsIntegralClosure B₂ A F₂] [IsIntegralClosure B A ↥(F₁ ⊔ F₂)]
    [IsScalarTower A B₁ F₁] [IsScalarTower A B₂ F₂]
    [IsScalarTower A B₁ C] [IsScalarTower A B₂ C]
    [IsScalarTower A B ↥(F₁ ⊔ F₂)] [IsScalarTower A B C]
    {p : Ideal A} {P₁ : Ideal B₁} {P₂ : Ideal B₂} (P : Ideal B) (Q : Ideal C)
    [p.IsMaximal] [P₁.IsMaximal] [P₂.IsMaximal] [P.IsMaximal] [Q.IsMaximal]
    [Q.LiesOver p] [Q.LiesOver P₁] [Q.LiesOver P₂] [Q.LiesOver P]
    (h₁ : ramificationIdx (algebraMap A B₁) p P₁ = 1)
    (h₂ : ramificationIdx (algebraMap A B₂) p P₂ = 1) (hp : p ≠ ⊥) :
    ramificationIdx (algebraMap A B) p P = 1 := by
  have : Module.Finite B₁ C := Module.Finite.right A B₁ C
  have : Module.Finite B₂ C := Module.Finite.right A B₂ C
  have : Module.Finite B C := Module.Finite.right A B C
  let E : IntermediateField K L := FixedPoints.intermediateField (inertia Gal(L/K) Q)
  let : Algebra A E := E.algebra'
  let 𝓞E := integralClosure A E
  have : IsDedekindDomain 𝓞E := integralClosure.isDedekindDomain A K E
  have : IsFractionRing 𝓞E E := integralClosure.isFractionRing_of_finite_extension K E
  let : Algebra 𝓞E L := 𝓞E.toAlgebra
  let : Algebra 𝓞E C := (galRestrict' A 𝓞E C E.val).toRingHom.toAlgebra
  have : Module.IsTorsionFree 𝓞E C := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have : IsScalarTower A 𝓞E C := IsScalarTower.of_algHom _
  have : IsScalarTower 𝓞E C L := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    have := algebraMap_galRestrict'_apply A 𝓞E C E.val x
    rw [RingHom.algebraMap_toAlgebra (galRestrict' A 𝓞E C E.val).toRingHom, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, algebraMap_galRestrict'_apply, IsScalarTower.algebraMap_apply 𝓞E E L,
      Subalgebra.algebraMap_apply, IntermediateField.algebraMap_apply, IntermediateField.coe_val]
  rw [← IntermediateField.le_isInertiaField_iff _ K _ (E := E) (B := C) (𝓞E := 𝓞E) (p := p)
    (P := Q) (F := F₁) _ _ hp] at h₁
  rw [← IntermediateField.le_isInertiaField_iff _ K _ (E := E) (B := C) (𝓞E := 𝓞E) (p := p)
    (P := Q) (F := F₂) _ _ hp] at h₂
  have := sup_le h₁ h₂
  rwa [IntermediateField.le_isInertiaField_iff _ K _ (E := E) (B := C) (𝓞E := 𝓞E) (p := p)
    (P := Q) (𝓟F := P) (F := F₁ ⊔ F₂) _ hp] at this

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 50000 in
open IntermediateField in
theorem Ideal.ramificationIdx_sup_eq_one (K L : Type*) [Field K] [Field L]
    [PerfectField K]
    [PerfectField L]
    [Algebra K L]
    [FiniteDimensional K L]
    (F₁ F₂ : IntermediateField K L) {A B₁ B₂ B C : Type*} [CommRing A] [CommRing B] [CommRing B₁]
    [CommRing B₂] [CommRing C] [Ring.HasFiniteQuotients A] [IsDedekindDomain A]
    [Ring.HasFiniteQuotients C] [IsDedekindDomain C]
    [Algebra A K] [IsFractionRing A K]
    [Algebra C L] [IsFractionRing C L]
    [Algebra B₁ F₁] [IsFractionRing B₁ F₁] [Ring.HasFiniteQuotients B₁] [IsDedekindDomain B₁]
    [Algebra B₂ F₂] [IsFractionRing B₂ F₂] [Ring.HasFiniteQuotients B₂] [IsDedekindDomain B₂]
    [Algebra B ↥(F₁ ⊔ F₂)] [IsFractionRing B ↥(F₁ ⊔ F₂)] [Ring.HasFiniteQuotients B]
    [IsDedekindDomain B]
    [Algebra A B₁] [Algebra A B₂] [Algebra A B]
    [Algebra A C] [Algebra B₁ C] [Algebra B₂ C] [Algebra B C]
    [Module.Finite A C] [Module.IsTorsionFree A C]
    [Algebra A L] [IsScalarTower A K L] [IsScalarTower A C L]
    [Algebra B₁ L] [IsScalarTower B₁ F₁ L] [IsScalarTower B₁ C L]
    [Algebra B₂ L] [IsScalarTower B₂ F₂ L] [IsScalarTower B₂ C L]
    [Algebra B L] [IsScalarTower B ↥(F₁ ⊔ F₂) L] [IsScalarTower B C L]
    [Module.IsTorsionFree B₁ C] [Module.IsTorsionFree B₂ C] [Module.IsTorsionFree B C]
    [IsIntegralClosure B₁ A F₁] [IsIntegralClosure B₂ A F₂] [IsIntegralClosure B A ↥(F₁ ⊔ F₂)]
    [IsScalarTower A B₁ F₁] [IsScalarTower A B₂ F₂]
    [IsScalarTower A B₁ C] [IsScalarTower A B₂ C]
    [IsScalarTower A B ↥(F₁ ⊔ F₂)] [IsScalarTower A B C]
    (p : Ideal A) (P₁ : Ideal B₁) (P₂ : Ideal B₂) (P : Ideal B) (Q : Ideal C)
    [p.IsMaximal] [P₁.IsMaximal] [P₂.IsMaximal] [P.IsMaximal] [Q.IsMaximal]
    [Q.LiesOver p] [Q.LiesOver P₁] [Q.LiesOver P₂] [Q.LiesOver P]
    (h₁ : ramificationIdx (algebraMap A B₁) p P₁ = 1)
    (h₂ : ramificationIdx (algebraMap A B₂) p P₂ = 1) (hp : p ≠ ⊥) :
    ramificationIdx (algebraMap A B) p P = 1 := by
  let N := IntermediateField.normalClosure K L (AlgebraicClosure L)
  let : Algebra L N := normalClosure.algebra K L (AlgebraicClosure L)
  have : FiniteDimensional L N := Module.Finite.right K L N
  have : Algebra.IsSeparable L N := Algebra.IsAlgebraic.isSeparable_of_perfectField
  algebraize [(algebraMap L N).comp (algebraMap C L)]
  let C₀ := integralClosure C N
  have : Module.Finite C C₀ := IsIntegralClosure.finite C L N _
  have : Ring.HasFiniteQuotients C₀ := Ring.HasFiniteQuotients.of_module_finite C C₀
  have : FaithfulSMul C N := (faithfulSMul_iff_algebraMap_injective C N).mpr <|
      (FaithfulSMul.algebraMap_injective L N).comp (FaithfulSMul.algebraMap_injective C L)
  have : Module.IsTorsionFree C C₀ := Subalgebra.instIsTorsionFree (integralClosure C N)
  have : IsDedekindDomain C₀ := integralClosure.isDedekindDomain C L N
  have : IsFractionRing C₀ N := integralClosure.isFractionRing_of_finite_extension L N
  algebraize [(algebraMap C C₀).comp (algebraMap A C)]
  algebraize [(algebraMap C C₀).comp (algebraMap B C)]
  algebraize [(algebraMap C C₀).comp (algebraMap B₁ C)]
  algebraize [(algebraMap C C₀).comp (algebraMap B₂ C)]
  have : Module.Finite A C₀ := Module.Finite.trans C C₀
  have : Module.IsTorsionFree A C₀ := Module.IsTorsionFree.trans_faithfulSMul _ C C₀
  have : Module.IsTorsionFree B₁ C₀ := Module.IsTorsionFree.trans_faithfulSMul _ C C₀
  have : Module.IsTorsionFree B₂ C₀ := Module.IsTorsionFree.trans_faithfulSMul _ C C₀
  have : Module.IsTorsionFree B C₀ := Module.IsTorsionFree.trans_faithfulSMul _ C C₀
  have : IsScalarTower A L N := IsScalarTower.to₁₃₄ A K L N
  have : IsScalarTower A C N := IsScalarTower.to₁₂₄ A C L N
  have : IsScalarTower A C₀ N := IsScalarTower.to₁₃₄ A C C₀ N
  have : IsScalarTower A B₁ C₀ := IsScalarTower.to₁₂₄ A B₁ C C₀
  have : IsScalarTower A B₂ C₀ := IsScalarTower.to₁₂₄ A B₂ C C₀
  have : IsScalarTower A B C₀ := IsScalarTower.to₁₂₄ A B C C₀
  let : MulSemiringAction Gal(N/K) C₀ := IsIntegralClosure.MulSemiringAction A K N C₀
  let F₁' := F₁.map (Algebra.algHom K L N)
  let f₁ : F₁ ≃ₐ[K] F₁' := F₁.equivMap (Algebra.algHom K L N)
  algebraize [f₁.toRingHom]
  let F₂' := F₂.map (Algebra.algHom K L N)
  let F' := F₁' ⊔ F₂'
  let f₂ : F₂ ≃ₐ[K] F₂' := F₂.equivMap (Algebra.algHom K L N)
  algebraize [f₂.toRingHom]
  let F := F₁ ⊔ F₂
  let f : F ≃ₐ[K] F' := (F.equivMap (Algebra.algHom K L N)).trans <| equivOfEq <| F₁.map_sup F₂ _
  algebraize [f.toRingHom]
  algebraize [(algebraMap F₁ F₁').comp (algebraMap B₁ F₁)]
  algebraize [(algebraMap F₂ F₂').comp (algebraMap B₂ F₂)]
  algebraize [(algebraMap F F').comp (algebraMap B F)]
  have : IsFractionRing B₁ F₁' := .of_algEquiv B₁ _ _ <| (f₁.restrictScalars A).extendScalars B₁
  have : IsIntegralClosure B₁ A F₁' := .of_algEquiv B₁ A F₁ _ (f₁.restrictScalars A) rfl
  have : IsFractionRing B₂ F₂' := .of_algEquiv B₂ _ _ <| (f₂.restrictScalars A).extendScalars B₂
  have : IsIntegralClosure B₂ A F₂' := .of_algEquiv B₂ A F₂ _ (f₂.restrictScalars A) rfl
  have : IsFractionRing B F' := .of_algEquiv B _ _ <| (f.restrictScalars A).extendScalars B
  have : IsIntegralClosure B A F' := .of_algEquiv B A F _ (f.restrictScalars A) rfl
  algebraize [(algebraMap C N).comp (algebraMap B₁ C)]
  algebraize [(algebraMap C N).comp (algebraMap B₂ C)]
  algebraize [(algebraMap C N).comp (algebraMap B C)]
  have : IsScalarTower F₁ F₁' N := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B₁ F₁ F₁' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B₁ F₁ N := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    rw [IsScalarTower.algebraMap_apply B₁ C N, IsScalarTower.algebraMap_apply C L N,
      IsScalarTower.algebraMap_apply F₁ L N, ← IsScalarTower.algebraMap_apply B₁ C L,
      ← IsScalarTower.algebraMap_apply B₁ F₁ L]
  have : IsScalarTower B₁ F₁' N := IsScalarTower.to₁₃₄ B₁ F₁ F₁' N
  have : IsScalarTower F₂ F₂' N := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B₂ F₂ F₂' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B₂ F₂ N := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    rw [IsScalarTower.algebraMap_apply B₂ C N, IsScalarTower.algebraMap_apply C L N,
      IsScalarTower.algebraMap_apply F₂ L N, ← IsScalarTower.algebraMap_apply B₂ C L,
      ← IsScalarTower.algebraMap_apply B₂ F₂ L]
  have : IsScalarTower B₂ F₂' N := IsScalarTower.to₁₃₄ B₂ F₂ F₂' N
  have : IsScalarTower F F' N := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B F F' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B F N := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    rw [IsScalarTower.algebraMap_apply B C N, IsScalarTower.algebraMap_apply C L N,
      IsScalarTower.algebraMap_apply F L N, ← IsScalarTower.algebraMap_apply B C L,
      ← IsScalarTower.algebraMap_apply B F L]
  have : IsScalarTower B F' N := IsScalarTower.to₁₃₄ B F F' N
  have : IsScalarTower A F₁ F₁' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A B₁ F₁' := IsScalarTower.to₁₂₄ A B₁ F₁ F₁'
  have : IsScalarTower A F₂ F₂' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A B₂ F₂' := IsScalarTower.to₁₂₄ A B₂ F₂ F₂'
  have : IsScalarTower A F F' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A B F' := IsScalarTower.to₁₂₄ A B F F'
  obtain ⟨Q₀, _, _⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := C₀) Q
  have : Q₀.LiesOver p := LiesOver.trans Q₀ Q p
  have : Q₀.LiesOver P₁ := LiesOver.trans Q₀ Q P₁
  have : Q₀.LiesOver P₂ := LiesOver.trans Q₀ Q P₂
  have : Q₀.LiesOver P := LiesOver.trans Q₀ Q P
  exact ramificationIdx_sup_eq_one_of_isGalois K N F₁' F₂' P Q₀ h₁ h₂ hp

theorem Ideal.ramificationIdx_inertiaDeg_sup_eq_one_of_isGalois (K L : Type*) [Field K] [Field L]
    [Algebra K L]
    [IsGalois K L] [FiniteDimensional K L]
    (F₁ F₂ : IntermediateField K L) {A B₁ B₂ B C : Type*} [CommRing A] [CommRing B₁]
    [CommRing B₂] [CommRing B] [CommRing C] [Ring.HasFiniteQuotients A] [IsDedekindDomain A]
    [IsDedekindDomain C]
    [Algebra A K] [IsFractionRing A K]
    [Algebra C L] [IsFractionRing C L]
    [Algebra B₁ F₁] [IsFractionRing B₁ F₁] [Ring.HasFiniteQuotients B₁] [IsDedekindDomain B₁]
    [Algebra B₂ F₂] [IsFractionRing B₂ F₂] [Ring.HasFiniteQuotients B₂] [IsDedekindDomain B₂]
    [Algebra B ↥(F₁ ⊔ F₂)] [IsFractionRing B ↥(F₁ ⊔ F₂)] [Ring.HasFiniteQuotients B]
    [IsDedekindDomain B]
    [MulSemiringAction Gal(L/K) C] [SMulDistribClass Gal(L/K) C L]
    [Algebra A B₁] [Algebra A B₂] [Algebra A B]
    [Algebra A C] [Algebra B₁ C] [Algebra B₂ C] [Algebra B C]
    [Module.Finite A C] [Module.IsTorsionFree A C]
    [Algebra A L] [IsScalarTower A K L] [IsScalarTower A C L]
    [Algebra B₁ L] [IsScalarTower B₁ F₁ L] [IsScalarTower B₁ C L]
    [Algebra B₂ L] [IsScalarTower B₂ F₂ L] [IsScalarTower B₂ C L]
    [Algebra B L] [IsScalarTower B ↥(F₁ ⊔ F₂) L] [IsScalarTower B C L]
    [Module.IsTorsionFree B₁ C] [Module.IsTorsionFree B₂ C] [Module.IsTorsionFree B C]
    [IsIntegralClosure B₁ A F₁] [IsIntegralClosure B₂ A F₂] [IsIntegralClosure B A ↥(F₁ ⊔ F₂)]
    [IsScalarTower A B₁ F₁] [IsScalarTower A B₂ F₂]
    [IsScalarTower A B₁ C] [IsScalarTower A B₂ C]
    [IsScalarTower A B ↥(F₁ ⊔ F₂)] [IsScalarTower A B C]
    {p : Ideal A} {P₁ : Ideal B₁} {P₂ : Ideal B₂} (P : Ideal B) (Q : Ideal C)
    [p.IsMaximal] [P₁.IsMaximal] [P₂.IsMaximal] [P.IsMaximal] [Q.IsMaximal]
    [Q.LiesOver p] [Q.LiesOver P₁] [Q.LiesOver P₂] [Q.LiesOver P]
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

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 50000 in
theorem Ideal.ramificationIdx_inertiaDeg_sup_eq_one (K L : Type*) [Field K] [Field L]
    [PerfectField K]
    [PerfectField L]
    [Algebra K L]
    [FiniteDimensional K L]
    (F₁ F₂ : IntermediateField K L) {A B₁ B₂ B C : Type*} [CommRing A] [CommRing B] [CommRing B₁]
    [CommRing B₂] [CommRing C] [Ring.HasFiniteQuotients A] [IsDedekindDomain A]
    [Ring.HasFiniteQuotients C] [IsDedekindDomain C]
    [Algebra A K] [IsFractionRing A K]
    [Algebra C L] [IsFractionRing C L]
    [Algebra B₁ F₁] [IsFractionRing B₁ F₁] [Ring.HasFiniteQuotients B₁] [IsDedekindDomain B₁]
    [Algebra B₂ F₂] [IsFractionRing B₂ F₂] [Ring.HasFiniteQuotients B₂] [IsDedekindDomain B₂]
    [Algebra B ↥(F₁ ⊔ F₂)] [IsFractionRing B ↥(F₁ ⊔ F₂)] [Ring.HasFiniteQuotients B]
    [IsDedekindDomain B]
    [Algebra A B₁] [Algebra A B₂] [Algebra A B]
    [Algebra A C] [Algebra B₁ C] [Algebra B₂ C] [Algebra B C]
    [Module.Finite A C] [Module.IsTorsionFree A C]
    [Algebra A L] [IsScalarTower A K L] [IsScalarTower A C L]
    [Algebra B₁ L] [IsScalarTower B₁ F₁ L] [IsScalarTower B₁ C L]
    [Algebra B₂ L] [IsScalarTower B₂ F₂ L] [IsScalarTower B₂ C L]
    [Algebra B L] [IsScalarTower B ↥(F₁ ⊔ F₂) L] [IsScalarTower B C L]
    [Module.IsTorsionFree B₁ C] [Module.IsTorsionFree B₂ C] [Module.IsTorsionFree B C]
    [IsIntegralClosure B₁ A F₁] [IsIntegralClosure B₂ A F₂] [IsIntegralClosure B A ↥(F₁ ⊔ F₂)]
    [IsScalarTower A B₁ F₁] [IsScalarTower A B₂ F₂]
    [IsScalarTower A B₁ C] [IsScalarTower A B₂ C]
    [IsScalarTower A B ↥(F₁ ⊔ F₂)] [IsScalarTower A B C]
    (p : Ideal A) (P₁ : Ideal B₁) (P₂ : Ideal B₂) (P : Ideal B) (Q : Ideal C)
    [p.IsMaximal] [P₁.IsMaximal] [P₂.IsMaximal] [P.IsMaximal] [Q.IsMaximal]
    [Q.LiesOver p] [Q.LiesOver P₁] [Q.LiesOver P₂] [Q.LiesOver P]
    (h₁ : ramificationIdx (algebraMap A B₁) p P₁ = 1 ∧ inertiaDeg p P₁ = 1)
    (h₂ : ramificationIdx (algebraMap A B₂) p P₂ = 1 ∧ inertiaDeg p P₂ = 1) (hp : p ≠ ⊥) :
    ramificationIdx (algebraMap A B) p P = 1 ∧ inertiaDeg p P = 1 := by
  let N := IntermediateField.normalClosure K L (AlgebraicClosure L)
  let : Algebra L N := normalClosure.algebra K L (AlgebraicClosure L)
  have : FiniteDimensional L N := Module.Finite.right K L N
  have : Algebra.IsSeparable L N := Algebra.IsAlgebraic.isSeparable_of_perfectField
  algebraize [(algebraMap L N).comp (algebraMap C L)]
  let C₀ := integralClosure C N
  have : Module.Finite C C₀ := IsIntegralClosure.finite C L N _
  have : Ring.HasFiniteQuotients C₀ := Ring.HasFiniteQuotients.of_module_finite C C₀
  have : FaithfulSMul C N := (faithfulSMul_iff_algebraMap_injective C N).mpr <|
      (FaithfulSMul.algebraMap_injective L N).comp (FaithfulSMul.algebraMap_injective C L)
  have : Module.IsTorsionFree C C₀ := Subalgebra.instIsTorsionFree (integralClosure C N)
  have : IsDedekindDomain C₀ := integralClosure.isDedekindDomain C L N
  have : IsFractionRing C₀ N := integralClosure.isFractionRing_of_finite_extension L N
  algebraize [(algebraMap C C₀).comp (algebraMap A C)]
  algebraize [(algebraMap C C₀).comp (algebraMap B C)]
  algebraize [(algebraMap C C₀).comp (algebraMap B₁ C)]
  algebraize [(algebraMap C C₀).comp (algebraMap B₂ C)]
  have : Module.Finite A C₀ := Module.Finite.trans C C₀
  have : Module.IsTorsionFree A C₀ := Module.IsTorsionFree.trans_faithfulSMul _ C C₀
  have : Module.IsTorsionFree B₁ C₀ := Module.IsTorsionFree.trans_faithfulSMul _ C C₀
  have : Module.IsTorsionFree B₂ C₀ := Module.IsTorsionFree.trans_faithfulSMul _ C C₀
  have : Module.IsTorsionFree B C₀ := Module.IsTorsionFree.trans_faithfulSMul _ C C₀
  have : IsScalarTower A L N := IsScalarTower.to₁₃₄ A K L N
  have : IsScalarTower A C N := IsScalarTower.to₁₂₄ A C L N
  have : IsScalarTower A C₀ N := IsScalarTower.to₁₃₄ A C C₀ N
  have : IsScalarTower A B₁ C₀ := IsScalarTower.to₁₂₄ A B₁ C C₀
  have : IsScalarTower A B₂ C₀ := IsScalarTower.to₁₂₄ A B₂ C C₀
  have : IsScalarTower A B C₀ := IsScalarTower.to₁₂₄ A B C C₀
  let : MulSemiringAction Gal(N/K) C₀ := IsIntegralClosure.MulSemiringAction A K N C₀
  let F₁' := F₁.map (Algebra.algHom K L N)
  let f₁ : F₁ ≃ₐ[K] F₁' := F₁.equivMap (Algebra.algHom K L N)
  algebraize [f₁.toRingHom]
  let F₂' := F₂.map (Algebra.algHom K L N)
  let F' := F₁' ⊔ F₂'
  let f₂ : F₂ ≃ₐ[K] F₂' := F₂.equivMap (Algebra.algHom K L N)
  algebraize [f₂.toRingHom]
  let F := F₁ ⊔ F₂
  let f : F ≃ₐ[K] F' := (F.equivMap (Algebra.algHom K L N)).trans <|
    IntermediateField.equivOfEq <| F₁.map_sup F₂ _
  algebraize [f.toRingHom]
  algebraize [(algebraMap F₁ F₁').comp (algebraMap B₁ F₁)]
  algebraize [(algebraMap F₂ F₂').comp (algebraMap B₂ F₂)]
  algebraize [(algebraMap F F').comp (algebraMap B F)]
  have : IsFractionRing B₁ F₁' := .of_algEquiv B₁ _ _ <| (f₁.restrictScalars A).extendScalars B₁
  have : IsIntegralClosure B₁ A F₁' := .of_algEquiv B₁ A F₁ _ (f₁.restrictScalars A) rfl
  have : IsFractionRing B₂ F₂' := .of_algEquiv B₂ _ _ <| (f₂.restrictScalars A).extendScalars B₂
  have : IsIntegralClosure B₂ A F₂' := .of_algEquiv B₂ A F₂ _ (f₂.restrictScalars A) rfl
  have : IsFractionRing B F' := .of_algEquiv B _ _ <| (f.restrictScalars A).extendScalars B
  have : IsIntegralClosure B A F' := .of_algEquiv B A F _ (f.restrictScalars A) rfl
  algebraize [(algebraMap C N).comp (algebraMap B₁ C)]
  algebraize [(algebraMap C N).comp (algebraMap B₂ C)]
  algebraize [(algebraMap C N).comp (algebraMap B C)]
  have : IsScalarTower F₁ F₁' N := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B₁ F₁ F₁' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B₁ F₁ N := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    rw [IsScalarTower.algebraMap_apply B₁ C N, IsScalarTower.algebraMap_apply C L N,
      IsScalarTower.algebraMap_apply F₁ L N, ← IsScalarTower.algebraMap_apply B₁ C L,
      ← IsScalarTower.algebraMap_apply B₁ F₁ L]
  have : IsScalarTower B₁ F₁' N := IsScalarTower.to₁₃₄ B₁ F₁ F₁' N
  have : IsScalarTower F₂ F₂' N := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B₂ F₂ F₂' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B₂ F₂ N := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    rw [IsScalarTower.algebraMap_apply B₂ C N, IsScalarTower.algebraMap_apply C L N,
      IsScalarTower.algebraMap_apply F₂ L N, ← IsScalarTower.algebraMap_apply B₂ C L,
      ← IsScalarTower.algebraMap_apply B₂ F₂ L]
  have : IsScalarTower B₂ F₂' N := IsScalarTower.to₁₃₄ B₂ F₂ F₂' N
  have : IsScalarTower F F' N := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B F F' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B F N := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    rw [IsScalarTower.algebraMap_apply B C N, IsScalarTower.algebraMap_apply C L N,
      IsScalarTower.algebraMap_apply F L N, ← IsScalarTower.algebraMap_apply B C L,
      ← IsScalarTower.algebraMap_apply B F L]
  have : IsScalarTower B F' N := IsScalarTower.to₁₃₄ B F F' N
  have : IsScalarTower A F₁ F₁' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A B₁ F₁' := IsScalarTower.to₁₂₄ A B₁ F₁ F₁'
  have : IsScalarTower A F₂ F₂' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A B₂ F₂' := IsScalarTower.to₁₂₄ A B₂ F₂ F₂'
  have : IsScalarTower A F F' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A B F' := IsScalarTower.to₁₂₄ A B F F'
  obtain ⟨Q₀, _, _⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := C₀) Q
  have : Q₀.LiesOver p := LiesOver.trans Q₀ Q p
  have : Q₀.LiesOver P₁ := LiesOver.trans Q₀ Q P₁
  have : Q₀.LiesOver P₂ := LiesOver.trans Q₀ Q P₂
  have : Q₀.LiesOver P := LiesOver.trans Q₀ Q P
  exact ramificationIdx_inertiaDeg_sup_eq_one_of_isGalois K N F₁' F₂' P Q₀ h₁ h₂ hp






open NumberField

example {K : Type*} [Field K] [NumberField K] (F₁ F₂ : IntermediateField ℚ K)
    (p : Ideal ℤ) (P₁ : Ideal (𝓞 F₁)) (P₂ : Ideal (𝓞 F₂)) (P : Ideal (𝓞 ↥(F₁ ⊔ F₂)))
    (Q : Ideal (𝓞 K)) [p.IsMaximal] [P₁.IsMaximal] [P₂.IsMaximal] [P.IsMaximal] [Q.IsMaximal]
    [Q.LiesOver p] [Q.LiesOver P₁] [Q.LiesOver P₂] [Q.LiesOver P]
    (h₁ : ramificationIdx (algebraMap ℤ (𝓞 F₁)) p P₁ = 1)
    (h₂ : ramificationIdx (algebraMap ℤ (𝓞 F₂)) p P₂ = 1) (hp : p ≠ ⊥) :
    ramificationIdx (algebraMap ℤ (𝓞 ↥(F₁ ⊔ F₂))) p P = 1 := by
  exact Ideal.ramificationIdx_sup_eq_one ℚ K F₁ F₂ _  _ _ P Q h₁ h₂ hp

-- instance {ι K : Type*} [Field K] [CharZero K] (s : Finset ι) (F : ι → IntermediateField ℚ K)
--     [∀ i, NumberField (F i)] :
--     NumberField (s.sup F : IntermediateField ℚ K) where
--   to_finiteDimensional := by
--     classical
--     induction s using Finset.induction with
--     | empty =>
--         rw [Finset.sup_empty]
--         infer_instance
--     | insert i s hi h =>
--         rw [Finset.sup_insert]
--         exact IntermediateField.finiteDimensional_sup (F i) (s.sup F)

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
      refine Ideal.ramificationIdx_sup_eq_one ℚ K F₁ F₂ p P₁ P₂ P Q ?_ ?_ hp'
      · have hP₁ : P₁ ≠ ⊥ := under_ne_bot (𝓞 F₁) hP
        rw [over_def P₁ p, ← Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP₁]
        apply (not_dvd_discr_iff_forall_liesOver _ (𝓞 F₁)
          (Nat.prime_iff_prime_int.mp hp)).mp <| hF i (Finset.mem_insert_self i s)
        · infer_instance
        · infer_instance
      · have hP₂ : P₂ ≠ ⊥ := under_ne_bot (𝓞 F₂) hP
        rw [over_def P₂ p, ← Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP₂]
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


/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!

# Decomposition and Inertia fields

In this file, we develop Hilbert Theory on the splitting of prime ideals in a Galois extension.

Let `L/K` be a Galois extension of fields. Let `A` and `B` be subrings of `K` `L` respectively with
`A` integrally closed, `K` fraction field of `A`, `L` fraction field of `B` and `B` the integral
closure of `A` in `L`.

For `P` a prime ideal of `B`, the decomposition field `D` of `P` in `L/K` is the subfield of
elements of `L` fixed by the decomposition group, that the stabilizer, of `P` in `Gal(L/K)` and
the inertia field `E` of `P` in `L/K` is the subfield of elements of `L` fixed by the inertia
group of `P` in `Gal(L/K)`.

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

variable [MulSemiringAction Gal(L/K) B]

variable [FiniteDimensional K L] [IsGaloisGroup Gal(L/K) A B] [IsDedekindDomain A]
  [IsDedekindDomain B] [Module.Finite A B] [Module.IsTorsionFree A B] [P.IsMaximal]
  [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]

variable (D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D]

include K P in
theorem IsDecompositionField.rank_left (hp : p ≠ ⊥) :
    Module.finrank D L = p.ramificationIdxIn B * p.inertiaDegIn B := by
  rw [← IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L, card_stabilizer_eq p hp]

include P in
theorem IsDecompositionField.rank_right [Algebra K D] [IsScalarTower K D L] [p.IsMaximal]
    [IsGalois K L] (hp : p ≠ ⊥) :
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
  rw [← IsGaloisGroup.card_eq_finrank (inertia Gal(L/K) P) E L,
    card_inertia_eq_ramificationIdxIn p hp]

include P in
theorem IsInertiaField.rank_right [Algebra K E] [IsScalarTower K E L] [p.IsMaximal] [IsGalois K L]
    (hp : p ≠ ⊥) :
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
    [IsScalarTower K D E] [IsScalarTower K E L] [IsScalarTower K D L] [p.IsMaximal] [IsGalois K L]
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
  [IsScalarTower 𝓞D B L]

include K L D in
theorem primesOver [hP : P.IsPrime] [Finite (stabilizer Gal(L/K) P)] [IsIntegrallyClosed 𝓞D]
    [Algebra.IsIntegral 𝓞D B] (𝓟D : Ideal 𝓞D) [hD : P.LiesOver 𝓟D] :
    primesOver 𝓟D B = {P} := by
  have := IsGaloisGroup.of_isFractionRing (stabilizer Gal(L/K) P) 𝓞D B D L
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hP, hD⟩, ?_⟩
  rintro Q ⟨_, _⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝓟D P Q (stabilizer Gal(L/K) P)
  exact σ.prop

variable [FiniteDimensional K L] [IsGalois K L] [IsDedekindDomain A] [IsDedekindDomain B]
  [Module.Finite A B] [Module.IsTorsionFree A B] [IsDedekindDomain 𝓞D] (𝓟D : Ideal 𝓞D)
  [𝓟D.IsMaximal] [P.IsMaximal] [P.LiesOver 𝓟D] [Module.Finite 𝓞D B] [Module.IsTorsionFree 𝓞D B]
  [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]

include K L P D in
theorem ramficationIdxIn_eq_inertiaDegIn_eq (hp : p ≠ ⊥) (hP : 𝓟D ≠ ⊥) :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B ∧
      inertiaDegIn 𝓟D B = p.inertiaDegIn B := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B := .of_isFractionRing _ _ _ D L
  have : p.ramificationIdxIn B * p.inertiaDegIn B ≤ 𝓟D.ramificationIdxIn B * 𝓟D.inertiaDegIn B := by
    have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hP B (stabilizer Gal(L/K) P)
    rw [primesOver K L P D 𝓞D, Set.ncard_singleton, one_mul] at this
    rw [this, IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L,
      IsDecompositionField.rank_left A K L P D hp]
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · sorry
  · refine Nat.le_of_mul_le_mul_right (this.trans ?_) ?_
    refine Nat.mul_le_mul_left _ ?_
    sorry
    sorry
  · sorry
  · refine Nat.le_of_mul_le_mul_left (this.trans ?_) ?_
    refine Nat.mul_le_mul_right _ ?_
    sorry
    sorry






#exit
  refine ⟨le_antisymm ?_ <| Nat.eq_of_mul_eq_mul_right
    (this.trans <| Nat.mul_eq_mul_left ?_ ?_) ?_,
    le_antisymm ?_ <| Nat.eq_of_mul_eq_mul_left (this.trans <| Nat.mul_le_mul_right ?_ ?_) ?_⟩

#exit

variable [Algebra A 𝓞D]
include K L D P in
theorem IsDecompositionRing.ramificationIdxIn [𝓟D.LiesOver p] [p.IsMaximal] (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B := by
  have : 𝓟D ≠ ⊥ := by
    sorry
--    apply Ideal.ne_bot_of_liesOver_of_ne_bot hp 𝓟D
  refine (Nat.eq_eq_of_mul_le_mul ?_ ?_ ?_ ?_
    (ramficationIdxIn_mul_inertiaDegIn A K L P D 𝓞D 𝓟D hp this).symm.le).1
  · rw [ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
      ramificationIdxIn_eq_ramificationIdx _ P (stabilizer Gal(L/K) P)]
    exact IsDedekindDomain.ramificationIdx_le_ramificationIdx _ _ _ hp
  · rw [inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
      inertiaDegIn_eq_inertiaDeg _ P (stabilizer Gal(L/K) P)]
    exact inertiaDeg_le_inertiaDeg p 𝓟D P
  · exact Nat.pos_of_ne_zero <| ramificationIdxIn_ne_zero Gal(L/K) hp
  · exact Nat.pos_of_ne_zero <| inertiaDegIn_ne_zero Gal(L/K)

end IsDecompositionField

end splitting

#lint

#exit

variable (𝓞D : Type*) [CommRing 𝓞D] [Algebra 𝓞D B]

/--
Let `A ⊆ B` be an extension of rings and let `P` be a prime ideal of `B `. The decomposition ring
of `P` is the subring of elements of `B` fixed the decomposition subgroup of `P`, that is the
stabilizer, of `P` in `B ≃ₐ[A] B`.
-/
@[mk_iff]
class IsDecompositionRing extends
    IsGaloisGroup (stabilizer (B ≃ₐ[A] B) P) 𝓞D B

variable (𝓞E : Type*) [CommRing 𝓞E] [Algebra 𝓞E B]

/--
Let `A ⊆ B` be an extension of rings and let `P` be a prime ideal of `B `. The inertia ring
of `P` is the subring of elements of `B` fixed the inertia subgroup of `P` in `B ≃ₐ[A] B`.
-/
@[mk_iff]
class IsInertiaRing extends
    IsGaloisGroup (inertia (B ≃ₐ[A] B) P) 𝓞E B

variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L] [Algebra B L]
  [IsScalarTower A B L] [IsIntegralClosure B A L] [SMulDistribClass Gal(L/K) B L]
  [IsFractionRing B L]

/--
Let `L/K` be a Galois extension of fields. Let `A` and `B` be subrings of `K` `L` respectively with
`A` integrally closed, `K` fraction field of `A`, `L` fraction field of `B` and `B` the integral
closure of `A` in `L`. For `P` an ideal of `B`, the stabilizer of `P` in `B ≃ₐ[A] B` is
isomorphic to the stabilizer of `P` in `Gal(L/K)`.
-/
abbrev stabilizerEquivOfIsFractionRing [FaithfulSMul B L] [Algebra.IsAlgebraic K L] :
    stabilizer (B ≃ₐ[A] B) P ≃* stabilizer Gal(L/K)  P :=
  stabilizerEquiv P (galRestrict A K L B).symm
    (fun _ _ ↦ by
      apply FaithfulSMul.algebraMap_injective B L
      simp [algebraMap.smul, AlgEquiv.smul_def, galRestrict_symm_algebraMap_apply])

/--
Let `L/K` be a Galois extension of fields. Let `A` and `B` be subrings of `K` `L` respectively with
`A` integrally closed, `K` fraction field of `A`, `L` fraction field of `B` and `B` the integral
closure of `A` in `L`. For `P` an ideal of `B`, the inertia subgroup of `P` in `B ≃ₐ[A] B` is
isomorphic to the inertia subgroup of `P` in `Gal(L/K)`.
-/
abbrev inertiaEquivOfIsFractionRing [FaithfulSMul B L] [Algebra.IsAlgebraic K L] :
    inertia (B ≃ₐ[A] B) P ≃* inertia Gal(L/K)  P :=
  inertiaEquiv P (galRestrict A K L B).symm
    (fun _ _ ↦ by
      apply FaithfulSMul.algebraMap_injective B L
      simp [algebraMap.smul, AlgEquiv.smul_def, galRestrict_symm_algebraMap_apply])

/--
If `D` is the decomposition field of `P` in `L/K` and `𝓞D` is such that `D` is the fraction
field of `𝓞D`. Then `𝓞D` is the decomposition ring of `P` in `L/K`.
This cannot be an instance since Lean cannot infer `D`.
-/
theorem IsDecompositionRing.of_isDecompositionField [Algebra.IsAlgebraic K L] [Algebra 𝓞D D]
    [IsFractionRing 𝓞D D] [Algebra.IsIntegral 𝓞D B] [IsIntegrallyClosed 𝓞D] [Algebra 𝓞D L]
    [IsScalarTower 𝓞D B L] [IsScalarTower 𝓞D D L] [IsDecompositionField K L P D] :
    IsDecompositionRing A P 𝓞D where
  toIsGaloisGroup :=
    have := IsGaloisGroup.of_isFractionRing (stabilizer Gal(L/K) P) 𝓞D B D L
    IsGaloisGroup.of_mulEquiv (stabilizerEquivOfIsFractionRing A K L P) (by simp)

/--
If `E` is the inertia field of `P` in `L/K` and `𝓞E ⊆ E` is such that `E` is the fraction
field of `𝓞E`. Then `𝓞E` is the decomposition ring of `P` in `L/K`.
This cannot be an instance since Lean cannot infer `E`.
-/
theorem IsInertiaRing.of_isInertiaField [Algebra.IsAlgebraic K L] [Algebra 𝓞E E]
    [IsFractionRing 𝓞E E] [Algebra.IsIntegral 𝓞E B] [IsIntegrallyClosed 𝓞E] [Algebra 𝓞E L]
    [IsScalarTower 𝓞E B L] [IsScalarTower 𝓞E E L] [IsInertiaField K L P E] :
    IsInertiaRing A P 𝓞E where
  toIsGaloisGroup :=
    have := IsGaloisGroup.of_isFractionRing (inertia Gal(L/K) P) 𝓞E B E L
    IsGaloisGroup.of_mulEquiv (inertiaEquivOfIsFractionRing A K L P) (by simp)

open NumberField in
/--
If the number field `D` is the decomposition field of `P` in `L/K`, then its ring of integers
is the decomposition ring of `P` in `L/K`.
-/
instance [Algebra.IsAlgebraic K L] [NumberField K] [NumberField L] [NumberField D]
    (P : Ideal (𝓞 L)) [IsDecompositionField K L P D] :
    IsDecompositionRing (𝓞 K) P (𝓞 D) := .of_isDecompositionField (𝓞 K) K L P D (𝓞 D)

open NumberField in
/--
If the number field `E` is the inertia field of `P` in `L/K`, then its ring of integers
is the inertia ring of `P` in `L/K`.
-/
instance [Algebra.IsAlgebraic K L] [NumberField K] [NumberField L] [NumberField E]
    (P : Ideal (𝓞 L)) [IsInertiaField K L P E] :
    IsInertiaRing (𝓞 K) P (𝓞 E) := .of_isInertiaField (𝓞 K) K L P E (𝓞 E)

end Basic

/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.FieldTheory.Finite.GaloisField

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

variable [MulSemiringAction Gal(L/K) B] [FiniteDimensional K L] [IsGaloisGroup Gal(L/K) A B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B] [Module.IsTorsionFree A B]
  [P.IsMaximal] [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]

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
  [Module.Finite A B] [Module.IsTorsionFree A B] [IsDedekindDomain 𝓞D] [Module.Finite 𝓞D B]
  [Module.IsTorsionFree 𝓞D B] [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
  [𝓟D.IsMaximal] [P.IsMaximal] [p.IsMaximal]

include K L P D in
private theorem ramficationIdxIn_eq_inertiaDegIn_eq (hp : p ≠ ⊥) (hP : 𝓟D ≠ ⊥)
    (h₀ : 𝓟D.ramificationIdxIn B ≤ p.ramificationIdxIn B)
    (h₁ : 𝓟D.inertiaDegIn B ≤ p.inertiaDegIn B) :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B ∧ inertiaDegIn 𝓟D B = p.inertiaDegIn B := by
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

variable [Algebra A 𝓞D] [Module.IsTorsionFree A 𝓞D] [IsScalarTower A 𝓞D B] [𝓟D.LiesOver p]

include K L D P in
theorem ramificationIdxIn_eq (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B := by
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
theorem inertiaDegIn_eq [IsIntegrallyClosed 𝓞E] [Algebra.IsIntegral 𝓞E B] [P.IsMaximal]
    [𝓟E.IsMaximal] [Finite (inertia Gal(L/K) P)] [IsGalois (𝓞E ⧸ 𝓟E) (B ⧸ P)]
    [FiniteDimensional (𝓞E ⧸ 𝓟E) (B ⧸ P)] :
    inertiaDegIn 𝓟E B = 1 := by
  have : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  rw [inertiaDegIn_eq_inertiaDeg 𝓟E P (inertia Gal(L/K) P), inertiaDeg_algebraMap,
    ← IsGalois.card_aut_eq_finrank,
    ← Nat.card_congr (Quotient.stabilizerQuotientInertiaEquiv (inertia Gal(L/K) P) 𝓟E P).toEquiv]
  simp

variable [FiniteDimensional K L] [IsGalois K L] [Algebra.IsIntegral A B] [Algebra.IsIntegral 𝓞E B]

include K L E P in
theorem inertiaDeg_eq [IsIntegrallyClosed A] [IsIntegrallyClosed 𝓞E] [Algebra A 𝓞E]
    [IsScalarTower A 𝓞E B] [𝓟E.LiesOver p] [P.IsMaximal] [𝓟E.IsMaximal]
    [p.IsMaximal] [IsGalois (𝓞E ⧸ 𝓟E) (B ⧸ P)] [FiniteDimensional (𝓞E ⧸ 𝓟E) (B ⧸ P)] :
    inertiaDeg p 𝓟E = p.inertiaDegIn B := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  have := inertiaDeg_algebra_tower p 𝓟E P
  rwa [← inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
    ← inertiaDegIn_eq_inertiaDeg 𝓟E P (inertia Gal(L/K) P), inertiaDegIn_eq K L P E 𝓞E, mul_one,
    eq_comm] at this

variable [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]
  [IsDedekindDomain 𝓞E] [Module.Finite 𝓞E B] [Module.IsTorsionFree 𝓞E B]

include L K P E in
theorem ramificationIdxIn_eq [P.IsMaximal] [𝓟E.IsMaximal] [IsGalois (𝓞E ⧸ 𝓟E) (B ⧸ P)]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟E B = p.ramificationIdxIn B := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  have : 𝓟E ≠ ⊥ := by
    rw [over_def P 𝓟E]
    exact under_ne_bot 𝓞E <| ne_bot_of_liesOver_of_ne_bot hp _
  have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn this B (inertia Gal(L/K) P)
  rwa [primesOver_eq_singleton K L P E 𝓞E, Set.ncard_singleton, one_mul, inertiaDegIn_eq K L P E,
    mul_one, card_inertia_eq_ramificationIdxIn p hp] at this

variable [Algebra A 𝓞E] [Module.IsTorsionFree A 𝓞E] [IsScalarTower A 𝓞E B] [𝓟E.LiesOver p]

include K L E P in
theorem ramificationIdx_eq [𝓟E.IsMaximal] [P.IsMaximal] [IsGalois (𝓞E ⧸ 𝓟E) (B ⧸ P)]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] (hp : p ≠ ⊥) :
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
    simp [algebraMap.smul, fixingSubgroupEquiv_symm_apply_apply]
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
    simp [algebraMap.smul, fixingSubgroupEquiv_symm_apply_apply]
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
    rw [algebraMap.smul, inv_smul_eq_iff, AlgEquiv.smul_def, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply 𝓞F F L, (mem_fixingSubgroup_iff _ _).mp hσ]
    exact SetLike.coe_mem _

variable [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B] [Module.IsTorsionFree A B]
  [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L]
  [IsScalarTower A B L] [IsDedekindDomain 𝓞F] [Algebra A 𝓞F] [IsIntegralClosure B 𝓞F L]

variable [CommRing 𝓞D] [IsDedekindDomain 𝓞D] [Algebra 𝓞D D] [IsFractionRing 𝓞D D] [Algebra A 𝓞D]
  [Module.IsTorsionFree A 𝓞D] [Algebra 𝓞D B] [Module.Finite 𝓞D B] [Module.IsTorsionFree 𝓞D B]
  [IsScalarTower A 𝓞D B] [Algebra 𝓞D L] [IsScalarTower 𝓞D D L] [IsScalarTower 𝓞D B L]
  [IsScalarTower A 𝓞D D] [IsIntegralClosure 𝓞D A D]

variable [IsIntegralClosure 𝓞F A F] [IsScalarTower A 𝓞F F] [Module.Finite 𝓞F B]
  [Module.IsTorsionFree 𝓞F B] [IsScalarTower A 𝓞F B]

include 𝓞D P in
theorem le_isDecompositionField_iff [p.IsMaximal] [P.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] [Algebra.IsSeparable (𝓞F ⧸ 𝓟F) (B ⧸ P)]
    [𝓟F.IsMaximal] (hp : p ≠ ⊥) :
    F ≤ D ↔ ramificationIdx (algebraMap A 𝓞F) p 𝓟F = 1 ∧ inertiaDeg p 𝓟F = 1 := by
  have hF : 𝓟F ≠ ⊥ := by
    rw [over_def P 𝓟F]
    exact under_ne_bot 𝓞F <| ne_bot_of_liesOver_of_ne_bot hp _
  have : 𝓟F.LiesOver p := LiesOver.tower_bot P 𝓟F p
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
    have : Module.IsTorsionFree 𝓞F 𝓞D := Module.IsTorsionFree.of_faithfulSMul 𝓞D 𝓞F B
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

theorem isInertiaField_le_iff [P.IsPrime] :
    E ≤ F ↔ ramificationIdx (algebraMap 𝓞F B) 𝓟F P = Module.finrank K F := by
  sorry

variable [CommRing 𝓞E] [IsDedekindDomain 𝓞E] [Algebra 𝓞E E] [IsFractionRing 𝓞E E] [Algebra A 𝓞E]
  [Module.IsTorsionFree A 𝓞E] [Algebra 𝓞E B] [Module.Finite A 𝓞E] [Module.Finite 𝓞E B]
  [Module.IsTorsionFree 𝓞E B] [IsScalarTower A 𝓞E B] [Algebra 𝓞E L] [IsScalarTower 𝓞E E L]
  [IsScalarTower 𝓞E B L] [IsScalarTower A 𝓞E E] [IsIntegralClosure 𝓞E A E]

attribute [local instance] Ideal.Quotient.field

include 𝓞E P in
theorem le_isInertiaField_iff [P.IsMaximal] [𝓟F.IsMaximal]
    -- [PerfectField (B ⧸ P)]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    [Algebra.IsSeparable (𝓞F ⧸ 𝓟F) (B ⧸ P)]
    (hp : p ≠ ⊥) :
    F ≤ E ↔ ramificationIdx (algebraMap A 𝓞F) p 𝓟F = 1 := by
  have : 𝓟F.LiesOver p := LiesOver.tower_bot P 𝓟F p
  have hF : 𝓟F ≠ ⊥ := by
    rw [over_def P 𝓟F]
    exact under_ne_bot 𝓞F <| ne_bot_of_liesOver_of_ne_bot hp _
  refine ⟨?_, ?_⟩
  · intro h
    have : Algebra.IsSeparable (A ⧸ p) (B ⧸ P) := by
      have : p.IsMaximal := sorry
      have : Finite (A ⧸ p) := sorry
      have : Finite (B ⧸ P) := sorry
      exact Algebra.IsAlgebraic.isSeparable_of_perfectField
    let : Algebra 𝓞F 𝓞E := (galRestrict' A 𝓞F 𝓞E (inclusion h)).toRingHom.toAlgebra
    have :  IsScalarTower 𝓞F 𝓞E B := by
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
    have : IsGalois (𝓞E ⧸ 𝓟E) (B ⧸ P) := by
      have : p.IsMaximal := sorry
      have : Finite (A ⧸ p) := sorry
      have : Finite (B ⧸ P) := sorry
      exact GaloisField.instIsGaloisOfFinite
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

#lint

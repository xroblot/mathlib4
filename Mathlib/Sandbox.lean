module

public import Mathlib.NumberTheory.DirichletCharacter.Basic

@[to_additive]
theorem Subgroup.relIndex_mul_index' {G : Type*} [Group G] (H K : Subgroup G) :
    (H.relIndex K) * K.index = (H ⊓ K).index := by
  rw [Subgroup.relIndex, ← Subgroup.index_map_subtype, Subgroup.subgroupOf_map_subtype]


@[expose] public section

variable {G : Type*} (M : Type*) [CommGroup G] [Finite G] [CommMonoid M]
  [hM : HasEnoughRootsOfUnity M (Monoid.exponent G)]

namespace CommGroup

theorem card_subgroupOrderIsoSubgroupMonoidHom_eq_index (A : Subgroup G) :
    Nat.card (subgroupOrderIsoSubgroupMonoidHom G M A).ofDual = A.index := by
  rw [Subgroup.index_eq_card, ← card_subgroupOrderIsoSubgroupMonoidHom M A]

theorem relIndex_subgroupOrderIsoSubgroupMonoidHom (A B : Subgroup G) :
    (subgroupOrderIsoSubgroupMonoidHom G M B).ofDual.relIndex
      (subgroupOrderIsoSubgroupMonoidHom G M A).ofDual = A.relIndex B := by
  rw [← mul_left_inj' B.index_ne_zero_of_finite, Subgroup.relIndex_mul_index',
    ← card_subgroupOrderIsoSubgroupMonoidHom_eq_index M,
    ← card_subgroupOrderIsoSubgroupMonoidHom_eq_index M, ← Subgroup.relIndex_sup_right,
    ← ofDual_inf, ← OrderIso.map_inf, Subgroup.relIndex,
    ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe _).toEquiv, Subgroup.index_mul_card]
  exact OrderDual.ofDual_le_ofDual.mpr <| (OrderIso.le_iff_le _).mpr inf_le_right

end CommGroup

namespace MulChar

variable {M : Type*} {R : Type*} [CommMonoid M] [CommRing R] [Finite M]
  [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)]

theorem card_subgroupOrderIsoSubgroupMulChar_eq_index (H : Subgroup Mˣ) :
    Nat.card (subgroupOrderIsoSubgroupMulChar M R H).ofDual = H.index := by
  rw [Subgroup.index_eq_card, ← card_subgroupOrderIsoSubgroupMulChar R H]

theorem relIndex_subgroupOrderIsoSubgroupMulChar (H K : Subgroup Mˣ) :
    (subgroupOrderIsoSubgroupMulChar M R K).ofDual.relIndex
      (subgroupOrderIsoSubgroupMulChar M R H).ofDual = H.relIndex K := by
  have := CommGroup.relIndex_subgroupOrderIsoSubgroupMonoidHom R H K
  rwa [← Subgroup.relIndex_map_map_of_injective _ _
    (f := mulEquivToUnitHom.symm.toMonoidHom) mulEquivToUnitHom.symm.injective] at this

end MulChar

namespace DirichletCharacter

variable (R : Type*) [CommMonoidWithZero R] (n : ℕ)

example (a : ℕ) : Subgroup (DirichletCharacter R n) where
  carrier := {χ | χ.primitiveCharacter a = 1}
  mul_mem' := sorry
  one_mem' := by
    have : NeZero n := sorry
    rw [Set.mem_setOf_eq, primitiveCharacter_one]
    
  inv_mem' := sorry

end DirichletCharacter

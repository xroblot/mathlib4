module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.MulChar.Duality
public import Mathlib.Data.ZMod.Coprime
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

@[to_additive]
theorem Subgroup.center_eq_top_of_isMulCommutative (G : Type*) [Group G] [IsMulCommutative G] :
    Subgroup.center G = ⊤ :=
  (eq_top_iff' (center G)).mpr fun x ↦ mem_center_iff.mpr fun y ↦ mul_comm' y x

open Subgroup in
@[to_additive]
theorem commutator_eq_bot_of_isMulCommutative (G : Type*) [Group G] [IsMulCommutative G] :
    commutator G = ⊥ :=
  (commutator_eq_bot_iff_center_eq_top G).mpr <| center_eq_top_of_isMulCommutative G

@[to_additive]
instance {G : Type*} [Group G] [IsMulCommutative G] (H : Subgroup G) :
    H.Normal :=
  Subgroup.Normal.of_commutator_le G <| commutator_eq_bot_of_isMulCommutative G ▸ bot_le

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

theorem apply_ne_zero_iff_isUnit {R : Type*} [CommMonoid R] {R' : Type*} [CommMonoidWithZero R']
    [Nontrivial R'] (χ : MulChar R R') (a : R) :
    χ a ≠ 0 ↔ IsUnit a :=
  ⟨by simpa using (map_nonunit χ (a := a)).mt, fun h ↦ Units.ne_zero (χ.toUnitHom h.unit)⟩

theorem apply_eq_zero_iff_not_isUnit {R : Type*} [CommMonoid R] {R' : Type*} [CommMonoidWithZero R']
    [Nontrivial R'] (χ : MulChar R R') {a : R} :
    χ a = 0 ↔ ¬ IsUnit a := by
  rw [← (apply_ne_zero_iff_isUnit χ a).not, ne_eq, not_not]

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

variable {R : Type*} [CommMonoidWithZero R] {n : ℕ}

theorem apply_ne_zero_iff [Nontrivial R] (χ : DirichletCharacter R n) (a : ℤ) :
    χ a ≠ 0 ↔ IsCoprime a n := by
  rw [MulChar.apply_ne_zero_iff_isUnit, ZMod.coe_int_isUnit_iff_isCoprime, isCoprime_comm]

theorem apply_eq_zero_iff [Nontrivial R] (χ : DirichletCharacter R n) (a : ℤ) :
    χ a = 0 ↔ ¬ IsCoprime a n := by
  rw [← (apply_ne_zero_iff χ a).not, ne_eq, not_not]

theorem changeLevel_eq_cast_of_dvd' (χ : DirichletCharacter R n) {m : ℕ} (hm : n ∣ m) {a : ℤ}
    (ha : IsCoprime a m) : changeLevel hm χ a = χ a := by
  rw [← ZMod.coe_unitOfIsCoprime _ ha, changeLevel_eq_cast_of_dvd _ hm, ZMod.coe_unitOfIsCoprime,
    ZMod.cast_intCast hm]

theorem primitiveCharacter_apply_of_isCoprime (χ : DirichletCharacter R n) {a : ℤ}
    (ha : IsCoprime a n) :
    χ.primitiveCharacter a = χ a := by
  rw [← changeLevel_eq_cast_of_dvd' χ.primitiveCharacter χ.conductor_dvd_level ha,
    changeLevel_primitiveCharacter]

theorem conductor_changeLevel [NeZero n] (χ : DirichletCharacter R n) {m : ℕ} [NeZero m]
    (hm : n ∣ m) :
    ((changeLevel hm) χ).conductor = χ.conductor := by
  have h : ((changeLevel hm) χ).conductor ∣ χ.conductor := by
    refine conductor_dvd_of_mem_conductorSet ((changeLevel hm) χ)
      ⟨χ.conductor_dvd_level.trans hm, χ.primitiveCharacter, ?_⟩
    rw [χ.primitiveCharacter.changeLevel_trans χ.conductor_dvd_level,
      changeLevel_primitiveCharacter]
  apply dvd_antisymm h
  refine conductor_dvd_of_mem_conductorSet _
    ⟨h.trans χ.conductor_dvd_level, ((changeLevel hm) χ).primitiveCharacter, ?_⟩
  apply changeLevel_injective hm
  rw [← changeLevel_trans, changeLevel_primitiveCharacter]

theorem primitiveCharacter_changeLevel [Nontrivial R] [NeZero n] {m : ℕ} [NeZero m] (hm : n ∣ m)
    (χ : DirichletCharacter R n) (a : ℤ) :
    (changeLevel hm χ).primitiveCharacter a = χ.primitiveCharacter a := by
  by_cases ha : IsCoprime a χ.conductor
  · have : changeLevel (Nat.dvd_lcm_left _ _) (changeLevel hm χ).primitiveCharacter =
        changeLevel (Nat.dvd_lcm_right _ _)  χ.primitiveCharacter := by
      apply changeLevel_injective (m := m)
      rw [← changeLevel_trans, ← changeLevel_trans, changeLevel_primitiveCharacter,
        χ.primitiveCharacter.changeLevel_trans χ.conductor_dvd_level,
        changeLevel_primitiveCharacter]
      rw [conductor_changeLevel, Nat.lcm_self]
      exact χ.conductor_dvd_level.trans hm
    have := DFunLike.congr_fun this (a : ZMod _)
    rwa [changeLevel_eq_cast_of_dvd', changeLevel_eq_cast_of_dvd'] at this
    all_goals
    rwa [conductor_changeLevel, Nat.lcm_self]
  · rw [(apply_eq_zero_iff _ _).mpr ha, (apply_eq_zero_iff _ _).mpr
      (by rwa [conductor_changeLevel])]

variable (R n) in
def subgroupOfMapToOne [Nontrivial R] {a : ℤ} (ha : IsCoprime a n) :
    Subgroup (DirichletCharacter R n) where
  carrier := {χ | χ a = 1}
  mul_mem' hχ hψ := by rw [Set.mem_setOf, MulChar.mul_apply, hχ, hψ, one_mul]
  one_mem' := by
    rw [Set.mem_setOf_eq, MulChar.one_apply ((ZMod.coe_int_isUnit_iff_isCoprime a n).mpr ha.symm)]
  inv_mem' hχ := by rw [Set.mem_setOf_eq, MulChar.inv_apply_eq_inv, hχ, Ring.inverse_one]

@[simp]
theorem mem_subgroupOfMapToOne_iff [Nontrivial R] {a : ℤ} (ha : IsCoprime a n)
    {χ : DirichletCharacter R n} :
    χ ∈ subgroupOfMapToOne R n ha ↔ χ a = 1 := Iff.rfl

variable (R n) in
noncomputable def subgroupOfPrimitiveMapToOne [NeZero n] [Nontrivial R] (p : ℕ)
    [hp : Fact p.Prime] :
    Subgroup (DirichletCharacter R n) :=
  (subgroupOfMapToOne R (n / p ^ n.factorization p) (a := p)
    (Nat.isCoprime_iff_coprime.mpr <| Nat.coprime_ordCompl hp.out (NeZero.ne n))).map
      (changeLevel (Nat.ordCompl_dvd n p))

@[simp]
theorem mem_subgroupOfPrimitiveMapToOne_iff [NeZero n] [Nontrivial R] (p : ℕ) [hp : Fact p.Prime]
    (χ : DirichletCharacter R n) :
    χ ∈ subgroupOfPrimitiveMapToOne R n p ↔ χ.primitiveCharacter p = 1 := by
  have : NeZero (n / p ^ n.factorization p) := ⟨(Nat.ordCompl_pos p (NeZero.ne n)).ne'⟩
  rw [subgroupOfPrimitiveMapToOne]
  refine ⟨?_, ?_⟩
  · rintro ⟨ψ, hψ, rfl⟩
    rw [← Int.cast_natCast, primitiveCharacter_changeLevel, primitiveCharacter_apply_of_isCoprime,
      hψ]
    exact Nat.isCoprime_iff_coprime.mpr <| Nat.coprime_ordCompl hp.out (NeZero.ne n)
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have : χ.conductor ∣ n / p ^ n.factorization p := by
        apply Nat.dvd_ordCompl_of_dvd_not_dvd χ.conductor_dvd_level
        simp [← hp.out.coprime_iff_not_dvd, ← Nat.isCoprime_iff_coprime,
          ← apply_ne_zero_iff (χ := χ.primitiveCharacter), h]
      exact changeLevel this χ.primitiveCharacter
    · dsimp only
      rw [SetLike.mem_coe, mem_subgroupOfMapToOne_iff, changeLevel_eq_cast_of_dvd',
        Int.cast_natCast, h]
      exact Nat.isCoprime_iff_coprime.mpr <| Nat.coprime_ordCompl hp.out (NeZero.ne n)
    · rw [← changeLevel_trans, changeLevel_primitiveCharacter]

#exit
    rw [SetLike.mem_coe, mem_subgroupOfMapToOne_iff] at hψ


    rw [changeLevel_trans]
    rw [changeLevel_eq_cast_of_dvd']
    have := primitiveCharacter_apply_of_isCoprime (changeLevel (Nat.ordCompl_dvd n p) ψ) (a := p) ?_
    simp only [Int.cast_natCast] at this

    sorry
  · intro h

    refine ⟨?_, ?_⟩


    sorry


#exit

variable {R n}



theorem apply_ne_zero_iff [Nontrivial R] (χ : DirichletCharacter R n) (a : ℤ) :
    χ a ≠ 0 ↔ IsCoprime a n := by
  rw [MulChar.ne_zero_iff_isUnit, ZMod.coe_int_isUnit_iff_isCoprime, isCoprime_comm]

theorem apply_eq_zero_iff [Nontrivial R] (χ : DirichletCharacter R n) (a : ℤ) :
    χ a = 0 ↔ ¬ IsCoprime a n := by
  rw [← (apply_ne_zero_iff χ a).not, ne_eq, not_not]





theorem primitiveCharacter_inv_apply [Nontrivial R] [NeZero n] (χ : DirichletCharacter R n)
    (a : ℤ) :
    χ⁻¹.primitiveCharacter a = χ.primitiveCharacter⁻¹ a := by
  by_cases ha : IsCoprime a χ.conductor
  · have : χ⁻¹.primitiveCharacter =
        changeLevel (by rw [χ.conductor_inv]) χ.primitiveCharacter⁻¹ := by
      apply changeLevel_injective (conductor_dvd_level _)
      rw [changeLevel_primitiveCharacter, ← changeLevel_trans, map_inv,
        changeLevel_primitiveCharacter]
    have := DFunLike.congr_fun this (a : ZMod _)
    rw [this, changeLevel_eq_cast_of_dvd']
    rwa [χ.conductor_inv]
  · rw [(apply_eq_zero_iff χ⁻¹.primitiveCharacter a).mpr,
      (apply_eq_zero_iff χ.primitiveCharacter⁻¹ a).mpr ha]
    rwa [conductor_inv]

theorem primitive_mul_apply {n m : ℕ} (χ₁ : DirichletCharacter R n) (χ₂ : DirichletCharacter R m)
    {a : ℤ} (ha : IsCoprime a (Nat.lcm n m)) :
    primitive_mul χ₁ χ₂ a = χ₁ a * χ₂ a := by
  rw [primitive_mul, primitiveCharacter_apply_of_isCoprime _ ha, mul, MulChar.mul_apply,
    changeLevel_eq_cast_of_dvd' _ _ ha, changeLevel_eq_cast_of_dvd' _ _ ha]

theorem primitiveCharacter_mul_eq [NeZero n] (χ ψ : DirichletCharacter R n) :
    changeLevel (Nat.dvd_lcm_left _ _) (χ * ψ).primitiveCharacter =
      changeLevel (Nat.dvd_lcm_right _ _)
        (primitive_mul χ.primitiveCharacter ψ.primitiveCharacter) := by
  have h₁ : χ.conductor.lcm ψ.conductor ∣ n :=
    Nat.lcm_dvd (conductor_dvd_level _) (conductor_dvd_level _)
  have h₂ : (χ * ψ).conductor.lcm (χ.primitiveCharacter.mul ψ.primitiveCharacter).conductor ∣ n :=
    Nat.lcm_dvd (conductor_dvd_level _) <| dvd_trans (conductor_dvd_level _) <| h₁
  apply changeLevel_injective h₂
  rw [← changeLevel_trans, ← changeLevel_trans, changeLevel_primitiveCharacter, primitive_mul,
    changeLevel_trans _ (conductor_dvd_level _) h₁, changeLevel_primitiveCharacter,
    mul, map_mul, ← changeLevel_trans, ← changeLevel_trans, changeLevel_primitiveCharacter,
    changeLevel_primitiveCharacter]

theorem primitiveCharacter_mul_apply [NeZero n] (χ ψ : DirichletCharacter R n) {a : ℤ}
    (ha : IsCoprime a (χ.conductor.lcm ψ.conductor)) :
    (χ * ψ).primitiveCharacter a = χ.primitiveCharacter a * ψ.primitiveCharacter a := by
  have h := DFunLike.congr_fun (primitiveCharacter_mul_eq χ ψ) (a : ZMod _)
  rwa [changeLevel_eq_cast_of_dvd', changeLevel_eq_cast_of_dvd', primitive_mul_apply _ _ ha] at h
  all_goals
  exact ha.of_isCoprime_of_dvd_right <| Int.natCast_dvd_natCast.mpr <|
    Nat.lcm_dvd (conductor_mul_dvd_lcm_conductor χ ψ) (conductor_dvd_level _)

theorem primitiveCharacter_mul_apply_eq_one [NeZero n] [Nontrivial R]
    {χ ψ : DirichletCharacter R n} {a : ℤ}
    (hχ : χ.primitiveCharacter a = 1) (hψ : ψ.primitiveCharacter a = 1) :
    (χ * ψ).primitiveCharacter a = 1 := by
  have ha : IsCoprime a (χ.conductor.lcm ψ.conductor) := by
    have haχ : IsCoprime a χ.conductor := (apply_ne_zero_iff χ.primitiveCharacter a).mp
      (by simp [hχ])
    have haψ : IsCoprime a ψ.conductor := (apply_ne_zero_iff ψ.primitiveCharacter a).mp
      (by simp [hψ])
    have := IsCoprime.mul_right haχ haψ
    refine IsCoprime.of_isCoprime_of_dvd_right this ?_
    rw [Int.ofNat_mul_ofNat]
    rw [Int.natCast_dvd_natCast]
    exact Nat.lcm_dvd_mul χ.conductor ψ.conductor
  rw [primitiveCharacter_mul_apply χ ψ ha, hχ, hψ, mul_one]

variable (R n) in
theorem primitiveCharacter_one_apply [NeZero n] (a : ℤ) :
    primitiveCharacter (1 : DirichletCharacter R n) a = 1 := by
  rw [primitiveCharacter_one, MulChar.one_apply]
  rw [ZMod.coe_int_isUnit_iff_isCoprime, conductor_one, Int.natCast_one]
  exact isCoprime_one_left

example [NeZero n] [Nontrivial R] (a : ℤ) : Subgroup (DirichletCharacter R n) where
  carrier := {χ | χ.primitiveCharacter a = 1}
  mul_mem' := primitiveCharacter_mul_apply_eq_one
  one_mem' := by exact primitiveCharacter_one_apply R n a
  inv_mem' hχ := by
    rw [Set.mem_setOf_eq, primitiveCharacter_inv_apply, MulChar.inv_apply_eq_inv, hχ,
      Ring.inverse_one]

#exit

theorem primitive_mul_apply_eq_one [Nontrivial R] {n m : ℕ} (χ₁ : DirichletCharacter R n)
    (χ₂ : DirichletCharacter R m) (a : ℤ)
    (h₁ : χ₁ a = 1) (h₂ : χ₂ a = 1) :
    primitive_mul χ₁ χ₂ a = 1 := by
  have ha₁ : IsCoprime a n := (apply_ne_zero_iff χ₁ a).mp (by simp [h₁])
  have ha₂ : IsCoprime a m := (apply_ne_zero_iff χ₂ a).mp (by simp [h₂])
  rw [primitive_mul_apply _ _ a, h₁, h₂, mul_one]
  have := IsCoprime.mul_right ha₁ ha₂
  apply IsCoprime.of_isCoprime_of_dvd_right this
  rw [Int.ofNat_mul_ofNat]
  rw [Int.natCast_dvd_natCast]
  exact Nat.lcm_dvd_mul n m



example (χ ψ : DirichletCharacter R n) (a : ℤ) :
    (χ * ψ).primitiveCharacter a =
      (χ.primitiveCharacter.mul ψ.primitiveCharacter).primitiveCharacter a := by

  sorry

theorem apply_ne_zero_iff (χ : DirichletCharacter R n) (a : ℤ) :
    χ a ≠ 0 ↔ IsCoprime a n := by
  sorry



theorem primitiveCharacter_mul_apply_eq_one [Nontrivial R] [NeZero n]
    (χ ψ : DirichletCharacter R n) (a : ℤ)
    (hχ : χ.primitiveCharacter a = 1) (hψ : ψ.primitiveCharacter a = 1) :
    (χ * ψ).primitiveCharacter a = 1 := by
  -- χ'(a) ≠ 0 donc IsCoprime a f_χ
  have hχ_cop : IsCoprime a χ.conductor := by
    rw [← χ.primitiveCharacter.apply_ne_zero_iff R]
    simp [hχ]
  -- de même pour ψ
  have hψ_cop : IsCoprime a ψ.conductor := by
    rw [← ψ.primitiveCharacter.apply_ne_zero_iff R]
    simp [hψ]
  -- IsCoprime a f_{χψ} par le Lemme 3
  have hχψ_cop : IsCoprime a (χ * ψ).conductor := by
    have := IsCoprime.mul_right hχ_cop hψ_cop
    apply IsCoprime.of_isCoprime_of_dvd_right this
    have := conductor_mul_dvd_lcm_conductor χ ψ
    rw [Int.ofNat_mul_ofNat]
    rw [Int.natCast_dvd_natCast]
    refine this.trans ?_
    exact Nat.lcm_dvd_mul χ.conductor ψ.conductor
  -- conclusion par changeLevel_eq_cast_of_dvd
  -- rw [← (χ * ψ).primitiveCharacter.apply_ne_zero_iff R] at hχψ_cop
  rw [← zap] at hχ
  rw [← zap _ (conductor_mul_dvd_lcm_conductor χ ψ)]



theorem zap {R : Type*} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n) {m : ℕ}
    (hm : n ∣ m) {a : ℤ} (ha : IsCoprime a m) :
    changeLevel hm χ a = χ a := by
  rw [← ZMod.coe_unitOfIsCoprime _ ha, changeLevel_eq_cast_of_dvd _ hm, ZMod.coe_unitOfIsCoprime,
    ZMod.cast_intCast hm]

theorem toto (χ : DirichletCharacter R n) (a : ℤ) (ha : IsCoprime a n) :
    χ.primitiveCharacter a = χ a := by
  have := χ.primitiveCharacter.zap χ.conductor_dvd_level ha
  rwa [changeLevel_primitiveCharacter, eq_comm] at this

theorem step1 {R : Type*} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n) {m : ℕ}
    (ψ : DirichletCharacter R m) (a : ℤ) (ha : IsCoprime a (n.lcm m)) :
    χ.mul ψ a = χ a * ψ a := by
  unfold mul
  rw [MulChar.mul_apply, zap _ _ ha, zap _ _ ha]

example {R : Type*} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n) {m : ℕ}
    (ψ : DirichletCharacter R m) (a : ℤ) (ha : IsCoprime a (n.lcm m)) :
    χ.primitive_mul ψ a = χ a * ψ a := by
  unfold primitive_mul
  rw [toto, step1]
  · exact ha
  · exact ha

example [NeZero n] (a : ℤ) : Subgroup (DirichletCharacter R n) where
  carrier := {χ | χ.primitiveCharacter a = 1}
  mul_mem' {χ ψ} hχ hψ := by
    rw [Set.mem_setOf] at hχ hψ ⊢
    have := conductor_mul_dvd_lcm_conductor χ ψ
    rw [← zap _ this]

    let ν := χ.primitiveCharacter.mul ψ.primitiveCharacter
    have : IsCoprime a (χ.conductor.lcm ψ.conductor) := sorry
    rw [← ZMod.coe_unitOfIsCoprime _ sorry]



    have : ν a = 1 := by
      unfold ν mul
      rw [MulChar.mul_apply]

    have := conductor_mul_dvd_lcm_conductor χ ψ

    rw [MulChar.mul_apply, hχ, hψ, one_mul]



  one_mem' := by
    rw [Set.mem_setOf_eq, primitiveCharacter_one, MulChar.one_apply]
    refine (ZMod.isUnit_iff_coprime a (conductor 1)).mpr ?_
    rw [conductor_one]
    exact Nat.gcd_one_right a
  inv_mem' := sorry

end DirichletCharacter

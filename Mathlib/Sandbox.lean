/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Int
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Analysis.Complex.Order

/-!
# Discriminants of quadratic fields

Statements of the next PR, with `sorry`ed proofs.
-/

@[expose] public section

theorem NumberField.InfinitePlace.mk_surjective (K : Type*) [Field K] :
    Function.Surjective (mk : (K →+* ℂ) → NumberField.InfinitePlace K) :=
  fun w ↦ ⟨w.embedding, w.mk_embedding⟩

theorem Squarefree.isUnit_of_pow {M : Type*} [Monoid M] {x : M} {n : ℕ} (hn : 2 ≤ n)
    (h : Squarefree (x ^ n)) : IsUnit x := by
  by_contra!
  grind [h.eq_zero_or_one_of_pow_of_not_isUnit this]

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R]

theorem range_lift {a b : R} {A : Type*} [Ring A] [Algebra R A] {u : A} (h : u * u = a • 1 + b • u) :
    (lift ⟨u, h⟩).range = Algebra.adjoin R {u} := by
  sorry

theorem omega_pow_two_eq_add {a b : R} :
    ω ^ 2 = a • (1 : QuadraticAlgebra R a b) + b • ω := by
  rw [sq, omega_mul_omega_eq_add]

/-- Equal parameters give the same quadratic algebra, as an isomorphism which is the identity
on `re` and `im`. -/
@[simps]
def equivOfEq {a b a' b' : R} (ha : a = a') (hb : b = b') :
    QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R a' b' where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := by ext <;> simp [ha, hb]
  map_add' _ _ := by ext <;> simp
  commutes' _ := by ext <;> simp

end QuadraticAlgebra

section PR42554

open Algebra Module QuadraticAlgebra

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

theorem Algebra.discr_quadraticAlgebra (a b : R) :
    Algebra.discr R (basis a b) = QuadraticAlgebra.discr a b := by
  sorry

variable [StrongRankCondition R] [IsQuadraticExtension R A]
theorem IsQuadraticExtension.exists_algEquiv_quadraticAlgebra :
    ∃ (a b : R), Nonempty (A ≃ₐ[R] QuadraticAlgebra R a b) := by
  sorry

end PR42554

/-! ### For `Mathlib/RingTheory/Discriminant.lean` -/

open  QuadraticAlgebra NumberField

variable {D d : ℤ}

/-! ### Pure arithmetic, for `Mathlib/NumberTheory/FundamentalDiscriminant.lean` -/

namespace Int

theorem IsFundamentalDiscr.eq_one_of_isSquare {D : ℤ} (h : IsFundamentalDiscr D)
    (h' : IsSquare D) : D = 1 := by
  have h_main {r : ℤ} (hr : Squarefree (r * r)) : r * r = 1 := by
    grind [isUnit_iff.mp <| Squarefree.isUnit_of_pow le_rfl (pow_two r ▸ hr)]
  obtain ⟨r, rfl⟩ := h'
  obtain h | h := isFundamentalDiscr_iff_squarefree.mp h
  · exact h_main h.2
  · obtain ⟨s, rfl⟩ : Even r := by
      grind [prime_two.dvd_mul.mp <| dvd_trans (by norm_num : _) <| dvd_iff_emod_eq_zero.mpr h.1]
    rw [show (s + s) * (s + s) / 4 = s * s by grind] at h
    grind

theorem isIntegrallyClosed_iff {a b : ℤ} :
      IsIntegrallyClosed (QuadraticAlgebra ℤ a b) ↔ Int.IsFundamentalDiscr (discr a b) := by
  sorry

theorem isIntegralClosure_iff {a b : ℤ} :
    IsIntegralClosure (QuadraticAlgebra ℤ a b) ℤ (QuadraticAlgebra ℚ a b) ↔
      Int.IsFundamentalDiscr (discr a b) := by
  sorry

-- theorem IsFundamentalDiscr.not_isSquare (h : IsFundamentalDiscr D) (h1 : D ≠ 1) :
--    ¬ IsSquare D := sorry

theorem IsFundamentalDiscr.discr_ediv_four_emod_four (h : IsFundamentalDiscr D) :
    discr (D / 4) (D % 4) = D := by
  have : (D % 4) ^ 2 = D % 4 := by grind [h.1]
  rw [discr_def, this, add_comm, mul_ediv_add_emod]

-- theorem not_isSquare_ratCast (h : ¬ IsSquare d) : ¬ IsSquare (d : ℚ) := sorry

end Int

/-! ### Auxiliary results on quadratic algebras -/

namespace QuadraticAlgebra

variable {a b : ℤ}

-- theorem algebra_discr_basis : Algebra.discr ℤ (basis a b) = discr a b := sorry

-- instance {a b : ℚ} : CharZero (QuadraticAlgebra ℚ a b) := by
--  infer_instance

/-- This is `instIsQuadraticExtensionRat` of #42554, stated here so that the statements below
elaborate. The `Fact` is what makes it fire: when `QuadraticAlgebra ℚ a b` is a field, its
`Algebra ℚ`-structure is inferred as `algebraRat`, not as `instAlgebra`, so the unconditional
instance of #42554 does not apply. -/
instance {a b : ℚ} : Algebra.IsQuadraticExtension ℚ (QuadraticAlgebra ℚ a b) := sorry

end QuadraticAlgebra

/-! ### Abstract quadratic fields -/

instance NumberField.of_isQuadraticExtension (K : Type*) [Field K] [CharZero K]
    [Algebra.IsQuadraticExtension ℚ K] : NumberField K where

variable (K : Type*) [Field K] [CharZero K] [h : Algebra.IsQuadraticExtension ℚ K]

instance : Algebra.IsQuadraticExtension ℤ (𝓞 K) where
  finrank_eq_two' := by rw [RingOfIntegers.rank, h.finrank_eq_two]

variable {K}

theorem NumberField.discr_eq_quadraticAlgebra_discr {a b : ℤ} (f : 𝓞 K ≃+* QuadraticAlgebra ℤ a b) :
    discr K = QuadraticAlgebra.discr a b := by
  rw [← discr_eq_discr K ((basis a b).map f.toIntAlgEquiv.symm), Module.Basis.coe_map,
    RingEquiv.symm_toIntAlgEquiv, AlgEquiv.coe_toLinearEquiv, ← Algebra.discr_eq_discr_of_algEquiv,
    ← Algebra.discr_quadraticAlgebra]
  rfl

noncomputable def algEquivOfRingEquiv {a b : ℤ} (f : 𝓞 K ≃+* QuadraticAlgebra ℤ a b) :
    K ≃ₐ[ℚ] QuadraticAlgebra ℚ a b :=
  (IsFractionRing.ringEquivOfRingEquiv f).equivRatAlgEquiv _ _

variable (K)

theorem NumberField.isFundamentalDiscr_discr : Int.IsFundamentalDiscr (discr K) := by
  obtain ⟨a, b, ⟨f⟩⟩ := IsQuadraticExtension.exists_algEquiv_quadraticAlgebra ℤ (𝓞 K)
  rw [discr_eq_quadraticAlgebra_discr f.toRingEquiv]
  exact  Int.isIntegrallyClosed_iff.mp <| IsIntegrallyClosed.of_equiv f.toRingEquiv

theorem NumberField.nonempty_algEquiv_ringOfIntegers :
    Nonempty (𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ (discr K / 4) (discr K % 4)) := by
  obtain ⟨a, b, ⟨f⟩⟩ := IsQuadraticExtension.exists_algEquiv_quadraticAlgebra ℤ (𝓞 K)
  refine ⟨f.trans (Nonempty.some ?_)⟩
  rw [nonempty_algEquiv_int_iff, (isFundamentalDiscr_discr K).discr_ediv_four_emod_four,
    discr_eq_quadraticAlgebra_discr f.toRingEquiv]

/-- Every quadratic field is `ℚ(√(discr K))`. -/
theorem NumberField.nonempty_algEquiv_quadraticAlgebra_discr :
    Nonempty (K ≃ₐ[ℚ] QuadraticAlgebra ℚ (discr K : ℚ) 0) := by
  obtain ⟨a, b, ⟨f⟩⟩ := IsQuadraticExtension.exists_algEquiv_quadraticAlgebra ℤ (𝓞 K)
  exact ⟨(algEquivOfRingEquiv f.toRingEquiv).trans <|
    (algEquivDiscrZero (a : ℚ) (b : ℚ)).trans <|
      QuadraticAlgebra.equivOfEq (by rw [Int.discr_intCast, discr_eq_quadraticAlgebra_discr
        f.toRingEquiv]) rfl⟩

theorem NumberField.discr_ne_one : discr K ≠ 1 := by
  by_contra! h
  obtain ⟨a, b, ⟨f⟩⟩ := IsQuadraticExtension.exists_algEquiv_quadraticAlgebra ℤ (𝓞 K)
  exact Int.isDomain_iff.mp (f.symm.toMulEquiv.isDomain _)
    (discr_eq_quadraticAlgebra_discr f.toRingEquiv ▸ h ▸ IsSquare.one)

/-- `√(discr K)` lies in `K`. -/
theorem NumberField.exists_sq_eq_discr : ∃ x : K, x ^ 2 = discr K := by
  let e := (nonempty_algEquiv_quadraticAlgebra_discr K).some
  exact ⟨e.symm ω, by simp [← map_pow, omega_pow_two_eq_add]⟩

theorem NumberField.not_isSquare_discr : ¬ IsSquare (discr K) :=
  (Int.IsFundamentalDiscr.eq_one_of_isSquare (isFundamentalDiscr_discr K)).mt <| discr_ne_one K

/-- This instance is what makes `QuadraticAlgebra ℚ ↑(discr K) 0` a field, hence a number field,
without any `Fact` binder at the use sites: it feeds the `b = 0` bridge of `Basic.lean`. -/
instance NumberField.fact_not_isSquare_discr_ratCast :
    Fact (¬ IsSquare (discr K : ℚ)) :=
  ⟨Rat.isSquare_intCast_iff.not.mpr <| not_isSquare_discr K⟩

/-- Stickelberger, for quadratic fields. -/
theorem NumberField.discr_emod_four : discr K % 4 = 0 ∨ discr K % 4 = 1 :=
  (isFundamentalDiscr_discr K).1

/-- The complex embeddings of `ℚ(√d)` correspond to two square roots of `d` in `ℂ`. -/
noncomputable def embeddingEquiv (d : ℚ) :
    (QuadraticAlgebra ℚ d 0 →+* ℂ) ≃ {z : ℂ // z ^ 2 = d} :=
  (RingHom.equivRatAlgHom _ _).trans <| lift.symm.trans
    <| Equiv.subtypeEquivRight <| by simp [pow_two]

@[simp]
theorem embeddingEquiv_symm_apply (d : ℚ) (z : {z : ℂ // z ^ 2 = d}) (x y : ℚ) :
    (embeddingEquiv d).symm z (x • 1 + y • ω) = x + y * z := by
  simp [embeddingEquiv, Rat.smul_def]

@[simp]
theorem embeddingEquiv_symm_apply_omega (d : ℚ) (z : {z : ℂ // z ^ 2 = d}) :
    (embeddingEquiv d).symm z ω = z := by
  simp [embeddingEquiv]

theorem isReal_embeddingEquiv_symm_iff (d : ℚ) [Fact (¬ IsSquare d)]
    (z : {z : ℂ // z ^ 2 = d}) :
    ComplexEmbedding.IsReal ((embeddingEquiv d).symm z) ↔ 0 ≤ d := by
  simp [ComplexEmbedding.isReal_iff, ← (RingHom.equivRatAlgHom _ _).injective.eq_iff,
    QuadraticAlgebra.algHom_ext_iff, Complex.conj_eq_iff_im, ← Complex.sq_nonneg_iff, z.prop,
    ← Complex.ofReal_ratCast]

theorem NumberField.isTotallyReal_iff_discr_pos : IsTotallyReal K ↔ 0 ≤ discr K := by
  obtain ⟨e⟩ := nonempty_algEquiv_quadraticAlgebra_discr K
  rw [isTotallyReal_iff_ofRingEquiv e.toRingEquiv, isTotallyReal_iff,
    (InfinitePlace.mk_surjective _).forall]
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (discr K : ℂ) two_pos
  simp +contextual only [InfinitePlace.isReal_mk_iff, (embeddingEquiv _).forall_congr_left,
    isReal_embeddingEquiv_symm_iff, Int.cast_nonneg_iff, Subtype.forall, Rat.cast_intCast]
  exact Set.Nonempty.forall_const ⟨z, hz⟩

theorem NumberField.isTotallyComplex_iff_discr_neg : IsTotallyComplex K ↔ discr K < 0 := by
  convert_to ¬ IsTotallyReal K ↔ _
  · rw [← nrRealPlaces_eq_zero_iff, ← nrComplexPlaces_eq_zero_iff]
    grind [h.finrank_eq_two ▸ InfinitePlace.card_add_two_mul_card_eq_rank K]
  rw [isTotallyReal_iff_discr_pos, Int.not_le]

variable (F : Type*) [Field F] [CharZero F] [Algebra.IsQuadraticExtension ℚ F]

/-- The discriminant is a complete invariant of quadratic fields. -/
theorem NumberField.nonempty_algEquiv_iff_discr_eq :
    Nonempty (K ≃ₐ[ℚ] F) ↔ discr K = discr F := by
  refine ⟨fun ⟨e⟩ ↦ discr_eq_discr_of_algEquiv K e, fun h ↦ ?_⟩
  obtain ⟨a₁, b₁, ⟨f₁⟩⟩ := IsQuadraticExtension.exists_algEquiv_quadraticAlgebra ℤ (𝓞 K)
  obtain ⟨a₂, b₂, ⟨f₂⟩⟩ := IsQuadraticExtension.exists_algEquiv_quadraticAlgebra ℤ (𝓞 F)
  rw [discr_eq_quadraticAlgebra_discr f₁.toRingEquiv,
    discr_eq_quadraticAlgebra_discr f₂.toRingEquiv] at h
  refine ⟨(algEquivOfRingEquiv f₁.toRingEquiv).trans <|
    AlgEquiv.trans (RingEquiv.equivRatAlgEquiv _ _ ?_) (algEquivOfRingEquiv f₂.toRingEquiv).symm⟩
  exact IsFractionRing.ringEquivOfRingEquiv (nonempty_algEquiv_int_iff.mpr h).some.toRingEquiv

/-! ### The concrete fields `ℚ(√d)`

`QuadraticAlgebra ℚ (d : ℚ) 0` is a field, hence a number field, exactly when `d` is not a
rational square, hence the `[Fact (¬ IsSquare (d : ℚ))]` instance of the results below. -/

section concrete

/-- A squarefree integer other than `1` is not a square in `ℚ`.

This is the source of the `Fact (¬ IsSquare (d : ℚ))` instance that makes `ℚ(√d)` a number
field in the results below. -/
theorem Squarefree.not_isSquare_intCast (hd : Squarefree d) (hd₁ : d ≠ 1) :
    ¬ IsSquare (d : ℚ) := by
  rw [Rat.isSquare_intCast_iff]
  rintro ⟨r, rfl⟩
  obtain h | h := Int.isUnit_iff.mp (Squarefree.isUnit_of_pow le_rfl ((pow_two r) ▸ hd)) <;>
  simp [h] at hd₁ ⊢

/-- When the parameters are already those of the maximal order, the discriminant of the model
is the discriminant of the quadratic algebra. -/
theorem NumberField.discr_quadraticAlgebra_eq {a b : ℤ}
    (h : Int.IsFundamentalDiscr (QuadraticAlgebra.discr a b))
    (h1 : QuadraticAlgebra.discr a b ≠ 1) :
    haveI : Fact (¬ IsSquare (QuadraticAlgebra.discr (a : ℚ) (b : ℚ))) :=
      ⟨by rw [QuadraticAlgebra.Int.discr_intCast, Rat.isSquare_intCast_iff]
          exact h.eq_one_of_isSquare.mt h1⟩
    discr (QuadraticAlgebra ℚ a b) = QuadraticAlgebra.discr a b := by
  have : Fact (¬ IsSquare (QuadraticAlgebra.discr (a : ℚ) (b : ℚ))) :=
    ⟨by rw [QuadraticAlgebra.Int.discr_intCast, Rat.isSquare_intCast_iff]
        exact h.eq_one_of_isSquare.mt h1⟩
  refine discr_eq_quadraticAlgebra_discr ?_
  exact (Int.algEquivIntegralClosure h).toRingEquiv.symm

/-- The discriminant of `ℚ(√d)` is `4 * d` when `d` is squarefree and `d ≡ 2, 3 [ZMOD 4]`.

Note that the `Fact` instance is what tells Mathlib that `QuadraticAlgebra ℚ (d : ℚ) 0` is a
number field, so that its discriminant is defined. It is easily deduced from the other
hypotheses using `Squarefree.not_isSquare_intCast`. -/
theorem NumberField.discr_sqrtd [Fact (¬ IsSquare (d : ℚ))]
    (hd₁ : Squarefree d) (hd₂ : d % 4 = 2 ∨ d % 4 = 3) :
    discr (QuadraticAlgebra ℚ (d : ℚ) 0) = 4 * d := by
  have h₁ : QuadraticAlgebra.discr d 0 = 4 * d := by simp [discr_def]
  have h₂ : (QuadraticAlgebra.discr d 0).IsFundamentalDiscr :=
    h₁ ▸ Int.isFundamentalDiscr_four_mul.mpr ⟨hd₁, hd₂⟩
  simpa [discr_def] using discr_quadraticAlgebra_eq h₂ (by grind)

/-- Every fundamental discriminant other than `1` is the discriminant of a quadratic field.

Note that the `Fact` instance is what tells Mathlib that `QuadraticAlgebra ℚ (D : ℚ) 0` is a
number field, so that its discriminant is defined. It is easily deduced from the other
hypotheses using `Int.IsFundamentalDiscr.eq_one_of_isSquare`. -/
theorem NumberField.discr_quadraticAlgebra [Fact (¬ IsSquare (D : ℚ))]
    (hD : Int.IsFundamentalDiscr D) (hD1 : D ≠ 1) :
    discr (QuadraticAlgebra ℚ (D : ℚ) 0) = D := by
  -- `QuadraticAlgebra ℤ (D / 4) (D % 4)` is the order of discriminant `D`, and `ℚ(√D)` is its
  -- field of fractions: over `ℚ` the two discriminants differ by `2 ^ 2`.
  have hd : QuadraticAlgebra.discr (D / 4) (D % 4) = D := hD.discr_ediv_four_emod_four
  have h_eq : QuadraticAlgebra.discr (D : ℚ) 0 =
      2 ^ 2 * QuadraticAlgebra.discr ((D / 4 : ℤ) : ℚ) ((D % 4 : ℤ) : ℚ) := by
    rw [QuadraticAlgebra.Int.discr_intCast, hd, discr_def]
    ring
  have : Fact (¬ IsSquare (QuadraticAlgebra.discr ((D / 4 : ℤ) : ℚ) ((D % 4 : ℤ) : ℚ))) :=
    ⟨by rw [QuadraticAlgebra.Int.discr_intCast, hd]; exact Fact.out⟩
  let e : QuadraticAlgebra ℚ (D : ℚ) 0 ≃ₐ[ℚ] QuadraticAlgebra ℚ (D / 4 : ℤ) (D % 4 : ℤ) :=
    (nonempty_algEquiv_iff_of_invertible_two.mpr ⟨(isUnit_of_invertible 2).unit, h_eq⟩).some
  rw [discr_eq_discr_of_algEquiv _ e, discr_quadraticAlgebra_eq (by rwa [hd]) (by rwa [hd]), hd]

/-- The discriminant of `ℚ(√d)` is `d` itself when `d` is squarefree and `d ≡ 1 [ZMOD 4]`.

Note that the `Fact` instance is what tells Mathlib that `QuadraticAlgebra ℚ (d : ℚ) 0` is a
number field, so that its discriminant is defined. It is easily deduced from the other
hypotheses using `Squarefree.not_isSquare_intCast`. -/
theorem NumberField.discr_half [Fact (¬ IsSquare (d : ℚ))]
    (hd : Squarefree d) (hd1 : d ≠ 1) (h : d % 4 = 1) :
    discr (QuadraticAlgebra ℚ (d : ℚ) 0) = d :=
  discr_quadraticAlgebra (Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨h, hd⟩)) hd1

end concrete

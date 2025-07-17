/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom, Xavier Roblot
-/
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Extension of fractional ideals

This file defines the extension of a fractional ideal along a ring homomorphism.

## Main definition

* `FractionalIdeal.extended`: Let `A` and `B` be commutative rings with respective localizations
  `IsLocalization M K` and `IsLocalization N L`. Let `f : A →+* B` be a ring homomorphism with
  `hf : M ≤ Submonoid.comap f N`. If `I : FractionalIdeal M K`, then the extension of `I` along
  `f` is `extended L hf I : FractionalIdeal N L`.

## Main results

* `extended_add` says that extension commutes with addition.
* `extended_mul` says that extension commutes with multiplication.

## Tags

fractional ideal, fractional ideals, extended, extension
-/

@[simp]
theorem FractionalIdeal.inv_le_inv_iff {A K : Type*} [CommRing A] [Field K] [IsDedekindDomain A]
    [Algebra A K] [IsFractionRing A K] {I J : FractionalIdeal (nonZeroDivisors A) K} (hI : I ≠ 0)
    (hJ : J ≠ 0) :
    I⁻¹ ≤ J⁻¹ ↔ J ≤ I := by
  rw [le_inv_comm (inv_ne_zero hI) hJ, inv_inv]

-- open nonZeroDivisors in
-- theorem FractionalIdeal.ne_one_iff {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
--     [IsFractionRing R K] (I : FractionalIdeal R⁰ K) :
--     I ≠ 1 ↔ 1 ∉ I ∨ ∃ x ∈ I, x ∉ (algebraMap R K).range := by
--   by_cases hI : I ≤ 1
--   · rw [le_one_iff_exists_coeIdeal] at hI
--     obtain ⟨J, rfl⟩ := hI
--     simp only [ne_eq, coeIdeal_eq_one, Ideal.one_eq_top, Ideal.eq_top_iff_one, mem_coeIdeal,
--       FaithfulSMul.algebraMap_eq_one_iff, exists_eq_right, RingHom.mem_range, not_exists,
--       exists_exists_and_eq_and, IsFractionRing.coe_inj, forall_eq, and_false, exists_const,
--       or_false]
--   · simp_rw [SetLike.not_le_iff_exists, mem_one_iff, not_exists] at hI
--     obtain ⟨x, hx₁, hx₂⟩ := hI
--     have : ∃ x ∈ I, x ∉ (algebraMap R K).range := ⟨x, hx₁, by simpa⟩
--     simp_rw [this, or_true, iff_true]
--     refine ne_of_mem_of_not_mem' hx₁ ?_
--     rwa [mem_one_iff, not_exists]

open IsLocalization FractionalIdeal Submodule

namespace FractionalIdeal

section CommRing

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] {f : A →+* B}
variable {K : Type*} {M : Submonoid A} [CommRing K] [Algebra A K] [IsLocalization M K]
variable (L : Type*) {N : Submonoid B} [CommRing L] [Algebra B L] [IsLocalization N L]
variable (hf : M ≤ Submonoid.comap f N)
variable (I : FractionalIdeal M K) (J : FractionalIdeal M K)

/-- Given commutative rings `A` and `B` with respective localizations `IsLocalization M K` and
`IsLocalization N L`, and a ring homomorphism `f : A →+* B` satisfying `M ≤ Submonoid.comap f N`, a
fractional ideal `I` of `A` can be extended along `f` to a fractional ideal of `B`. -/
def extended (I : FractionalIdeal M K) : FractionalIdeal N L where
  val := span B <| (IsLocalization.map (S := K) L f hf) '' I
  property := by
    have ⟨a, ha, frac⟩ := I.isFractional
    refine ⟨f a, hf ha, fun b hb ↦ ?_⟩
    refine span_induction (fun x hx ↦ ?_) ⟨0, by simp⟩
      (fun x y _ _ hx hy ↦ smul_add (f a) x y ▸ isInteger_add hx hy) (fun b c _ hc ↦ ?_) hb
    · rcases hx with ⟨k, kI, rfl⟩
      obtain ⟨c, hc⟩ := frac k kI
      exact ⟨f c, by simp [← IsLocalization.map_smul, ← hc]⟩
    · rw [← smul_assoc, smul_eq_mul, mul_comm (f a), ← smul_eq_mul, smul_assoc]
      exact isInteger_smul hc

local notation "map_f" => (IsLocalization.map (S := K) L f hf)

lemma mem_extended_iff (x : L) : (x ∈ I.extended L hf) ↔ x ∈ span B (map_f '' I) := by
  constructor <;> { intro hx; simpa }

lemma coe_extended_eq_span : I.extended L hf = span B (map_f '' I) := by
  ext; simp [mem_coe, mem_extended_iff]

@[simp]
theorem extended_zero : extended L hf (0 : FractionalIdeal M K) = 0 :=
  have : ((0 : FractionalIdeal M K) : Set K) = {0} := by ext; simp
  coeToSubmodule_injective (by simp [this, coe_extended_eq_span])

variable {I}

theorem extended_ne_zero [IsDomain K] [IsDomain L] [NoZeroSMulDivisors A K] [NoZeroSMulDivisors B L]
    (hf' : Function.Injective f) (hI : I ≠ 0) :
    extended L hf I ≠ 0 := by
  simp only [ne_eq, ← coeToSubmodule_inj, coe_extended_eq_span, coe_zero, Submodule.span_eq_bot,
    Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    not_forall]
  obtain ⟨x, hx₁, hx₂⟩ : ∃ x ∈ I, x ≠ 0 := by simpa [ne_eq, eq_zero_iff] using hI
  refine ⟨x, hx₁, ?_⟩
  exact (map_ne_zero_iff _ (IsLocalization.map_injective_of_injective' _ _ _ hf hf')).mpr hx₂

@[simp]
theorem extended_eq_zero_iff [IsDomain K] [IsDomain L] [NoZeroSMulDivisors A K]
    [NoZeroSMulDivisors B L] (hf' : Function.Injective f) :
    extended L hf I = 0 ↔ I = 0 := by
  refine ⟨?_, fun h ↦ h ▸ extended_zero _ _⟩
  contrapose!
  exact fun a ↦ extended_ne_zero L hf hf' a

variable (I)

@[simp]
theorem extended_one : extended L hf (1 : FractionalIdeal M K) = 1 := by
  refine coeToSubmodule_injective <| Submodule.ext fun x ↦ ⟨fun hx ↦ span_induction
    ?_ (zero_mem _) (fun y z _ _ hy hz ↦ add_mem hy hz) (fun b y _ hy ↦ smul_mem _ b hy) hx, ?_⟩
  · rintro ⟨b, _, rfl⟩
    rw [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
    exact smul_mem _ _ <| subset_span ⟨1, by simp [one_mem_one]⟩
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨f a, ha, by rw [Algebra.linearMap_apply, Algebra.linearMap_apply, map_eq]⟩

theorem extended_le_one_of_le_one (I : FractionalIdeal M K) (hI : I ≤ 1) :
    extended L hf I ≤ 1 := by
  rw [le_one_iff_exists_coeIdeal] at hI
  obtain ⟨J, rfl⟩ := hI
  intro x hx
  simp [mem_extended_iff, Submodule.mem_span_image_iff_exists_fun] at hx
  obtain ⟨s, hs, c, rfl⟩ := hx
  simp only [val_eq_coe, coe_one]
  refine Submodule.sum_smul_mem _ _ fun x h ↦ ?_
  have := hs x.prop
  simp only [SetLike.mem_coe, mem_coeIdeal] at this
  let a := f this.choose
  have := this.choose_spec.2
  refine ⟨?_, ?_⟩
  use a
  simp
  rw [← this]
  simp
  rw [Algebra.algebraMap_eq_smul_one]

theorem one_le_extended_of_one_le (I : FractionalIdeal M K) (hI : 1 ≤ I) :
    1 ≤ extended L hf I := by
  rw [one_le] at hI ⊢
  rw [mem_extended_iff]
  apply subset_span
  exact ⟨1, hI, by rw [map_one]⟩

theorem extended_add : (I + J).extended L hf = (I.extended L hf) + (J.extended L hf) := by
  apply coeToSubmodule_injective
  simp only [coe_extended_eq_span, coe_add, Submodule.add_eq_sup, ← span_union, ← Set.image_union]
  apply Submodule.span_eq_span
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨i, hi, j, hj, rfl⟩ := (mem_add I J y).mp <| SetLike.mem_coe.mp hy
    rw [RingHom.map_add]
    exact add_mem (Submodule.subset_span ⟨i, Set.mem_union_left _ hi, by simp⟩)
      (Submodule.subset_span ⟨j, Set.mem_union_right _ hj, by simp⟩)
  · rintro _ ⟨y, hy, rfl⟩
    suffices y ∈ I + J from SetLike.mem_coe.mpr <| Submodule.subset_span ⟨y, by simp [this]⟩
    exact hy.elim (fun h ↦ (mem_add I J y).mpr ⟨y, h, 0, zero_mem J, add_zero y⟩)
      (fun h ↦ (mem_add I J y).mpr ⟨0, zero_mem I, y, h, zero_add y⟩)

theorem extended_mul : (I * J).extended L hf = (I.extended L hf) * (J.extended L hf) := by
  apply coeToSubmodule_injective
  simp only [coe_extended_eq_span, coe_mul, span_mul_span]
  refine Submodule.span_eq_span (fun _ h ↦ ?_) (fun _ h ↦ ?_)
  · rcases h with ⟨x, hx, rfl⟩
    replace hx : x ∈ (I : Submodule A K) * (J : Submodule A K) := coe_mul I J ▸ hx
    rw [Submodule.mul_eq_span_mul_set] at hx
    refine span_induction (fun y hy ↦ ?_) (by simp) (fun y z _ _ hy hz ↦ ?_)
      (fun a y _ hy ↦ ?_) hx
    · rcases Set.mem_mul.mp hy with ⟨i, hi, j, hj, rfl⟩
      exact subset_span <| Set.mem_mul.mpr
        ⟨map_f i, ⟨i, hi, by simp⟩, map_f j, ⟨j, hj, by simp⟩, by simp⟩
    · exact map_add map_f y z ▸ Submodule.add_mem _ hy hz
    · rw [Algebra.smul_def, map_mul, map_eq, ← Algebra.smul_def]
      exact smul_mem _ (f a) hy
  · rcases Set.mem_mul.mp h with ⟨y, ⟨i, hi, rfl⟩, z, ⟨j, hj, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨i * j, mul_mem_mul hi hj, by simp⟩

theorem extended_coeIdeal_eq_map {A : Type*} [CommRing A] {B : Type*} [CommRing B]
    {f : A →+* B} {K : Type*} {M : Submonoid A} [CommRing K] [Algebra A K] [IsLocalization M K]
    (L : Type*) {N : Submonoid B} [CommRing L] [Algebra B L] [IsLocalization N L]
    (hf : M ≤ Submonoid.comap f N) (I : Ideal A) :
    (I : FractionalIdeal M K).extended L hf = (I.map f : FractionalIdeal N L) := by
  rw [Ideal.map, Ideal.span, ← coeToSubmodule_inj, Ideal.submodule_span_eq, coe_coeIdeal,
    IsLocalization.coeSubmodule_span, coe_extended_eq_span]
  refine Submodule.span_eq_span ?_ ?_
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact Submodule.subset_span
      ⟨f a, Set.mem_image_of_mem f ha, by rw [Algebra.linearMap_apply, IsLocalization.map_eq hf a]⟩
  · rintro _ ⟨_ , ⟨a, ha, rfl⟩, rfl⟩
    exact Submodule.subset_span
      ⟨algebraMap A K a, mem_coeIdeal_of_mem M ha, IsLocalization.map_eq hf a⟩

end CommRing

section FractionRing

open scoped nonZeroDivisors

variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K] (B : Type*) [CommRing B] [IsDomain B] (L : Type*) [Field L]
  [Algebra B L] [IsFractionRing B L] [Algebra A B] [NoZeroSMulDivisors A B]

-- example (hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰)
--     [Algebra A L] [Algebra K L] [IsScalarTower A B L]
--     [IsScalarTower A K L] (I : FractionalIdeal A⁰ K) :
--     (extended L hs I : Submodule B L).restrictScalars A =
--       Submodule.map (IsScalarTower.toAlgHom A K L) I := by
--   rw [coe_extended_eq_span]

--   sorry

lemma coe_extended_eq_span_algebraMap [Algebra K L] [Algebra A L] [IsScalarTower A B L]
    [IsScalarTower A K L] [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L]
    (I : FractionalIdeal A⁰ K) :
    haveI hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
    I.extended L hs = span B (algebraMap K L '' I) := by
  rw [IsLocalization.algebraMap_eq_map_map_submonoid A⁰ B K L]
  exact coe_extended_eq_span L _ I

theorem le_one_of_extended_le_one
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegrallyClosed A]
    [IsIntegrallyClosed B] [Algebra.IsIntegral A B]
    (I : FractionalIdeal A⁰ K) (hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰)
    (hI : extended L hs I ≤ 1) :
    I ≤ 1 := by
  contrapose! hI
  rw [SetLike.not_le_iff_exists] at hI ⊢
  obtain ⟨x, hx₁, hx₂⟩ := hI
  refine ⟨algebraMap K L x, ?_, ?_⟩
  · have := coe_extended_eq_span_algebraMap B L I
    rw [← FractionalIdeal.mem_coe, this]
    apply subset_span
    exact Set.mem_image_of_mem _ hx₁
  · contrapose! hx₂
    rw [mem_one_iff] at hx₂ ⊢
    rw [← IsIntegrallyClosed.isIntegral_iff] at hx₂ ⊢
    have := isIntegral_trans (R := A) _ hx₂
    have := IsIntegral.tower_bot_of_field this
    exact this

theorem extended_le_one_iff [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L] [IsIntegrallyClosed A]
    [IsIntegrallyClosed B] [Algebra.IsIntegral A B]
    (I : FractionalIdeal A⁰ K) (hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰) :
    extended L hs I ≤ 1 ↔ I ≤ 1 := by
  constructor
  · intro h
    apply le_one_of_extended_le_one B L _ hs h
  · exact fun a ↦ extended_le_one_of_le_one L hs I a

variable (K) in
theorem extended_coeIdeal_eq_map_algebraMap (I : Ideal A) :
    haveI hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
    (I : FractionalIdeal A⁰ K).extended L hs =
      (I.map (algebraMap A B) : FractionalIdeal B⁰ L) :=
  FractionalIdeal.extended_coeIdeal_eq_map _ _ _

variable [IsDedekindDomain A] [IsDedekindDomain B]

theorem extended_inv {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) :
    haveI hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
    extended L hs (f := algebraMap A B) I⁻¹ =
       (extended L hs (f := algebraMap A B) I : FractionalIdeal B⁰ L)⁻¹ := by
  rw [← mul_eq_one_iff_eq_inv₀, ← extended_mul, inv_mul_cancel₀ hI, extended_one]
  exact extended_ne_zero _ _ (FaithfulSMul.algebraMap_injective _ _) hI

theorem one_le_extended_iff [Algebra K L] [Algebra A L] [IsScalarTower A B L]
    [IsScalarTower A K L] (I : FractionalIdeal A⁰ K) [Algebra.IsIntegral A B]
    [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L]
    (hI : I ≠ 0) :
    haveI hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
    1 ≤ extended L hs I ↔ 1 ≤ I := by
  rw [← inv_le_inv_iff, inv_one, ← extended_inv, extended_le_one_iff, inv_le_comm, inv_one]
  exact hI
  exact one_ne_zero
  exact hI
  apply extended_ne_zero
  exact FaithfulSMul.algebraMap_injective _ _
  exact hI
  exact one_ne_zero

theorem extended_eq_one_iff [Algebra K L] [Algebra A L] [IsScalarTower A B L]
    [IsScalarTower A K L] (I : FractionalIdeal A⁰ K) [Algebra.IsIntegral A B]
    [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L]
    (hI : I ≠ 0) :
    haveI hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
    extended L hs I = 1 ↔ I = 1 := by
  rw [le_antisymm_iff, extended_le_one_iff, one_le_extended_iff _ _ _ hI, ← le_antisymm_iff]

theorem extended_injective [Algebra K L] [Algebra A L] [IsScalarTower A B L]
    [IsScalarTower A K L] [Algebra.IsIntegral A B]
    [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L] :
    haveI hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
    Function.Injective (fun I : FractionalIdeal A⁰ K ↦ extended L hs (f := algebraMap A B) I) := by
  intro I J h
  by_cases hI : I = 0
  · have hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
    dsimp only at h
    rw [hI, extended_zero, eq_comm,
      extended_eq_zero_iff _ _ (FaithfulSMul.algebraMap_injective _ _)] at h
    rw [hI, h]
  by_cases hJ : J = 0
  · have hs : A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ := fun _ hx ↦ by simpa using hx
    dsimp only at h
    rw [hJ, extended_zero, extended_eq_zero_iff _ _ (FaithfulSMul.algebraMap_injective _ _)] at h
    rw [hJ, h]
  rwa [← mul_inv_eq_one₀, ← extended_inv _ _ hJ, ← extended_mul, extended_eq_one_iff,
    mul_inv_eq_one₀ hJ] at h
  · exact mul_ne_zero hI (inv_ne_zero hJ)
  · apply extended_ne_zero
    exact FaithfulSMul.algebraMap_injective _ _
    exact hJ

theorem _root_.Ideal.map_algebraMap_injective [Algebra.IsIntegral A B] :
    Function.Injective (fun I : Ideal A ↦ I.map (algebraMap A B)) := by
  let _ : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra A (FractionRing B)
  intro I _ h
  rwa [← coeIdeal_inj (K := FractionRing B), ← extended_coeIdeal_eq_map_algebraMap (FractionRing A),
    ← extended_coeIdeal_eq_map_algebraMap (FractionRing A), (extended_injective _ _).eq_iff,
    coeIdeal_inj] at h

end FractionRing

end FractionalIdeal

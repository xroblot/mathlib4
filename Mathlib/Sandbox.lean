module

public import Mathlib.Algebra.QuadraticAlgebra.Int
public import Mathlib.Algebra.QuadraticAlgebra.Rat
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Data.Nat.Squarefree

@[expose] public section

theorem Nat.forall_prime_iff_two_and_odd {P : ℕ → Prop} :
    (∀ p, Nat.Prime p → P p) ↔ P 2 ∧ ∀ p, Nat.Prime p → Odd p → P p := by
  refine ⟨fun h ↦ ⟨h 2 Nat.prime_two, fun p hp _ ↦ h p hp⟩, fun h p hp ↦ ?_⟩
  obtain rfl | hne := eq_or_ne p 2
  · exact h.1
  · exact h.2 p hp (hp.odd_of_ne_two hne)

/-!
# Scratch: quadratic rings and integral closure

Skeleton following `~/Desktop/Claude/plan_cloture_integrale.md`. `QuadraticAlgebra ℤ a b` IS the
ring-of-integers object; three independent relations to `QA ℚ ↑a ↑b`: structure (§1), density
(§2), maximality (§3). Bridge to the standard form `QA ℚ d 0` in §4, standard forms in §5.
-/

/-- If `algebraMap A B` is injective, `A` is the integral closure of `R` in `B` iff an element
of `B` is integral over `R` exactly when it lies in the image of `A`. -/
theorem isIntegralClosure_iff {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R B] [Algebra A B] [FaithfulSMul A B] :
    IsIntegralClosure A R B ↔ ∀ x : B, IsIntegral R x ↔ ∃ a : A, algebraMap A B a = x :=
  ⟨fun _ _ ↦ IsIntegralClosure.isIntegral_iff,
   fun h ↦ ⟨FaithfulSMul.algebraMap_injective A B, fun {x} ↦ h x⟩⟩

namespace QuadraticAlgebra

open Algebra

namespace Int

variable {a b : ℤ}

/-! ## §3 Maximality — the arithmetic core -/

open Polynomial in
/-- §3.1 pivot (carries all the content): integrality over `ℤ` ⟺ integral trace and norm.
`←` Cayley–Hamilton (`sq_eq_trace_smul_sub_norm`); `→` minpoly of degree ≤ 2. -/
theorem isIntegral_iff {z : QuadraticAlgebra ℚ a b} :
    IsIntegral ℤ z ↔ (∃ t : ℤ, t = trace z) ∧ (∃ n : ℤ, n = norm z) := by
  refine ⟨fun h ↦ ?_, fun ⟨⟨t, ht⟩, ⟨n, hn⟩⟩ ↦ ⟨X ^ 2 - C t * X + C n, by monicity!, ?_⟩⟩
  · have hs : IsIntegral ℤ (star z) := h.map (starRingEnd _).toIntAlgHom
    refine ⟨?_, ?_⟩
    · exact IsIntegrallyClosed.isIntegral_iff.mp <|
        (algebraMap_trace_eq_add_star z ▸ h.add hs).tower_bot
          (FaithfulSMul.algebraMap_injective _ _)
    · exact IsIntegrallyClosed.isIntegral_iff.mp <|
        (algebraMap_norm_eq_mul_star z ▸ h.mul hs).tower_bot
          (FaithfulSMul.algebraMap_injective _ _)
  · simpa only [eval₂_add, eval₂_sub,  eval₂_X_pow, eval₂_mul, eval₂_X, eval₂_C,
      IsScalarTower.algebraMap_apply ℤ ℚ (QuadraticAlgebra ℚ a b), eq_intCast (algebraMap ℤ ℚ),
      ht, hn, ← Algebra.smul_def] using sq_sub_trace_smul_add_norm_eq_zero z

theorem isIntegral_omega :
    IsIntegral ℤ (ω : QuadraticAlgebra ℚ a b) :=
  isIntegral_iff.mpr ⟨by simp, -a, by simp [norm_def]⟩

/-- `im_sq_mul_discr` rearranged, the orientation used by the rewrites below. -/
theorem four_mul_norm_eq {R : Type*} [CommRing R] {a b : R} (z : QuadraticAlgebra R a b) :
    4 * norm z = trace z ^ 2 - discr a b * z.im ^ 2 := by
  linear_combination im_sq_mul_discr z

/-- `discr a b = b² + 4a ≡ 0, 1 [ZMOD 4]` for every `a, b`. -/
theorem discr_mod_four (a b : ℤ) : discr a b % 4 = 0 ∨ discr a b % 4 = 1 := by
  rw [discr_def]; have := Int.sq_emod_four b; omega

open Polynomial in
/-- Witness lemma (shared engine for (ii)⟹ and (iii)⟹): with `p ∣ 2t+b` and `4p² ∣ (2t+b)²−D`,
the element `ζ = (t + ω)/p` is integral (root of `X² − T·X + N`, `T = (2t+b)/p`,
`N = ((2t+b)²−D)/(4p²)`), has `p • ζ = t + ω` in the order's image, yet `ζ ∉` it (`im ζ = 1/p`).
(ii)⟹ and (iii)⟹ differ only in the choice of `t`. -/
theorem exists_unsaturated_of_dvd {d t : ℤ} (hd : d ≠ 0) (hd' : d.natAbs ≠ 1) (h₁ : d ∣ 2 * t + b)
    (h₂ : 4 * d ^ 2 ∣ (2 * t + b) ^ 2 - discr a b) :
    ∃ z : QuadraticAlgebra ℚ a b, IsIntegral ℤ z ∧
      d • z ∈ Set.range (baseChange ℚ a b) ∧ z ∉ Set.range (baseChange ℚ a b) := by
  replace hd : (d : ℚ) ≠ 0 := Rat.num_ne_zero.mp hd
  obtain ⟨s, hs⟩ := h₁
  obtain ⟨v, hv⟩ := h₂
  have ht : trace (t • 1 + ω : QuadraticAlgebra ℚ a b) = d * s := by
    simp only [zsmul_eq_mul, mul_one, map_add, trace_intCast, trace_omega]
    exact_mod_cast hs
  have hn : norm (t • 1 + ω : QuadraticAlgebra ℚ a b) = d ^ 2 * v := by
    rw [← mul_right_inj' four_ne_zero, four_mul_norm_eq]
    simp only [zsmul_eq_mul, mul_one, map_add, trace_intCast, trace_omega, im_add, im_intCast,
      im_omega, zero_add, one_pow, ← mul_assoc, discr_intCast]
    exact_mod_cast hv
  refine ⟨(d : ℚ)⁻¹ • (t • 1 + ω), isIntegral_iff.mpr ⟨⟨s, ?_⟩, ⟨v, ?_⟩⟩, ⟨t • 1 + ω, ?_⟩, ?_⟩
  · rw [map_smul, ht, smul_eq_mul, inv_mul_cancel_left₀ hd]
  · rw [norm_smul, hn, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hd, one_pow, one_mul]
  · rw [map_add, map_smul, map_one, baseChange_omega, ← Int.cast_smul_eq_zsmul ℚ d, smul_smul,
      mul_inv_cancel₀ hd, one_smul]
  · intro ⟨x, hx⟩
    replace hx := congr_arg im hx
    rw [im_smul, im_add, im_smul, im_one, smul_zero, im_omega, zero_add, im_baseChange_apply,
      Int.smul_one_eq_cast, Rat.smul_one_eq_cast, Rat.cast_inv, Rat.cast_intCast,
      ← mul_eq_one_iff_eq_inv₀ (by aesop), ← Int.cast_mul, Int.cast_eq_one,
      Int.mul_eq_one_iff_eq_one_or_neg_one] at hx
    grind

/-- For an integral element, an integer imaginary part forces an integer real part. Via
`z.re • 1 = z - z.im • ω`: `z` and `ω` integral, `z.im ∈ ℤ` ⟹ `z.re • 1` integral, so
`z.re ∈ ℤ` (`mem_of_isIntegral_algebraMap`). -/
theorem re_mem_range_of_im_mem_range {z : QuadraticAlgebra ℚ a b} (h : IsIntegral ℤ z)
    (him : z.im ∈ Set.range (algebraMap ℤ ℚ)) : z.re ∈ Set.range (algebraMap ℤ ℚ) := by
  rw [Set.mem_range, ← IsIntegrallyClosed.isIntegral_iff]
  have : algebraMap ℚ (QuadraticAlgebra ℚ a b) z.re = z - z.im • (ω : QuadraticAlgebra ℚ a b) := by
    rw [eq_sub_iff_add_eq, algebraMap_eq_smul_one, re_smul_add_im_smul]
  rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ (QuadraticAlgebra ℚ a b))
    (FaithfulSMul.algebraMap_injective _ _), IsScalarTower.coe_toAlgHom', this]
  obtain ⟨m, hm⟩ := him
  rw [← hm, IsScalarTower.algebraMap_smul]
  exact h.sub (isIntegral_omega.smul _)

theorem aux {z : QuadraticAlgebra ℚ a b} {x : QuadraticAlgebra ℤ a b} {d : ℤ}
    (hz : IsIntegral ℤ z) (hd : d ≠ 0) (hx : baseChange ℚ a b x = d • z) (him : d ∣ x.im) :
    z ∈ Set.range (baseChange ℚ a b) := by
  suffices z.re ∈ Set.range (algebraMap ℤ ℚ) ∧ z.im ∈ Set.range (algebraMap ℤ ℚ) by
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := this
    refine ⟨u • 1 + v • ω, ?_⟩
    rw [map_add, map_smul, map_smul, map_one, baseChange_omega, ← re_smul_add_im_smul z, ← hu, ← hv,
      IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul]
  have him : z.im ∈ Set.range (algebraMap ℤ ℚ) := by
    obtain ⟨v, hv⟩ := him
    refine ⟨v, ?_⟩
    rw [← smul_right_inj hd, Algebra.smul_def, ← map_mul, ← hv, eq_intCast, ← algebraMap_im_eq,
      algebraMap_eq, hx, im_smul]
  exact ⟨re_mem_range_of_im_mem_range hz him, him⟩

theorem aux₀ {z : QuadraticAlgebra ℚ a b} {x : QuadraticAlgebra ℤ a b} {d : ℤ}
    (hz : IsIntegral ℤ z) (hx : baseChange ℚ a b x = d • z) :
    d ^ 2 ∣ norm x := by
  obtain ⟨-, n, hn⟩ := isIntegral_iff.mp hz
  refine ⟨n, FaithfulSMul.algebraMap_injective ℤ ℚ ?_⟩
  simp_rw [map_mul, ← norm_baseChange, hx, ← Int.cast_smul_eq_zsmul ℚ, norm_smul, ← hn,
    algebraMap_int_eq, eq_intCast, Int.cast_pow]

theorem aux₁ {z : QuadraticAlgebra ℚ a b} {x : QuadraticAlgebra ℤ a b} {d : ℤ}
    (hz : IsIntegral ℤ z) (hx : baseChange ℚ a b x = d • z) :
    d ∣ 2 * x.re + b * x.im := by
  obtain ⟨⟨t, ht⟩, -⟩ := isIntegral_iff.mp hz
  refine ⟨t, ?_⟩
  rw [← Int.cast_inj (α := ℚ), ← trace_def, ← eq_intCast (algebraMap ℤ ℚ), ← trace_baseChange, hx,
    ← Int.cast_smul_eq_zsmul ℚ, map_smul, ← ht,  smul_eq_mul, Int.cast_mul]

theorem aux₂ {z : QuadraticAlgebra ℚ a b} {x : QuadraticAlgebra ℤ a b} {d : ℤ}
    (hz : IsIntegral ℤ z) (hx : baseChange ℚ a b x = d • z) :
    d ^ 2 ∣ discr a b * x.im ^ 2 := by
  obtain ⟨-, ⟨n, hn⟩⟩ := isIntegral_iff.mp hz
  rw [← Int.dvd_neg, ← Int.dvd_add_right (pow_dvd_pow_of_dvd (aux₁ hz hx) 2), ← trace_def,
    ← sub_eq_add_neg, ← four_mul_norm_eq]
  exact Int.dvd_mul_of_dvd_right <| aux₀ hz hx

/-- §1.3(ii) — saturation at an odd prime `p` holds iff `p² ∤ discr a b`. -/
theorem saturated_iff_of_odd (p : ℕ) (hp : p.Prime) (hp' : Odd p) :
    (∀ z : QuadraticAlgebra ℚ a b, IsIntegral ℤ z →
        p • z ∈ Set.range (baseChange ℚ a b) → z ∈ Set.range (baseChange ℚ a b)) ↔
      ¬ (p : ℤ) ^ 2 ∣ discr a b := by
  simp_rw [← Nat.cast_smul_eq_nsmul ℤ]
  let q := (p : ℤ)
  have hq : Prime q := Nat.prime_iff_prime_int.mp hp
  have hq' : Odd q := Odd.natCast hp'
  refine ⟨fun h hd ↦ ?_,  fun h z hz ⟨x, hx⟩ ↦ ?_⟩
  · have h₁ : q ∣ 2 * (-(Int.gcdA 2 p) * b) + b := by
      refine ⟨Int.gcdB 2 p * b, ?_⟩
      rw [Int.neg_mul, Int.mul_neg, neg_add_eq_iff_eq_add, ← mul_assoc, ← mul_assoc, ← add_mul,
          ← Int.gcd_eq_gcd_ab, Int.isCoprime_iff_gcd_eq_one.mp (Int.isCoprime_two_left.mpr hq'),
          Nat.cast_one, one_mul]
    obtain ⟨t, ht₁, ht₂⟩ : ∃ t : ℤ, q ∣ 2 * t + b ∧ (4 * q ^ 2) ∣ (2 * t + b) ^ 2 - discr a b := by
      refine ⟨-(Int.gcdA 2 q) * b, h₁, ?_⟩
      have : IsCoprime 4 (q ^ 2) := by
        rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
        exact (Int.isCoprime_two_left.mpr hq').pow
      refine IsCoprime.mul_dvd this ?_ <| dvd_sub (pow_dvd_pow_of_dvd h₁ 2) hd
      rw [← Int.modEq_iff_dvd, add_sq, mul_pow, show (2 : ℤ) ^ 2 = 4 by norm_num,
        Int.add_assoc, Int.modEq_modulus_mul_add_iff, ← mul_assoc,
        show (2 : ℤ) * 2 = 4 by norm_num, mul_assoc, Int.modEq_modulus_mul_add_iff, discr_def,
        Int.add_modulus_mul_modEq_iff]
    obtain ⟨z, hz₁, hz₂, hz₃⟩ :=
      exists_unsaturated_of_dvd hq.ne_zero (Int.prime_iff_natAbs_prime.mp hq).ne_one ht₁ ht₂
    exact hz₃ (h z hz₁ hz₂)
  · refine aux hz hq.ne_zero hx <| Prime.dvd_of_dvd_pow hq (n := 2) ?_
    contrapose! h
    exact ((Prime.coprime_iff_not_dvd hq).mpr h).pow_left.dvd_of_dvd_mul_right <| aux₂ hz hx

/-- §1.3(iii) — saturation at `2` holds iff `discr a b` is not `4e` with `e` a discriminant. -/
theorem saturated_two_iff :
    (∀ z : QuadraticAlgebra ℚ a b, IsIntegral ℤ z →
        2 • z ∈ Set.range (baseChange ℚ a b) → z ∈ Set.range (baseChange ℚ a b)) ↔
      ¬ ∃ e : ℤ, discr a b = 4 * e ∧ (e % 4 = 0 ∨ e % 4 = 1) := by
  simp_rw [← Nat.cast_smul_eq_nsmul ℤ, show (2 : ℕ) = (2 : ℤ) by rfl]
  refine ⟨fun hsat ⟨e, he, he'⟩ ↦ ?_, fun h z hz ⟨x, hx⟩ ↦ ?_⟩
  · obtain ⟨t, ht₁, ht₂⟩ : ∃ t : ℤ, 2 ∣ 2 * t + b ∧ (4 * 2 ^ 2) ∣ (2 * t + b) ^ 2 - discr a b := by
      obtain ⟨c, rfl⟩ : 2 ∣ b :=
        Int.prime_two.dvd_of_dvd_pow (n := 2) ⟨2 * (e - a), by grind [discr_def]⟩
      obtain _ | _ := he'
      · exact ⟨-c, by lia, by lia⟩
      · exact ⟨1 - c, by lia, by lia⟩
    obtain ⟨z, hz₁, hz₂, hz₃⟩ :=
      exists_unsaturated_of_dvd (d := 2) (by norm_num) (by norm_num) ht₁ ht₂
    exact hz₃ (hsat z hz₁ hz₂)
  · refine aux hz two_ne_zero hx ?_
    by_contra him
    rw [← even_iff_two_dvd, Int.not_even_iff_odd] at him
    obtain ⟨c, rfl⟩ : 2 ∣ b := by
      have := aux₁ hz hx
      rw [Int.dvd_self_mul_add] at this
      exact (Int.isCoprime_two_left.mpr him).dvd_of_dvd_mul_right this
    refine h ⟨c ^ 2 + a, by grind [discr_def], ?_⟩
    have : norm x = (x.re + c * x.im) ^ 2 - (c ^ 2 + a) * x.im ^ 2 := by
      rw [← mul_right_inj' four_ne_zero, four_mul_norm_eq, trace_def, discr_def]
      ring
    have : ((x.re + c * x.im) ^ 2 - (c ^ 2 + a)) % 4 = norm x % 4 := by
      rw [this, Int.emod_sub_cancel_left, Int.mul_emod, Int.sq_emod_four_eq_one_of_odd him, mul_one,
        Int.emod_emod]
    have : (c ^ 2 + a) % 4 = (x.re + c * x.im) ^ 2 % 4 := by
      rw [eq_comm, Int.emod_eq_emod_iff_emod_sub_eq_zero, this, ← Int.dvd_iff_emod_eq_zero]
      exact aux₀ hz hx
    rw [this, Int.sq_emod_four]
    exact Int.emod_two_eq (x.re + c * x.im)

/-- §1.3(i) Recollement — integral closure reduces to per-prime saturation of the order, by
minimal-`N` denominator descent (`N • z ∈ range`, `N > 1` ⟹ take `p ∣ N`). -/
theorem isIntegralClosure_iff_forall_prime :
    IsIntegralClosure (QuadraticAlgebra ℤ a b) ℤ (QuadraticAlgebra ℚ a b) ↔
      ∀ p : ℕ, p.Prime → ∀ z : QuadraticAlgebra ℚ a b, IsIntegral ℤ z →
        p • z ∈ Set.range (baseChange ℚ a b) → z ∈ Set.range (baseChange ℚ a b) := by
  rw [_root_.isIntegralClosure_iff]
  refine ⟨fun H p _ z hz _ ↦ (H z).mp hz, fun H z ↦ ⟨fun hz ↦ ?_, ?_⟩⟩
  · simp_rw [algebraMap_eq, ← Set.mem_range]
    obtain ⟨n, hn, hw⟩ := exists_nat_smul_mem z
    induction n using Nat.strong_induction_on generalizing z with
    | h n h_ind =>
        obtain rfl | h := eq_or_ne n 1
        · rwa [one_smul] at hw
        · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h
          refine H p hp z hz <| h_ind (n / p) (Nat.div_lt_self hn hp.one_lt) _ (hz.nsmul p) ?_ ?_
          · exact (Nat.lt_div_iff_mul_lt' hpn 0).mpr hn
          · rwa [smul_smul, Nat.div_mul_cancel hpn]
  · rintro ⟨w, rfl⟩
    exact (Algebra.IsIntegral.isIntegral w).map (baseChange ℚ a b)

/-- δ — the order `QA ℤ a b` is integral over `ℤ` (free module of rank 2). -/
instance : Algebra.IsIntegral ℤ (QuadraticAlgebra ℤ a b) := Algebra.IsIntegral.of_finite ℤ _

/-- Main result (§1.3), assembled from (i) + (ii) + (iii) + (iv); the `discr a b ≡ 0, 1 [ZMOD 4]`
clause of (iv) is automatic (`discr_mod_four`). -/
theorem isIntegralClosure_iff :
    IsIntegralClosure (QuadraticAlgebra ℤ a b) ℤ (QuadraticAlgebra ℚ a b) ↔
      _root_.Int.IsFundamentalDiscr (discr a b) := by
  rw [isIntegralClosure_iff_forall_prime, Nat.forall_prime_iff_two_and_odd, saturated_two_iff]
  simp_rw +contextual [saturated_iff_of_odd, EuclideanDomain.mod_eq_zero, not_exists,
    not_and, not_or]
  exact (and_iff_right (discr_mod_four a b)).symm

/-- §3.4 — free from §3.3, for whoever wants the `integralClosure` object explicitly. -/
noncomputable def algEquivIntegralClosure (h : _root_.Int.IsFundamentalDiscr (discr a b)) :
    QuadraticAlgebra ℤ a b ≃ₐ[ℤ] integralClosure ℤ (QuadraticAlgebra ℚ a b) :=
  letI := isIntegralClosure_iff.mpr h
  IsIntegralClosure.equiv ℤ (QuadraticAlgebra ℤ a b) (QuadraticAlgebra ℚ a b)
    (integralClosure ℤ (QuadraticAlgebra ℚ a b))

/-! ## §4 Bridge to any ℚ-form with a compatible discriminant — via `mapIntegralClosure`,
no new algebra instance. -/

/-- For any `a' b' : ℚ` whose discriminant equals `discr a b` up to a square unit, `QA ℤ a b`
is the ring of integers of `QA ℚ a' b'` (as a `ℤ`-algebra). Rests only on the discriminant
classification `nonempty_algEquiv_iff_of_invertible_two`; no algebra instance is asserted. -/
noncomputable def algEquivIntegralClosure' (hf : _root_.Int.IsFundamentalDiscr (discr a b))
    {a' b' : ℚ} (h : ∃ u : ℚˣ, discr (a : ℚ) (b : ℚ) = (u : ℚ) ^ 2 * discr a' b') :
    QuadraticAlgebra ℤ a b ≃ₐ[ℤ] integralClosure ℤ (QuadraticAlgebra ℚ a' b') :=
  (algEquivIntegralClosure hf).trans
    ((nonempty_algEquiv_iff_of_invertible_two.mpr h).some.restrictScalars ℤ).mapIntegralClosure

/-! ## §5 Standard forms — corollaries of §3.3 (mod-4 disjunction lives on the ℤ side) -/

/-- `d ≡ 2, 3 [ZMOD 4]`: `ℤ[√d] = QA ℤ d 0` is maximal (`discr = 4d`). -/
theorem isFundamental_sqrtd {d : ℤ} (hd : Squarefree d) (h : d % 4 = 2 ∨ d % 4 = 3) :
    _root_.Int.IsFundamentalDiscr (discr d 0) :=
  _root_.Int.isFundamentalDiscr_iff_squarefree.mpr <| by simpa [discr_def] using ⟨hd, h⟩

/-- `d ≡ 1 [ZMOD 4]`: `ℤ[(1+√d)/2] = QA ℤ ((d-1)/4) 1` is maximal (`discr = d`). -/
theorem isFundamental_half {d : ℤ} (hd : Squarefree d) (h : d % 4 = 1) :
    _root_.Int.IsFundamentalDiscr (discr ((d - 1) / 4) 1) := by
  have : Squarefree (1 + 4 * ((d - 1) / 4)) := by
    rwa [Int.mul_ediv_cancel' (Int.dvd_self_sub_of_emod_eq h), add_sub_cancel]
  exact _root_.Int.isFundamentalDiscr_iff_squarefree.mpr <| by simp [discr_def, this]

end Int

end QuadraticAlgebra

section NumberField

instance {a b : ℚ} [Fact (∀ r, r ^ 2 ≠ a + b * r)] : NumberField (QuadraticAlgebra ℚ a b) where

end NumberField

/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Ring-theoretic properties of quadratic algebras

This file collects ring-theoretic properties of `QuadraticAlgebra R a b` as an `R`-algebra.

## Main results

* `QuadraticAlgebra.polynomial_discr_eq_discr`: the discriminant of the polynomial
  `X ^ 2 - C b * X - C a` equals `discr a b`.
* `QuadraticAlgebra.minpoly_omega`: the minimal polynomial of `ω` over `R` is
  `X ^ 2 - C b * X - C a`.
* `Algebra.trace_quadraticAlgebra_apply` and `Algebra.norm_quadraticAlgebra_apply`:
  `Algebra.trace` and `Algebra.norm` on `QuadraticAlgebra R a b` agree with
  `QuadraticAlgebra.trace` and `QuadraticAlgebra.norm`.
* `Algebra.discr_quadraticAlgebra`: `Algebra.discr R (basis a b)` equals `discr a b`.
-/

public section

open QuadraticAlgebra

variable {R : Type*} [CommRing R] (a b : R)

namespace QuadraticAlgebra

open Polynomial

/-- The discriminant of the polynomial `X ^ 2 - C b * X - C a` is the discriminant `discr a b` of
the quadratic algebra `QuadraticAlgebra R a b`. -/
theorem polynomial_discr_eq_discr :
    (X ^ 2 - C b * X - C a).discr = discr a b := by
  nontriviality R
  rw [discr_of_degree_eq_two (by compute_degree!)]
  simp [discr_def]

theorem aeval_omega_eq_zero :
    aeval (ω : QuadraticAlgebra R a b) (X ^ 2 - C b * X - C a) = 0 := by
  simp [omega_pow_two_eq_add, Algebra.smul_def]

variable {a b} in
/-- There is no nonzero polynomial of degree at most one that vanishes at `ω`. -/
theorem eq_zero_of_aeval_omega_eq_zero {q : R[X]}
    (hq₁ : aeval (ω : QuadraticAlgebra R a b) q = 0) (hq₂ : q.natDegree ≤ 1) :
    q = 0 := by
  obtain ⟨r, s, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hq₂
  obtain ⟨rfl, rfl⟩ : s = 0 ∧ r = 0 := by simpa [QuadraticAlgebra.ext_iff] using hq₁
  rw [map_zero, zero_mul, add_zero]

/-- The minimal polynomial of `ω` over `R` is `X ^ 2 - C b * X - C a`. -/
theorem minpoly_omega :
    minpoly R (ω : QuadraticAlgebra R a b) = X ^ 2 - C b * X - C a := by
  nontriviality R
  refine (minpoly.unique' R ω (by monicity!) (aeval_omega_eq_zero a b) fun q hq ↦ ?_).symm
  refine or_not_of_imp fun h ↦ eq_zero_of_aeval_omega_eq_zero h ?_
  rw [show (X ^ 2 - C b * X - C a : R[X]).degree = 2 by compute_degree!] at hq
  exact natDegree_le_of_degree_le (Order.le_of_lt_succ hq)

end QuadraticAlgebra

namespace Algebra

variable {a b}

/-- The matrix of left multiplication by `z` in the basis `{1, ω}`. -/
theorem leftMulMatrix_quadraticAlgebra (z : QuadraticAlgebra R a b) :
    leftMulMatrix (basis a b) z = !![z.re, a * z.im; z.im, z.re + b * z.im] := by
  ext i j
  fin_cases i <;>
  fin_cases j <;>
  simp [leftMulMatrix_eq_repr_mul]

/-- The algebra trace of `QuadraticAlgebra R a b` is the elementary trace. -/
@[simp]
theorem trace_quadraticAlgebra_apply (z : QuadraticAlgebra R a b) :
    trace R (QuadraticAlgebra R a b) z = QuadraticAlgebra.trace z := by
  rw [trace_eq_matrix_trace (basis a b), leftMulMatrix_quadraticAlgebra,
    Matrix.trace_fin_two_of, trace_def]
  ring

/-- The algebra norm of `QuadraticAlgebra R a b` is the elementary norm. -/
@[simp]
theorem norm_quadraticAlgebra_apply (z : QuadraticAlgebra R a b) :
    norm R z = QuadraticAlgebra.norm z :=
  det_toLinearMap_eq_norm z

/-- The `Algebra.discr` of the standard basis `{1, ω}` is the elementary discriminant. -/
@[simp]
theorem discr_quadraticAlgebra :
    discr R (basis a b) = QuadraticAlgebra.discr a b := by
  rw [discr_def, Matrix.det_fin_two, QuadraticAlgebra.discr_def]
  simp only [traceMatrix_apply, traceForm_apply, trace_quadraticAlgebra_apply, basis_apply_zero,
    basis_apply_one, one_mul, mul_one, omega_mul_omega_eq_mk, QuadraticAlgebra.trace_def, re_one,
    im_one, re_omega, im_omega]
  ring

end Algebra

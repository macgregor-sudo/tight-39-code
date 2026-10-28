/-
Isolated pinned-toolchain port of https://github.com/bjbraams/lean-SCV
Revision: 50392764ae64d75779abbea1396fe93d80b677cc
Original file: ToMathlib/Algebra/Polynomial/OfFn.lean; copied scope: the complete original file.
Original author/copyright holder: Bastiaan J Braams (retained header below).
License: Apache-2.0; unchanged upstream license retained at LICENSES/SCV-Apache-2.0.txt.
Changes: pinned-toolchain compatibility port, public module/import adaptation and attribution comments; see THIRD_PARTY_NOTICES.md#scv-complex-analysis for the public modification record.
Thank you to the lean-SCV author and Lean/Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/
/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.OfFn

/-!
# Reconstruction of polynomials from finite coefficient vectors

The notation `R[X]` denotes `Polynomial R`. Mathlib's linear map `Polynomial.ofFn n` builds
an `R[X]` from `n` coefficients. Adding `X ^ n` gives a monic polynomial; its monicity follows
from `Polynomial.monic_X_pow_add` and `Polynomial.ofFn_degree_lt`.

## Main results

* `Polynomial.ofFn_toFn_eq_of_degree_lt`: Reconstruction below a degree bound, including the
  zero polynomial and the empty coefficient vector.
* `Polynomial.Monic.eq_X_pow_add_ofFn`: Reconstruction of a monic polynomial from its leading
  term and its lower coefficients.
* `Polynomial.coeff_X_pow_add_ofFn_of_lt`: The lower coefficients of the monic construction.
* `Polynomial.natDegree_X_pow_add_ofFn`: Its natural degree over a nontrivial semiring.

These algebraic facts require no topology and apply to arbitrary semirings.

## References

* V. Scheidemann, *Introduction to Complex Analysis in Several Variables*,
  Birkhäuser, 2005 (background on holomorphic functions of several variables).
-/

public section

namespace Polynomial

variable {R : Type*} [Semiring R] [DecidableEq R]

/-- A polynomial of degree below `n` is recovered from its first `n` coefficients, including
when `n = 0` and the polynomial is zero. -/
theorem ofFn_toFn_eq_of_degree_lt {n : ℕ} {p : R[X]} (hp : p.degree < (n : WithBot ℕ)) :
    ofFn n (toFn n p) = p := by
  ext i
  by_cases hi : i < n
  · simp [hi, toFn]
  · rw [ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi)]
    exact (coeff_eq_zero_of_degree_lt (hp.trans_le (by exact_mod_cast Nat.le_of_not_gt hi))).symm

/-- A monic polynomial is its leading power of `X` plus the polynomial of its lower
coefficient vector. -/
theorem Monic.eq_X_pow_add_ofFn {p : R[X]} (hp : p.Monic) :
    p = X ^ p.natDegree + ofFn p.natDegree (toFn p.natDegree p) := by
  rw [ofFn_eq_sum_monomial]
  simp only [toFn, LinearMap.pi_apply, lcoeff_apply, ← C_mul_X_pow_eq_monomial]
  rw [Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i) p.natDegree]
  exact hp.as_sum

/-- Adding the leading monomial leaves every prescribed lower coefficient unchanged. -/
theorem coeff_X_pow_add_ofFn_of_lt {n i : ℕ} (v : Fin n → R) (hi : i < n) :
    (X ^ n + ofFn n v).coeff i = v ⟨i, hi⟩ := by
  simp [coeff_add, coeff_X_pow, hi.ne, ofFn_coeff_eq_val_of_lt v hi]

/-- Over a nontrivial semiring, adding `X ^ n` to a polynomial with `n` prescribed lower
coefficients gives natural degree `n`. -/
theorem natDegree_X_pow_add_ofFn [Nontrivial R] {n : ℕ} (v : Fin n → R) :
    (X ^ n + ofFn n v).natDegree = n := by
  apply natDegree_eq_of_degree_eq_some
  have hlt : (ofFn n v).degree < (X ^ n : R[X]).degree := by
    rw [degree_X_pow]
    exact ofFn_degree_lt v
  rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]

end Polynomial

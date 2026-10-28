module

public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-!
# CHAINMID prototype: the Vandermonde / cumulative step (step 7 tail of DESIGN-v0)

* `sum_antidiagonal_choose_mul_choose` (upper-index Vandermonde):
  `∑_{i+j=n} C(a+i,a)·C(b+j,b) = C(a+b+1+n, a+b+1)`, from `invOneSubPow_add`.
* `cumulative_convolution_choose`: `∑_{n≤N} ∑_{i+j=n} C(a+i,a)·C(b+j,b) = C(N+a+b+2, a+b+2)`.
* `cumulative_convolution_bound`: if `h m ≤ 4·C(m+5,5) + 1540·C(m+4,4)` for all `m`, then
  `∑_{n≤N} ∑_{i+j=n} h i · C(j+55,55) ≤ 4·C(N+62,62) + 1540·C(N+61,61)`
  (56 free variables contribute `multichoose 56 j = C(j+55,55)`).
-/

open Finset PowerSeries

namespace ChainMid

/-- Upper-index Vandermonde identity. -/
theorem sum_antidiagonal_choose_mul_choose (a b n : ℕ) :
    ∑ ij ∈ antidiagonal n, (a + ij.1).choose a * (b + ij.2).choose b =
      (a + b + 1 + n).choose (a + b + 1) := by
  have h := congrArg (fun f : ℤ⟦X⟧ => coeff n f)
    (congrArg Units.val (invOneSubPow_add ℤ (a + 1) (b + 1)))
  simp only [Units.val_mul, show a + 1 + (b + 1) = (a + b + 1) + 1 by omega,
    invOneSubPow_val_succ_eq_mk_add_choose, coeff_mul, coeff_mk] at h
  exact_mod_cast h.symm

/-- Cumulative form: one more hockey-stick summation. -/
theorem cumulative_convolution_choose (a b N : ℕ) :
    ∑ n ∈ range (N + 1), ∑ ij ∈ antidiagonal n, (a + ij.1).choose a * (b + ij.2).choose b =
      (N + a + b + 2).choose (a + b + 2) := by
  simp_rw [sum_antidiagonal_choose_mul_choose]
  have := Nat.sum_range_add_choose N (a + b + 1)
  simp only [show N + (a + b + 1) + 1 = N + a + b + 2 by omega] at this
  rw [← this]
  refine sum_congr rfl fun n _ => ?_
  rw [add_comm (a + b + 1) n]

/-- The all-`N` bound consumed by the jet/colon chain, from a per-degree bound on the
24-variable Hilbert function `h` and 56 free variables. -/
theorem cumulative_convolution_bound (h : ℕ → ℕ)
    (hh : ∀ m, h m ≤ 4 * (m + 5).choose 5 + 1540 * (m + 4).choose 4) (N : ℕ) :
    ∑ n ∈ range (N + 1), ∑ ij ∈ antidiagonal n, h ij.1 * (ij.2 + 55).choose 55 ≤
      4 * (N + 62).choose 62 + 1540 * (N + 61).choose 61 := by
  calc ∑ n ∈ range (N + 1), ∑ ij ∈ antidiagonal n, h ij.1 * (ij.2 + 55).choose 55
      ≤ ∑ n ∈ range (N + 1), ∑ ij ∈ antidiagonal n,
          (4 * ((5 + ij.1).choose 5 * (55 + ij.2).choose 55) +
            1540 * ((4 + ij.1).choose 4 * (55 + ij.2).choose 55)) := by
        refine sum_le_sum fun n _ => sum_le_sum fun ij _ => ?_
        have := Nat.mul_le_mul_right ((ij.2 + 55).choose 55) (hh ij.1)
        rw [add_comm 5 ij.1, add_comm 4 ij.1, add_comm 55 ij.2]
        nlinarith [this]
    _ = 4 * (N + 62).choose 62 + 1540 * (N + 61).choose 61 := by
        simp only [sum_add_distrib, ← mul_sum, cumulative_convolution_choose]

end ChainMid

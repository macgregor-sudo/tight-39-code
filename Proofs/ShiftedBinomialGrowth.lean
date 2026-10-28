module

public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Degree drop between matching shifted binomial bounds

An upper bound for L(N) + B(N+cu) and a matching lower bound for B(N+cl)
are compared at N+cl and N+cu. Monotonicity moves L back to N. Repeated
Pascal bounds the difference of the leading binomials by a fixed multiple
of a binomial of one lower degree. The existing Mathlib choose-to-power
estimate absorbs the remaining shifts into one explicit natural constant.

The proof cancels only a finite natural-number term in extended naturals.
It never subtracts infinities or assumes the desired growth estimate.
All sequence bounds remain hypotheses, independent of any branch model.

First-party proof using Nat.choose_succ_succ, Nat.choose_le_choose and
Nat.choose_add_le_add_one_pow from Mathlib Data/Nat/Choose/{Basic,Bounds}.lean,
plus ENat.add_le_add_iff_right from Data/ENat/Basic.lean. No upstream proof
body is copied. Pin: Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55,
Lean v4.35.0-rc2. Thank you to the Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

namespace ShiftedBinomialGrowth

/-- A fixed shift of a degree-(d+1) binomial costs at most the shift times
a degree-d binomial. This additive form avoids truncated subtraction. -/
theorem choose_add_shift_le (n s d : ℕ) :
    (n + s).choose (d + 1) ≤ n.choose (d + 1) + s * (n + s).choose d := by
  induction s with
  | zero => simp
  | succ s ih =>
    calc
      (n + (s + 1)).choose (d + 1) =
          (n + s).choose d + (n + s).choose (d + 1) := by
        rw [← Nat.add_assoc, Nat.choose_succ_succ']
      _ ≤ (n + s).choose d + (n.choose (d + 1) + s * (n + s).choose d) :=
        Nat.add_le_add_left ih _
      _ = n.choose (d + 1) + (s + 1) * (n + s).choose d := by ring
      _ ≤ n.choose (d + 1) + (s + 1) * (n + (s + 1)).choose d :=
        Nat.add_le_add_left (Nat.mul_le_mul_left (s + 1)
          (Nat.choose_le_choose d (by omega))) _

/-- Matching shifted upper and lower binomial bounds imply an explicit
one-degree-lower bound, even when the sequences take extended-natural values. -/
theorem enat_bound_of_shifted_binomial_bounds
    (L B : ℕ → ℕ∞) (a b d cu cl : ℕ) (hMono : Monotone L)
    (hUpper : ∀ N : ℕ, L N + B (N + cu) ≤
      ((a * (N + cu + (d + 1)).choose (d + 1) +
        b * (N + cu + d).choose d : ℕ) : ℕ∞))
    (hLower : ∀ N : ℕ, ((a * (N + (d + 1)).choose (d + 1) : ℕ) : ℕ∞) ≤
      B (N + cl)) :
    ∀ N : ℕ, L N ≤
      (((a * cl + b) * (cu + cl + 2) ^ d * (N + 1) ^ d : ℕ) : ℕ∞) := by
  intro N
  let A := a * (N + cu + (d + 1)).choose (d + 1)
  let P := (N + cu + cl + (d + 1)).choose d
  let U := a * (N + cu + cl + (d + 1)).choose (d + 1) +
    b * (N + cu + cl + d).choose d
  have hMatched : L N + (A : ℕ∞) ≤ (U : ℕ∞) := by
    calc
      L N + (A : ℕ∞) ≤ L (N + cl) + B (N + cu + cl) :=
        add_le_add (hMono (Nat.le_add_right N cl)) (hLower (N + cu))
      _ ≤ (U : ℕ∞) := by
        simpa only [U, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hUpper (N + cl)
  have hPascal :
      (N + cu + cl + (d + 1)).choose (d + 1) ≤
        (N + cu + (d + 1)).choose (d + 1) + cl * P := by
    simpa only [P, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      choose_add_shift_le (N + cu + (d + 1)) cl d
  have hSmall : (N + cu + cl + d).choose d ≤ P :=
    Nat.choose_le_choose d (by omega)
  have hU : U ≤ A + (a * cl + b) * P := by
    calc
      U ≤ a * ((N + cu + (d + 1)).choose (d + 1) + cl * P) + b * P :=
        Nat.add_le_add (Nat.mul_le_mul_left a hPascal) (Nat.mul_le_mul_left b hSmall)
      _ = A + (a * cl + b) * P := by dsimp [A]; ring
  have hCancel : L N + (A : ℕ∞) ≤ (((a * cl + b) * P : ℕ) : ℕ∞) + (A : ℕ∞) := by
    calc
      L N + (A : ℕ∞) ≤ (U : ℕ∞) := hMatched
      _ ≤ ((A + (a * cl + b) * P : ℕ) : ℕ∞) := ENat.natCast_le_natCast.mpr hU
      _ = (((a * cl + b) * P : ℕ) : ℕ∞) + (A : ℕ∞) := by
        rw [ENat.natCast_add]
        exact add_comm (A : ℕ∞) (((a * cl + b) * P : ℕ) : ℕ∞)
  have hL : L N ≤ (((a * cl + b) * P : ℕ) : ℕ∞) :=
    (ENat.add_le_add_iff_right (ENat.natCast_ne_top A)).mp hCancel
  have hChoose : P ≤ (N + cu + cl + 2) ^ d := by
    simpa only [P, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.choose_add_le_add_one_pow (N + cu + cl + 1) d
  have hLin : N + cu + cl + 2 ≤ (cu + cl + 2) * (N + 1) := by
    have hN : N ≤ (cu + cl + 2) * N := Nat.le_mul_of_pos_left N (by omega)
    calc
      N + cu + cl + 2 ≤ (cu + cl + 2) * N + cu + cl + 2 := by omega
      _ = (cu + cl + 2) * (N + 1) := by ring
  apply hL.trans
  apply ENat.natCast_le_natCast.mpr
  calc
    (a * cl + b) * P ≤ (a * cl + b) * ((cu + cl + 2) * (N + 1)) ^ d :=
      Nat.mul_le_mul_left _ (hChoose.trans (Nat.pow_le_pow_left hLin d))
    _ = (a * cl + b) * (cu + cl + 2) ^ d * (N + 1) ^ d := by
      rw [mul_pow, mul_assoc]

/-- The literal quartic envelope and a shifted four-branch lower bound leave
at most degree-61 growth. The constant and both fixed shifts are uniform. -/
theorem exists_degree_sixty_one_bound
    (L B : ℕ → ℕ∞) (cu cl : ℕ) (hMono : Monotone L)
    (hUpper : ∀ N : ℕ, L N + B (N + cu) ≤
      ((4 * (N + cu + 62).choose 62 + 1540 * (N + cu + 61).choose 61 : ℕ) : ℕ∞))
    (hLower : ∀ N : ℕ, ((4 * (N + 62).choose 62 : ℕ) : ℕ∞) ≤ B (N + cl)) :
    ∃ C : ℕ, ∀ N : ℕ, L N ≤ ((C * (N + 1) ^ 61 : ℕ) : ℕ∞) := by
  refine ⟨(4 * cl + 1540) * (cu + cl + 2) ^ 61, ?_⟩
  exact enat_bound_of_shifted_binomial_bounds L B 4 1540 61 cu cl hMono hUpper hLower

end ShiftedBinomialGrowth

module

public import ThreeCycleDeterminant
import all FourierTransport

/-!
# The original monomial family satisfies the original residual equations

Different shift blocks have disjoint column support. Within one shift block,
the trace pairing is the sum of a nontrivial character of ZMod 3.
These are first-party proofs using the unchanged actual matrices and phases.
No new definition, compatibility hypothesis, or release license is introduced.
-/

@[expose] public section
noncomputable section

namespace UnitaryErrorBases

theorem residual_zero_iff (U : Family) : residual U = 0 ↔ IsUnitaryErrorBasis U := by
  constructor
  · intro h
    constructor
    · intro p
      constructor
      · exact sub_eq_zero.mp (congrArg (fun R : Residual => R.1 p) h)
      · exact sub_eq_zero.mp (congrArg (fun R : Residual => R.2.1 p) h)
    · intro p q hpq
      have hh := congrArg (fun R : Residual => R.2.2 p q) h
      change (if p = q then 0 else Matrix.trace ((U p).conjTranspose * U q)) = 0 at hh
      simpa only [if_neg hpq] using hh
  · rintro ⟨hU, hpair⟩
    apply Prod.ext
    · funext p
      exact sub_eq_zero.mpr (hU p).1
    · apply Prod.ext
      · funext p
        exact sub_eq_zero.mpr (hU p).2
      · funext p q
        change (if p = q then 0 else Matrix.trace ((U p).conjTranspose * U q)) = 0
        by_cases hpq : p = q
        · simp only [if_pos hpq]
        · simp only [if_neg hpq, hpair p q hpq]

namespace ThreeCycleMatrix

open scoped BigOperators

lemma character_sum_ne_zero (q : Index) (hq : q ≠ 0) :
    (∑ k : Index, ThreeCycleFourier.character (q * k)) = 0 := by
  calc
    (∑ k : Index, ThreeCycleFourier.character (q * k)) =
        ThreeCycleFourier.character (q * 0) +
        ThreeCycleFourier.character (q * 1) +
        ThreeCycleFourier.character (q * 2) := Fin.sum_univ_three _
    _ = 0 := by
      rcases (by decide : ∀ q : Index, q ≠ 0 → q = 1 ∨ q = 2) q hq with h | h
      · subst q
        simp only [one_mul, ThreeCycleFourier.character]
        change ThreeCycleFourier.omega ^ 0 + ThreeCycleFourier.omega ^ 1 +
          ThreeCycleFourier.omega ^ 2 = 0
        rw [pow_zero, pow_one, ThreeCycleFourier.omega_sq]
        ring
      · subst q
        simp only [mul_zero, mul_one, show (2 : Index) * 2 = 1 by decide,
          ThreeCycleFourier.character]
        change ThreeCycleFourier.omega ^ 0 + ThreeCycleFourier.omega ^ 2 +
          ThreeCycleFourier.omega ^ 1 = 0
        rw [pow_zero, pow_one, ThreeCycleFourier.omega_sq]
        ring

lemma leftFactor_cross_diagonal (d : PhaseTriple) (b c : Index) (hbc : b ≠ c)
    (k : Index) : ((leftFactor d b).conjTranspose * leftFactor d c) k k = 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, leftFactor_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i = k + b
  · have hi' : i ≠ k + c := by
      intro hc
      exact hbc (add_left_cancel (hi.symm.trans hc))
    simp only [if_pos hi, if_neg hi', mul_zero]
  · simp only [if_neg hi, star_zero, zero_mul]

theorem monomialFamily_pair_orthogonal (d : PhaseTriple) (p q : Label) (hpq : p ≠ q) :
    Matrix.trace ((monomialFamily d p).conjTranspose * monomialFamily d q) = 0 := by
  rcases p with ⟨a, b⟩
  rcases q with ⟨a', c⟩
  have he : Matrix.trace
      ((monomialFamily d (a, b)).conjTranspose * monomialFamily d (a', c)) =
      Matrix.trace (Matrix.diagonal (fun k => ThreeCycleFourier.character ((a' - a) * k)) *
        ((leftFactor d b).conjTranspose * leftFactor d c)) := by
    calc
      _ = Matrix.trace ((rightFactor a).conjTranspose *
          ((leftFactor d b).conjTranspose * leftFactor d c) * rightFactor a') := by
        simp only [monomialFamily_eq, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [Matrix.trace_mul_cycle, rightFactor_character]
  rw [he]
  by_cases hbc : b = c
  · subst c
    rw [leftFactor_star_mul, Matrix.mul_one, Matrix.trace_diagonal]
    apply character_sum_ne_zero
    intro h
    have ha : a' = a := sub_eq_zero.mp h
    exact hpq (by rw [ha])
  · change (∑ k : Index, _) = 0
    apply Finset.sum_eq_zero
    intro k _
    simp only [Matrix.diag_apply, Matrix.diagonal_mul,
      leftFactor_cross_diagonal d b c hbc k, mul_zero]

theorem monomial_family_is_unitary_error_basis (d : PhaseTriple) :
    IsUnitaryErrorBasis (monomialFamily d) :=
  ⟨monomialFamily_specialUnitary d, monomialFamily_pair_orthogonal d⟩

end ThreeCycleMatrix
end UnitaryErrorBases

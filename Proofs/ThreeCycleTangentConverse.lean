module

public import ThreeCycleDeterminant

/-!
# Converse from explicit matrix constraints to the literal derivative kernel

The hypotheses are anti-Hermiticity, trace zero, common within-block diagonals,
and the existing scalar pair equations. Every ordered pair and the original
Gram/determinant residuals are checked below; no unspecified compatibility
predicate or derivative-kernel equality is assumed.
First-party proof; unchanged imported mathlib provenance. No release license assigned.
-/

@[expose] public section
noncomputable section

namespace UnitaryErrorBases.ThreeCycleMatrix

open ArchitectureUEBDerivative
open scoped Matrix.Norms.Elementwise

theorem pair_trace_eq_matrix (d : PhaseTriple) (M : Family) (a b a' b' : Index)
    (hM : (M (a, b)).conjTranspose = -M (a, b)) :
    Matrix.trace
      ((fromCoordinates d M (a, b)).conjTranspose * monomialFamily d (a', b') +
        (monomialFamily d (a, b)).conjTranspose * fromCoordinates d M (a', b')) =
      Matrix.trace ((rightFactor a' * (rightFactor a).conjTranspose) *
        (((leftFactor d b).conjTranspose * leftFactor d b') * M (a', b') -
          M (a, b) * ((leftFactor d b).conjTranspose * leftFactor d b'))) := by
  have hm :
      (fromCoordinates d M (a, b)).conjTranspose * monomialFamily d (a', b') +
        (monomialFamily d (a, b)).conjTranspose * fromCoordinates d M (a', b') =
      (rightFactor a).conjTranspose *
        (((leftFactor d b).conjTranspose * leftFactor d b') * M (a', b') -
          M (a, b) * ((leftFactor d b).conjTranspose * leftFactor d b')) *
        rightFactor a' := by
    simp only [fromCoordinates, monomialFamily_eq, Matrix.conjTranspose_mul,
      hM, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc]
    abel
  rw [hm, Matrix.trace_mul_cycle]

theorem within_pair_trace_zero (d : PhaseTriple) (M : Family) (a a' b : Index)
    (hM : (M (a, b)).conjTranspose = -M (a, b))
    (hdiag : ∀ k, M (a', b) k k = M (a, b) k k) :
    Matrix.trace
      ((fromCoordinates d M (a, b)).conjTranspose * monomialFamily d (a', b) +
        (monomialFamily d (a, b)).conjTranspose * fromCoordinates d M (a', b)) = 0 := by
  rw [pair_trace_eq_matrix d M a b a' b hM, rightFactor_character,
    leftFactor_star_mul, Matrix.one_mul, Matrix.mul_one]
  change (∑ k : Index, _) = 0
  apply Finset.sum_eq_zero
  intro k _
  simp only [Matrix.diag_apply, Matrix.diagonal_mul, Matrix.sub_apply,
    hdiag k, sub_self, mul_zero]

/-- Reversing the ordered pair conjugates the exact differentiated trace. -/
theorem pair_trace_swap (U V : Family) (p q : Label) :
    Matrix.trace ((V p).conjTranspose * U q + (U p).conjTranspose * V q) =
      star (Matrix.trace ((V q).conjTranspose * U p + (U q).conjTranspose * V p)) := by
  rw [← Matrix.trace_conjTranspose]
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  rw [add_comm]

theorem all_pair_traces_zero (d : PhaseTriple) (M : Family)
    (hM : ∀ p, (M p).conjTranspose = -M p)
    (hdiag : ∀ a a' b k, M (a, b) k k = M (a', b) k k)
    (hscalar : ∀ b a a',
      ThreeCycleFourier.pairEquation (ThreeCycleFourier.phaseWeight d.val)
        (offDiagonalCoordinates M) b a a' = 0) :
    ∀ p q, Matrix.trace
      ((fromCoordinates d M p).conjTranspose * monomialFamily d q +
        (monomialFamily d p).conjTranspose * fromCoordinates d M q) = 0 := by
  rintro ⟨a, b⟩ ⟨a', b'⟩
  by_cases hb : b = b'
  · subst b'
    exact within_pair_trace_zero d M a a' b (hM (a, b)) (hdiag a' a b)
  · have hcycle : b' = b + 1 ∨ b = b' + 1 :=
      (by decide : ∀ b b' : Index, b ≠ b' → b' = b + 1 ∨ b = b' + 1) b b' hb
    rcases hcycle with hc | hc
    · subst b'
      exact (pair_trace_eq_scalar d M b a a' (hM (a, b))).trans (hscalar b a a')
    · subst b
      rw [pair_trace_swap]
      have hr := (pair_trace_eq_scalar d M b' a' a (hM (a', b'))).trans
        (hscalar b' a' a)
      rw [hr, star_zero]

/-- Every displayed matrix constraint is discharged against the original
derivative formula. There is no residual-binding or compatibility premise. -/
theorem fromCoordinates_mem_firstOrder (d : PhaseTriple) (M : Family)
    (hM : ∀ p, (M p).conjTranspose = -M p)
    (htrace : ∀ p, Matrix.trace (M p) = 0)
    (hdiag : ∀ a a' b k, M (a, b) k k = M (a', b) k k)
    (hscalar : ∀ b a a',
      ThreeCycleFourier.pairEquation (ThreeCycleFourier.phaseWeight d.val)
        (offDiagonalCoordinates M) b a a' = 0) :
    fromCoordinates d M ∈ firstOrderSpace (monomialFamily d) := by
  change fderiv ℝ residualOnAmbient (monomialFamily d) (fromCoordinates d M) = 0
  rw [(hasFDerivAt_residual (monomialFamily d)).fderiv]
  apply Prod.ext
  · funext p
    change productDerivative (monomialFamily d) p p (fromCoordinates d M) = 0
    apply (productDerivative_apply _ _ p p).trans
    rw [gram_fromCoordinates, hM p, add_neg_cancel, Matrix.mul_zero, Matrix.zero_mul]
    rfl
  · apply Prod.ext
    · funext p
      change detMultilinear.linearDeriv (monomialFamily d p) (fromCoordinates d M p) = 0
      exact (determinantDerivative_fromCoordinates d M p).trans (htrace p)
    · funext p q
      change (if p = q then (0 : AmbientFamily →L[ℝ] ℂ)
        else pairingDerivative (monomialFamily d) p q) (fromCoordinates d M) = 0
      by_cases hpq : p = q
      · rw [if_pos hpq]
        rfl
      · rw [if_neg hpq]
        exact (pairingDerivative_apply _ _ p q).trans
          (all_pair_traces_zero d M hM hdiag hscalar p q)

end UnitaryErrorBases.ThreeCycleMatrix

/-
First-party determinant differential over the original matrix residual.
The exact original definitions are imported through the accepted shared owner.
Classical determinant differentiation uses mathlib's continuous multilinear
derivative and determinant row replacement. No upstream proof body is copied.
Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55 (Apache-2.0);
Lean v4.35.0-rc2. Thanks to the Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
No first-party release license is assigned by this prototype.
-/
module

public import UEBResidualDefinitions
import all UEBResidualDefinitions
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open UnitaryErrorBases

namespace ArchitectureUEBDerivative

/-- The ordinary determinant, as a real continuous multilinear map of rows. -/
def detMultilinear : ContinuousMultilinearMap ℝ (fun _ : Index => Index → ℂ) ℂ where
  toMultilinearMap :=
    (Matrix.detRowAlternating : (Index → ℂ) [⋀^Index]→ₗ[ℂ] ℂ).toMultilinearMap.restrictScalars ℝ
  cont := by
    change Continuous (fun A : Matrix Index Index ℂ => A.det)
    exact continuous_id.matrix_det

theorem detMultilinear_apply (A : Mat) : detMultilinear A = A.det := rfl

/-- A real derivative exists at every ambient matrix, before any unitary hypothesis. -/
theorem hasFDerivAt_det (U : Index → Index → ℂ) :
    HasFDerivAt (fun A : Index → Index → ℂ => Matrix.det A)
      (detMultilinear.linearDeriv U) U :=
  detMultilinear.hasFDerivAt U

/-- At a determinant-one unitary the determinant derivative is the original trace equation. -/
theorem detDerivative_apply_of_specialUnitary (U V : Mat)
    (hU : IsSpecialUnitary U) :
    detMultilinear.linearDeriv U V = Matrix.trace (U.conjTranspose * V) := by
  unfold UnitaryErrorBases.Mat at *
  have hrow (i : Index) :
      (∑ k : Index, (V * U.conjTranspose) i k • U k) = V i := by
    funext j
    change (∑ k : Index, (V * U.conjTranspose) i k * U k j) = V i j
    change ((V * U.conjTranspose) * U) i j = V i j
    rw [Matrix.mul_assoc, hU.1, Matrix.mul_one]
  calc
    detMultilinear.linearDeriv U V = ∑ i : Index, (U.updateRow i (V i)).det := by
      exact ContinuousMultilinearMap.linearDeriv_apply detMultilinear U V
    _ = ∑ i : Index, (V * U.conjTranspose) i i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hrow i, Matrix.det_updateRow_sum, hU.2, smul_eq_mul, mul_one]
    _ = Matrix.trace (U.conjTranspose * V) := Matrix.trace_mul_comm V U.conjTranspose

theorem fderiv_det_apply_of_specialUnitary (U V : Mat)
    (hU : IsSpecialUnitary U) :
    fderiv ℝ (fun A : Mat => A.det) U V = Matrix.trace (U.conjTranspose * V) := by
  unfold UnitaryErrorBases.Mat at *
  calc
    _ = detMultilinear.linearDeriv U V :=
      congrArg (fun L : (Index → Index → ℂ) →L[ℝ] ℂ => L V) (hasFDerivAt_det U).fderiv
    _ = _ := detDerivative_apply_of_specialUnitary U V hU

#check hasFDerivAt_det
#check fderiv_det_apply_of_specialUnitary
#print axioms hasFDerivAt_det
#print axioms fderiv_det_apply_of_specialUnitary

end ArchitectureUEBDerivative

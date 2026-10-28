module

public import NativeExactCKMAllCross
public import NativeExactCKMFrameValueRows

/-!
# All original G polynomials vanish at the literal CKM point

The four cases are the unchanged original idempotency, within-frame,
frame-sum and cross-frame labels. The two imported theorems check those
cases at the same `pointCoordinates` and the original `h = 1/2`, `t = 1/3`.
This file only dispatches the original `gNumber` equivalence; it adds no
equation or point premise. It does not yet prove the F equations, a tangent
classification or a component theorem.

First-party composition only. The native/model and mathlib Apache-2.0
provenance is retained in the imported source owners; no borrowed proof body
is copied here. Thanks to the CKM construction and the Lean contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

@[expose] public section
noncomputable section

namespace QuadraticCertificate.ExactCKMAllG

open ConfigurationResidualIndices
open NativePolynomial.ConfigurationResiduals.Evaluation
open QuadraticCertificate.ExactCKMConfiguration

/-- Every one of the 3,159 originally numbered G polynomials vanishes at the
literal 39-point CKM configuration, with the original coefficients. -/
theorem all_gRow_eval_zero (r : Fin 3159) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ) r) = 0 := by
  have h : ∀ q : GLabel,
      MvPolynomial.eval pointCoordinates
        (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
          (gNumber q)) = 0 := by
    intro q
    rcases q with ⟨i, k⟩ | ⟨⟨f, s⟩, k⟩ | ⟨f, k⟩ | ⟨fg, a, b⟩
    · exact ExactCKMFrameValueRows.gId_eval_zero i k
    · exact ExactCKMFrameValueRows.gWithin_eval_zero f s k
    · exact ExactCKMFrameValueRows.gSum_eval_zero f k
    · exact ExactCKMAllCross.all_cross_eval_zero fg a b
  simpa only [gNumber.apply_symm_apply] using h (gNumber.symm r)

/-- The same result through the established original scalar evaluator. -/
theorem all_valueRow_zero (r : Fin 3159) :
    valueRow (1/2 : ℝ) (1/3 : ℝ) pointCoordinates r = 0 := by
  have h := all_gRow_eval_zero r
  rw [gRow_eval] at h
  exact h

/-- One wrong-value control for every original row. -/
theorem all_gRow_changed_value_control (r : Fin 3159) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ) r) ≠ 1 := by
  rw [all_gRow_eval_zero r]
  exact zero_ne_one

end QuadraticCertificate.ExactCKMAllG

#print axioms QuadraticCertificate.ExactCKMAllG.all_gRow_eval_zero
#print axioms QuadraticCertificate.ExactCKMAllG.all_valueRow_zero
#print axioms QuadraticCertificate.ExactCKMAllG.all_gRow_changed_value_control

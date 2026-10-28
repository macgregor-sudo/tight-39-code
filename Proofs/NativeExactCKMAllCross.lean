module

public import NativeExactCKMSharedCross
public import NativeExactCKMSharedHiddenCross
public import NativeExactCKMHiddenCross

@[expose] public section

/-!
Every original G cross equation at the unchanged raw CKM point.
An increasing original frame pair is either shared/shared, shared/hidden,
or hidden/hidden, where shared labels are0..3 and hidden labels are4..12.
The existing equation theorems cover54,324,324 rows respectively. This
module only joins those cases, retaining the exact original pair and all
outcome labels, coefficients, point coordinates and row numbering.

There is no new native/phase calculation and no supplied equation premise.
All702 cross rows are concluded; the other GLabel families and the full
3159-row solution remain separate. First-party theorem composition only,
with no copied proof body or novelty claim. Inherited native/mathlib
Apache-2.0 provenance remains in the imported owners, including
https://github.com/macgregor-sudo/compact-albert-recognition at
40d3b344180d9ddb78aaa2876873377c1e631515; mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55, Lean4.35.0-rc2.
Thanks to their contributors and the original CKM construction.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke,1676. No release license is selected here.
-/

noncomputable section

namespace QuadraticCertificate.ExactCKMAllCross

open ConfigurationResidualIndices
open NativePolynomial.ConfigurationResiduals.Evaluation
open QuadraticCertificate.ExactCKMConfiguration
open QuadraticCertificate.ExactCKMSharedCross
open QuadraticCertificate.ExactCKMSharedHiddenCross
open QuadraticCertificate.ExactCKMHiddenCross

/-- All702 original cross polynomials, with every increasing frame pair and outcome. -/
theorem all_cross_eval_zero (fg : Pair 13) (a b : Fin 3) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross fg a b))) = 0 := by
  by_cases hfirst : fg.val.1.val < 4
  · by_cases hsecond : fg.val.2.val < 4
    · let f : Fin 4 := ⟨fg.val.1.val, hfirst⟩
      let g : Fin 4 := ⟨fg.val.2.val, hsecond⟩
      have hfg : f < g := by
        change fg.val.1.val < fg.val.2.val
        exact fg.property
      have hpair : sharedFramePair f g hfg = fg := by
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;> rfl
      rw [← hpair]
      exact shared_cross_eval_zero f g hfg a b
    · exact original_shared_hidden_cross_eval_zero fg hfirst (by omega) a b
  · exact hidden_cross_eval_zero fg (by omega) a b

/-- The identical original cross residual values, for the semantic GLabel interface. -/
theorem all_cross_value_zero (fg : Pair 13) (a b : Fin 3) :
    valueRow (1/2 : ℝ) (1/3 : ℝ) pointCoordinates
      (gNumber (gCross fg a b)) = 0 := by
  have h := all_cross_eval_zero fg a b
  rw [gRow_eval] at h
  exact h

/-- The same original polynomial evaluation rejects the changed value1. -/
theorem all_cross_changed_value_control (fg : Pair 13) (a b : Fin 3) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross fg a b))) ≠ 1 := by
  rw [all_cross_eval_zero fg a b]
  exact zero_ne_one

end QuadraticCertificate.ExactCKMAllCross

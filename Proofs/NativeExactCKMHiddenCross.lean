module

public import NativeExactCKMQOneCross
public import NativeExactCKMQTwoCross
public import NativeExactCKMQThreeCross
public import NativeExactCKMCrossSectors

@[expose] public section

/-!
Every original scalar cross equation between distinct hidden frames4..12.
Each of the two labels belongs to exactly one of the existing three sectors
4+s,7+s,10+s, with s:Fin3. Six increasing sector cases invoke the existing
same-sector or cross-sector equation; three reversed cases contradict the
original strict frame order. No native or phase calculation is repeated.

The point is the unchanged raw CKM pointCoordinates, with its original
1053-variable packing, h=1/2, t=1/3, gCross labels and gNumber ordering.
This assembles324 original cross rows, not the complete3159-row solution.
It introduces neither a point nor a row-zero or frame assumption.

First-party finite index decomposition and theorem composition, with no
copied proof body or novelty claim. Inherited native/mathlib Apache-2.0
provenance remains in the imports and THIRD_PARTY_NOTICES.md#native-albert-code:
https://github.com/macgregor-sudo/compact-albert-recognition at
40d3b344180d9ddb78aaa2876873377c1e631515; mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55, Lean4.35.0-rc2.
Thanks to their contributors and the original CKM construction.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke,1676. No release license is selected here.
-/

noncomputable section

namespace QuadraticCertificate.ExactCKMHiddenCross

open NativePolynomial.ConfigurationResiduals
open NativePolynomial.ConfigurationResiduals.Evaluation
open ConfigurationResidualIndices UnitaryErrorBases.ComplexQuartet
open QuadraticCertificate.ExactCKMConfiguration
open QuadraticCertificate.ExactCKMThreeHiddenFrames
open QuadraticCertificate.ExactCKMABFrames
open QuadraticCertificate.ExactCKMCDFrames
open QuadraticCertificate.ExactCKMQOneCross
open QuadraticCertificate.ExactCKMQTwoCross
open QuadraticCertificate.ExactCKMQThreeCross
open QuadraticCertificate.ExactCKMCrossSectors

private theorem hidden_frame_cases (i : Fin 13) (hi : 4 ≤ i.val) :
    (∃ s : Fin 3, i = qOneFrameLabel s) ∨
    (∃ s : Fin 3, i = qTwoFrameLabel s) ∨
    (∃ s : Fin 3, i = qThreeFrameLabel s) := by
  by_cases h7 : i.val < 7
  · left
    refine ⟨⟨i.val - 4, by omega⟩, ?_⟩
    apply Fin.ext
    change i.val = 4 + (i.val - 4)
    omega
  · by_cases h10 : i.val < 10
    · right
      left
      refine ⟨⟨i.val - 7, by omega⟩, ?_⟩
      apply Fin.ext
      change i.val = 7 + (i.val - 7)
      omega
    · right
      right
      have hi13 := i.isLt
      refine ⟨⟨i.val - 10, by omega⟩, ?_⟩
      apply Fin.ext
      change i.val = 10 + (i.val - 10)
      omega

/-- All324 original values for strict hidden-frame pairs4≤i<j≤12. -/
theorem hidden_cross_value_zero (fg : Pair 13) (hhidden : 4 ≤ fg.val.1.val)
    (a b : PhaseIndex) :
    valueRow (1/2 : ℝ) (1/3 : ℝ) pointCoordinates
      (gNumber (gCross fg a b)) = 0 := by
  rcases fg with ⟨⟨i, j⟩, hij⟩
  change 4 ≤ i.val at hhidden
  have hjhidden : 4 ≤ j.val := by
    have hijv : i.val < j.val := hij
    omega
  rcases hidden_frame_cases i hhidden with ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩ <;>
    rcases hidden_frame_cases j hjhidden with ⟨u, rfl⟩ | ⟨u, rfl⟩ | ⟨u, rfl⟩
  · have hsu : s < u := by
      change 4 + s.val < 4 + u.val at hij
      change s.val < u.val
      omega
    exact qOne_cross_value_zero s u hsu a b
  · exact (crossSector_value_zero s u a b).1
  · exact (crossSector_value_zero s u a b).2.1
  · change 7 + s.val < 4 + u.val at hij
    have hu := u.isLt
    omega
  · have hsu : s < u := by
      change 7 + s.val < 7 + u.val at hij
      change s.val < u.val
      omega
    exact qTwo_cross_value_zero s u hsu a b
  · exact (crossSector_value_zero s u a b).2.2
  · change 10 + s.val < 4 + u.val at hij
    have hu := u.isLt
    omega
  · change 10 + s.val < 7 + u.val at hij
    have hu := u.isLt
    omega
  · have hsu : s < u := by
      change 10 + s.val < 10 + u.val at hij
      change s.val < u.val
      omega
    exact qThree_cross_value_zero s u hsu a b

/-- The same324 original numbered polynomials vanish at the unchanged real point. -/
theorem hidden_cross_eval_zero (fg : Pair 13) (hhidden : 4 ≤ fg.val.1.val)
    (a b : PhaseIndex) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross fg a b))) = 0 := by
  rw [gRow_eval]
  exact hidden_cross_value_zero fg hhidden a b

/-- Every identical original evaluation rejects the changed value1. -/
theorem hidden_cross_changed_value_control (fg : Pair 13)
    (hhidden : 4 ≤ fg.val.1.val) (a b : PhaseIndex) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross fg a b))) ≠ 1 := by
  rw [hidden_cross_eval_zero fg hhidden a b]
  exact zero_ne_one

end QuadraticCertificate.ExactCKMHiddenCross

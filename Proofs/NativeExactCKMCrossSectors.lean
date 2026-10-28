module

public import ComplexMatrixDisjointTrace
public import NativeCoordinateTracePairing
public import NativeExactCKMCDFrames

@[expose] public section

/-!
Original cross equations between distinct hidden CKM sectors q1,q2,q3.
The three actual complex matrices have supports respectively
{(0,2),(1,1),(2,0)}, {(0,0),(1,2),(2,1)}, {(0,1),(1,0),(2,2)}.
Their trace pairings vanish entry by entry, including every outcome phase.
The native overlap formula and the unchanged original point packing turn
this zero into the original overlap1/3 and numbered gCross evaluation0.

The three uniform conclusions cover all243 cross-sector equations between
frames4..6,7..9,10..12. No phase normalization, determinant expansion,
same-sector assertion, supplied row-zero premise or full39 solution is used.

First-party support arguments and native theorem composition; no copied
proof body or novelty claim. Inherited Apache-2.0/native provenance remains
in the imported owners and THIRD_PARTY_NOTICES.md#native-albert-code, including
https://github.com/macgregor-sudo/compact-albert-recognition at
40d3b344180d9ddb78aaa2876873377c1e631515. Lean4.35.0-rc2; mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55. Thanks to their contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke,1676. No release license is selected here.
-/

noncomputable section

namespace QuadraticCertificate.ExactCKMCrossSectors

open NativePolynomial CompactAlbert
open NativePolynomial.ConfigurationResiduals
open NativePolynomial.ConfigurationResiduals.MixedCoefficients
open NativePolynomial.ConfigurationResiduals.Evaluation
open NativePolynomial.CoordinateMaps ConfigurationResidualIndices
open UnitaryErrorBases.ComplexQuartet
open QuadraticCertificate.ExactCKMConfiguration
open QuadraticCertificate.ExactCKMThreeHiddenFrames
open QuadraticCertificate.ExactCKMABFrames
open QuadraticCertificate.ExactCKMCDFrames
open QuadraticCertificate.ComplexMatrixSupport

/-- Increasing original frame labels4+s and7+u. -/
def qOneQTwoPair (s u : Fin 3) : Pair 13 :=
  ⟨(qOneFrameLabel s, qTwoFrameLabel u), by
    change 4 + s.val < 7 + u.val
    have hs := s.isLt
    omega⟩

/-- Increasing original frame labels4+s and10+u. -/
def qOneQThreePair (s u : Fin 3) : Pair 13 :=
  ⟨(qOneFrameLabel s, qThreeFrameLabel u), by
    change 4 + s.val < 10 + u.val
    have hs := s.isLt
    omega⟩

/-- Increasing original frame labels7+s and10+u. -/
def qTwoQThreePair (s u : Fin 3) : Pair 13 :=
  ⟨(qTwoFrameLabel s, qThreeFrameLabel u), by
    change 7 + s.val < 10 + u.val
    have hs := s.isLt
    omega⟩

private theorem qOne_qTwo_disjoint (s u : PhaseIndex) :
    ∀ i j, qOneUnitary s i j = 0 ∨ qTwoUnitary u i j = 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [qOneUnitary, qTwoUnitary, ellNMatrix]

private theorem qOne_qThree_disjoint (s u : PhaseIndex) :
    ∀ i j, qOneUnitary s i j = 0 ∨ qThreeUnitary u i j = 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [qOneUnitary, qThreeUnitary, njMatrix]

private theorem qTwo_qThree_disjoint (s u : PhaseIndex) :
    ∀ i j, qTwoUnitary s i j = 0 ∨ qThreeUnitary u i j = 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [qTwoUnitary, ellNMatrix, qThreeUnitary, njMatrix]

private theorem phased_complementary_pairing (U V : TitsComplexMatrix)
    (h : ∀ i j, U i j = 0 ∨ V i j = 0) (c d : ℂ) :
    coordinatePairing
      (upperCoordinates (nativeComplementaryPoint (c • U)))
      (upperCoordinates (nativeComplementaryPoint (d • V))) = (1/3 : ℝ) := by
  have htrace : ((c • U) * (d • V).conjTranspose).trace = 0 := by
    apply trace_mul_conjTranspose_eq_zero_of_disjoint
    intro i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    rcases h i j with hU | hV
    · exact Or.inl (by rw [hU, mul_zero])
    · exact Or.inr (by rw [hV, mul_zero])
  rw [coordinatePairing_upperCoordinates_eq_native_trace,
    nativeComplementaryPoint_overlap, htrace]
  norm_num

private theorem qOne_qTwo_family_pairing (s u a b : PhaseIndex) :
    coordinatePairing (upperCoordinates (nativeFamilyPoint 1 s a))
      (upperCoordinates (nativeFamilyPoint 2 u b)) = (1/3 : ℝ) := by
  rw [qOneFamilyPoint_eq_matrix, qTwoFamilyPoint_eq_matrix]
  exact phased_complementary_pairing _ _ (qOne_qTwo_disjoint s u) _ _

private theorem qOne_qThree_family_pairing (s u a b : PhaseIndex) :
    coordinatePairing (upperCoordinates (nativeFamilyPoint 1 s a))
      (upperCoordinates (nativeFamilyPoint 3 u b)) = (1/3 : ℝ) := by
  rw [qOneFamilyPoint_eq_matrix, qThreeFamilyPoint_eq_matrix]
  exact phased_complementary_pairing _ _ (qOne_qThree_disjoint s u) _ _

private theorem qTwo_qThree_family_pairing (s u a b : PhaseIndex) :
    coordinatePairing (upperCoordinates (nativeFamilyPoint 2 s a))
      (upperCoordinates (nativeFamilyPoint 3 u b)) = (1/3 : ℝ) := by
  rw [qTwoFamilyPoint_eq_matrix, qThreeFamilyPoint_eq_matrix]
  exact phased_complementary_pairing _ _ (qTwo_qThree_disjoint s u) _ _

private theorem original_cross_value_zero_of_pairing (fg : Pair 13)
    (a b : PhaseIndex)
    (h : coordinatePairing
      (upperCoordinates (nativePoint (framePointIndex fg.val.1 a)))
      (upperCoordinates (nativePoint (framePointIndex fg.val.2 b))) = (1/3 : ℝ)) :
    valueRow (1/2 : ℝ) (1/3 : ℝ) pointCoordinates
      (gNumber (gCross fg a b)) = 0 := by
  simp only [valueRow, Equiv.symm_apply_apply, valueResidual, gCross]
  rw [pointValues_pointCoordinates, pointValues_pointCoordinates]
  exact sub_eq_zero.mpr h

/-- All243 actual original scalar cross-row values between the three sectors. -/
theorem crossSector_value_zero (s u : Fin 3) (a b : PhaseIndex) :
    valueRow (1/2 : ℝ) (1/3 : ℝ) pointCoordinates
      (gNumber (gCross (qOneQTwoPair s u) a b)) = 0 ∧
    valueRow (1/2 : ℝ) (1/3 : ℝ) pointCoordinates
      (gNumber (gCross (qOneQThreePair s u) a b)) = 0 ∧
    valueRow (1/2 : ℝ) (1/3 : ℝ) pointCoordinates
      (gNumber (gCross (qTwoQThreePair s u) a b)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · apply original_cross_value_zero_of_pairing
    change coordinatePairing
      (upperCoordinates (nativePoint (framePointIndex (qOneFrameLabel s) a)))
      (upperCoordinates (nativePoint (framePointIndex (qTwoFrameLabel u) b))) = (1/3 : ℝ)
    rw [congrFun (nativePoint_qOne_frame_eq_family s) a,
      congrFun (nativePoint_qTwo_frame_eq_family u) b]
    exact qOne_qTwo_family_pairing (s.val : PhaseIndex) (u.val : PhaseIndex)
      (a.val : PhaseIndex) (b.val : PhaseIndex)
  · apply original_cross_value_zero_of_pairing
    change coordinatePairing
      (upperCoordinates (nativePoint (framePointIndex (qOneFrameLabel s) a)))
      (upperCoordinates (nativePoint (framePointIndex (qThreeFrameLabel u) b))) = (1/3 : ℝ)
    rw [congrFun (nativePoint_qOne_frame_eq_family s) a,
      congrFun (nativePoint_qThree_frame_eq_family u) b]
    exact qOne_qThree_family_pairing (s.val : PhaseIndex) (u.val : PhaseIndex)
      (a.val : PhaseIndex) (b.val : PhaseIndex)
  · apply original_cross_value_zero_of_pairing
    change coordinatePairing
      (upperCoordinates (nativePoint (framePointIndex (qTwoFrameLabel s) a)))
      (upperCoordinates (nativePoint (framePointIndex (qThreeFrameLabel u) b))) = (1/3 : ℝ)
    rw [congrFun (nativePoint_qTwo_frame_eq_family s) a,
      congrFun (nativePoint_qThree_frame_eq_family u) b]
    exact qTwo_qThree_family_pairing (s.val : PhaseIndex) (u.val : PhaseIndex)
      (a.val : PhaseIndex) (b.val : PhaseIndex)

/-- The same original numbered polynomials vanish at the shared real configuration. -/
theorem crossSector_eval_zero (s u : Fin 3) (a b : PhaseIndex) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross (qOneQTwoPair s u) a b))) = 0 ∧
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross (qOneQThreePair s u) a b))) = 0 ∧
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross (qTwoQThreePair s u) a b))) = 0 := by
  simp only [gRow_eval]
  exact crossSector_value_zero s u a b

/-- Changing any of these identical original evaluations to1 is rejected. -/
theorem crossSector_changed_value_control (s u : Fin 3) (a b : PhaseIndex) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross (qOneQTwoPair s u) a b))) ≠ 1 ∧
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross (qOneQThreePair s u) a b))) ≠ 1 ∧
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross (qTwoQThreePair s u) a b))) ≠ 1 := by
  obtain ⟨h12, h13, h23⟩ := crossSector_eval_zero s u a b
  rw [h12, h13, h23]
  exact ⟨zero_ne_one, zero_ne_one, zero_ne_one⟩

/-- Original frames4/7, outcomes0/0, points12/21. -/
theorem original_g2853_representative :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow
        (1/2 : ℝ) (1/3 : ℝ) (2853 : Fin 3159)) = 0 := by
  have hn : gNumber (gCross (qOneQTwoPair 0 0) 0 0) = (2853 : Fin 3159) := by
    apply Fin.ext
    rw [gNumber_cross_val]
    decide +kernel
  rw [← hn]
  exact (crossSector_eval_zero 0 0 0 0).1

/-- Original frames4/10, outcomes0/0, points12/30. -/
theorem original_g2880_representative :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow
        (1/2 : ℝ) (1/3 : ℝ) (2880 : Fin 3159)) = 0 := by
  have hn : gNumber (gCross (qOneQThreePair 0 0) 0 0) = (2880 : Fin 3159) := by
    apply Fin.ext
    rw [gNumber_cross_val]
    decide +kernel
  rw [← hn]
  exact (crossSector_eval_zero 0 0 0 0).2.1

/-- Original frames7/10, outcomes0/0, points21/30. -/
theorem original_g3042_representative :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow
        (1/2 : ℝ) (1/3 : ℝ) (3042 : Fin 3159)) = 0 := by
  have hn : gNumber (gCross (qTwoQThreePair 0 0) 0 0) = (3042 : Fin 3159) := by
    apply Fin.ext
    rw [gNumber_cross_val]
    decide +kernel
  rw [← hn]
  exact (crossSector_eval_zero 0 0 0 0).2.2

end QuadraticCertificate.ExactCKMCrossSectors

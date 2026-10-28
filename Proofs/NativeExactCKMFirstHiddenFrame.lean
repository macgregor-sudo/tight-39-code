module

public import NativeExactCKMConfiguration
public import NativeComplementaryConstruction

/-!
# The first whole raw hidden CKM frame is a reverse central triple

This binder retains original frame4/points12,13,14. The native Tits sign
convention sends raw outcomes0,1,2 to matrix scalars1,omega²,omega. The
accepted native special-unitary construction then supplies trace1,
idempotency, all ordered orthogonal pairs and sum1 at once. No original
point formula is modified and no general raw-to-monomial gauge is asserted.

First-party native equality and accepted theorem composition; no proof copied.
Inherited Apache-2.0 provenance: compact-albert-recognition,
https://github.com/macgregor-sudo/compact-albert-recognition,
commit40d3b344180d9ddb78aaa2876873377c1e631515; mathlib,
https://github.com/leanprover-community/mathlib4,
commit065356127b1dc0016f66b7283ce0ce2c4055aa55. Thanks to the original
CKM, native-model, Lean and Mathlib contributors. No release license assigned.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke,1676.
-/

@[expose] public section
noncomputable section
namespace QuadraticCertificate.ExactCKMFirstHiddenFrame
open CompactAlbert NativePolynomial
open NativePolynomial.ConfigurationResiduals
open UnitaryErrorBases.ComplexQuartet
open ExactCKMConfiguration

/-- The exact raw q1,s0 outcome-zero hidden matrix; determinant is positive1. -/
def firstHiddenUnitary : TitsComplexMatrix :=
  !![0, 0, 1; 0, -1, 0; 1, 0, 0]

theorem firstHiddenUnitary_specialUnitary :
    firstHiddenUnitary * firstHiddenUnitary.conjTranspose = 1 ∧
      firstHiddenUnitary.det = 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [firstHiddenUnitary, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.conjTranspose_apply, Matrix.one_apply]
  · norm_num [firstHiddenUnitary, Matrix.det_fin_three]

/-- Reduce the j basis input once, before any phase or native point proof. -/
private theorem firstHidden_j_input (z : ℂ) :
    Glennie.octMul (complexOctonion z) (nativeOctonionBasis 2) =
      (⟨0, 0, z.re, z.im⟩, 0) := by
  have hj : nativeOctonionBasis 2 = (⟨0, 0, 1, 0⟩, 0) := rfl
  rw [hj]
  apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [complexOctonion, Glennie.octMul, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

/-- Reduce the ell basis input independently of all phase arithmetic. -/
private theorem firstHidden_ell_input (z : ℂ) :
    Glennie.octMul (complexOctonion z) (nativeOctonionBasis 4) =
      (0, ⟨z.re, z.im, 0, 0⟩) := by
  have hell : nativeOctonionBasis 4 = (0, 1) := rfl
  rw [hell]
  apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [complexOctonion, Glennie.octMul, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

/-- Small input equality, preserving the shared point definition unchanged. -/
private theorem firstHidden_raw_inputs (t : PhaseIndex) :
    nativeFamilyPoint 1 0 t =
      nativeOuterProductThird
        (⟨0, 0, (UnitaryErrorBases.ThreeCycleFourier.character t).re,
          (UnitaryErrorBases.ThreeCycleFourier.character t).im⟩, 0)
        (0, ⟨(UnitaryErrorBases.ThreeCycleFourier.character t).re,
          (UnitaryErrorBases.ThreeCycleFourier.character t).im, 0, 0⟩) := by
  rw [nativeFamilyPoint, if_neg (by decide), if_pos rfl, zero_add,
    firstHidden_j_input, firstHidden_ell_input]

/-- A small outer-product record calculation on real inputs only. -/
private theorem firstHidden_outer_readout (x y : ℝ) :
    nativeOuterProductThird (⟨0, 0, x, y⟩, 0) (0, ⟨x, y, 0, 0⟩) =
      (⟨1/3, (x^2+y^2)/3, (x^2+y^2)/3,
        (⟨0, 0, -x/3, -y/3⟩, 0),
        (0, ⟨-x/3, -y/3, 0, 0⟩),
        (0, ⟨0, 0, (y^2-x^2)/3, -(2*x*y)/3⟩)⟩ : Glennie.Albert) := by
  apply Glennie.Albert.extExplicit
  all_goals first | (apply Prod.ext <;> apply Quaternion.ext) | skip
  all_goals
    norm_num [nativeOuterProductThird, Glennie.octNormSq, Quaternion.normSq_def',
      Glennie.octMul, Glennie.octConj, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, smul_eq_mul] <;> ring

/-- Independently reduce the inverse Tits constructor, without basis or phases. -/
private theorem firstHidden_central_readout (c : ℂ) :
    nativeComplementaryPoint (c • firstHiddenUnitary) =
      (⟨1/3, 1/3, 1/3,
        (⟨0, 0, -c.re/3, c.im/3⟩, 0),
        (0, ⟨-c.re/3, c.im/3, 0, 0⟩),
        (0, ⟨0, 0, -c.re/3, -c.im/3⟩)⟩ : Glennie.Albert) := by
  apply Glennie.Albert.extExplicit
  all_goals first | (apply Prod.ext <;> apply Quaternion.ext) | skip
  all_goals
    norm_num [nativeComplementaryPoint, firstHiddenUnitary, fromTitsCoordinates,
      octonionFromTitsRow, Matrix.smul_apply, Glennie.octConj,
      Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring

private theorem firstHidden_case_zero :
    nativeFamilyPoint 1 0 (0 : PhaseIndex) = nativeComplementaryPoint firstHiddenUnitary := by
  have hc := firstHidden_central_readout (1 : ℂ)
  simp only [one_smul] at hc
  rw [firstHidden_raw_inputs, firstHidden_outer_readout, hc]
  apply Glennie.Albert.extExplicit
  all_goals first | (apply Prod.ext <;> apply Quaternion.ext) | skip
  all_goals norm_num [UnitaryErrorBases.ThreeCycleFourier.character]

private theorem firstHidden_case_one :
    nativeFamilyPoint 1 0 (1 : PhaseIndex) = nativeComplementaryPoint
      ((UnitaryErrorBases.ThreeCycleFourier.omega ^ 2) • firstHiddenUnitary) := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have hOneVal : (1 : PhaseIndex).val = 1 := by decide
  have hc1 : UnitaryErrorBases.ThreeCycleFourier.character (1 : PhaseIndex) =
      UnitaryErrorBases.ThreeCycleFourier.omega := by
    rw [UnitaryErrorBases.ThreeCycleFourier.character, hOneVal, pow_one]
  rw [UnitaryErrorBases.ThreeCycleFourier.omega_sq]
  rw [firstHidden_raw_inputs, hc1, firstHidden_outer_readout, firstHidden_central_readout]
  apply Glennie.Albert.extExplicit
  all_goals first | (apply Prod.ext <;> apply Quaternion.ext) | skip
  all_goals
    norm_num [UnitaryErrorBases.ThreeCycleFourier.character,
      UnitaryErrorBases.ThreeCycleFourier.omega, pow_two,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.normSq_apply] <;> nlinarith [hs]

private theorem firstHidden_case_two :
    nativeFamilyPoint 1 0 (2 : PhaseIndex) = nativeComplementaryPoint
      (UnitaryErrorBases.ThreeCycleFourier.omega • firstHiddenUnitary) := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) := Real.mul_self_sqrt (by norm_num)
  have hc2 : UnitaryErrorBases.ThreeCycleFourier.character (2 : PhaseIndex) =
      -1 - UnitaryErrorBases.ThreeCycleFourier.omega := by
    rw [UnitaryErrorBases.ThreeCycleFourier.character,
      show (2 : PhaseIndex).val = 2 by decide]
    exact UnitaryErrorBases.ThreeCycleFourier.omega_sq
  rw [firstHidden_raw_inputs, hc2, firstHidden_outer_readout, firstHidden_central_readout]
  apply Glennie.Albert.extExplicit
  all_goals first | (apply Prod.ext <;> apply Quaternion.ext) | skip
  all_goals
    norm_num [UnitaryErrorBases.ThreeCycleFourier.character,
      UnitaryErrorBases.ThreeCycleFourier.omega, pow_two,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.normSq_apply] <;> nlinarith [hs]

/-- Actual native identity of the three labelled points; raw1 is omega²,
raw2 is omega, so the accepted REVERSE central order is essential. -/
theorem firstHiddenFamily_eq_reverseCentral :
    (fun t : Fin 3 => nativeFamilyPoint 1 0 (t.val : PhaseIndex)) =
      nativeReverseCentralTriple firstHiddenUnitary := by
  funext t
  fin_cases t
  · exact firstHidden_case_zero
  · exact firstHidden_case_one
  · exact firstHidden_case_two

/-- Whole actual native trace-one orthogonal frame, with the exact raw order. -/
theorem firstHiddenFamily_frame :
    Glennie.Frame (fun t : Fin 3 => nativeFamilyPoint 1 0 (t.val : PhaseIndex)) := by
  rw [firstHiddenFamily_eq_reverseCentral]
  exact (native_central_triples_are_frames firstHiddenUnitary
    firstHiddenUnitary_specialUnitary).2

/-- Original grouped frame4 has these same raw q1,s0 points. -/
theorem nativePoint_frame4_eq_family :
    (fun t : Fin 3 => nativePoint (framePointIndex 4 t)) =
      (fun t : Fin 3 => nativeFamilyPoint 1 0 (t.val : PhaseIndex)) := by
  funext t
  fin_cases t <;> rfl

/-- Actual shared configuration frame4 satisfies all four native Frame fields. -/
theorem nativePoint_frame4 :
    Glennie.Frame (fun t : Fin 3 => nativePoint (framePointIndex 4 t)) := by
  rw [nativePoint_frame4_eq_family]
  exact firstHiddenFamily_frame

end QuadraticCertificate.ExactCKMFirstHiddenFrame

#print axioms QuadraticCertificate.ExactCKMFirstHiddenFrame.firstHiddenFamily_eq_reverseCentral
#print axioms QuadraticCertificate.ExactCKMFirstHiddenFrame.nativePoint_frame4

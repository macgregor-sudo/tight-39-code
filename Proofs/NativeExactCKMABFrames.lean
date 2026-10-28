module

public import NativeExactCKMThreeHiddenFrames

/-!
# The three raw A/B CKM frames from one generic e4/e6 matrix binder

Only original within-frames7,8,9 are concluded. The explicit matrix for raw
frame s has rows[AB character(s),0,0],[0,0,-star(B character(s))],
[0,star A,0]. The lower-column swap and explicit minus cancel in its
determinant. Raw t again retains the REVERSE central order0,2,1.

The small e4/e6 native readout adapts the first-party staged pattern also
validated in the numeric owner's private ell_n_readout; that separate overlap
source is neither imported nor modified, and no cross-row result is concluded.
Accepted q1 scalar phase multiplication is reused. No third-party proof copied.
Inherited native/mathlib Apache-2.0 pins: compact-albert-recognition at
40d3b344180d9ddb78aaa2876873377c1e631515 and mathlib at
065356127b1dc0016f66b7283ce0ce2c4055aa55. Thanks to their contributors and
the original CKM construction. No release license assigned.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke,1676.
-/

@[expose] public section
noncomputable section
namespace QuadraticCertificate.ExactCKMABFrames
open CompactAlbert NativePolynomial
open NativePolynomial.ConfigurationResiduals
open UnitaryErrorBases.ComplexQuartet
open ExactCKMConfiguration

/-- Exact e4/e6 native matrix, including the lower-column permutation. -/
def ellNMatrix (z w : ℂ) : TitsComplexMatrix :=
  !![z*w, 0, 0; 0, 0, -star w; 0, star z, 0]

/-- Actual raw A/B frame matrix, without a determinant gauge adjustment. -/
def qTwoUnitary (s : PhaseIndex) : TitsComplexMatrix :=
  ellNMatrix (exactPhases 0)
    (exactPhases 1 * UnitaryErrorBases.ThreeCycleFourier.character s)

private theorem ell_input (z : ℂ) :
    Glennie.octMul (complexOctonion z) (nativeOctonionBasis 4) =
      (0, ⟨z.re, z.im, 0, 0⟩) := by
  have hb : nativeOctonionBasis 4 = (0, 1) := rfl
  rw [hb]
  apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [complexOctonion, Glennie.octMul, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem n_input (w : ℂ) :
    Glennie.octMul (complexOctonion w) (nativeOctonionBasis 6) =
      (0, ⟨0, 0, w.re, -w.im⟩) := by
  have hb : nativeOctonionBasis 6 = (0, ⟨0, 0, 1, 0⟩) := rfl
  rw [hb]
  apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [complexOctonion, Glennie.octMul, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem ell_n_readout (z w : ℂ) :
    nativeOuterProductThird
      (Glennie.octMul (complexOctonion z) (nativeOctonionBasis 4))
      (Glennie.octMul (complexOctonion w) (nativeOctonionBasis 6)) =
      (⟨1/3, Complex.normSq z/3, Complex.normSq w/3,
        (0, ⟨-z.re/3, -z.im/3, 0, 0⟩),
        (0, ⟨0, 0, -w.re/3, w.im/3⟩),
        (⟨0, 0, -(z*w).re/3, (z*w).im/3⟩, 0)⟩ : Glennie.Albert) := by
  rw [ell_input, n_input]
  apply Glennie.Albert.extExplicit
  all_goals first | (apply Prod.ext <;> apply Quaternion.ext) | skip
  all_goals
    norm_num [nativeOuterProductThird, Glennie.octNormSq, Quaternion.normSq_def',
      Glennie.octMul, Glennie.octConj, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring

private theorem complementary_readout (z w : ℂ) :
    nativeComplementaryPoint (ellNMatrix z w) =
      (⟨1/3, 1/3, 1/3,
        (0, ⟨-z.re/3, -z.im/3, 0, 0⟩),
        (0, ⟨0, 0, -w.re/3, w.im/3⟩),
        (⟨0, 0, -(z*w).re/3, (z*w).im/3⟩, 0)⟩ : Glennie.Albert) := by
  apply Glennie.Albert.extExplicit
  all_goals first | (apply Prod.ext <;> apply Quaternion.ext) | skip
  all_goals
    norm_num [nativeComplementaryPoint, ellNMatrix, fromTitsCoordinates,
      octonionFromTitsRow, Glennie.octConj, Matrix.smul_apply,
      Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring

/-- One generic native point binder, before any exact A/B or phase arithmetic. -/
theorem nativeOuterProduct_ell_n_eq_complementary (z w : ℂ)
    (hz : Complex.normSq z = 1) (hw : Complex.normSq w = 1) :
    nativeOuterProductThird
      (Glennie.octMul (complexOctonion z) (nativeOctonionBasis 4))
      (Glennie.octMul (complexOctonion w) (nativeOctonionBasis 6)) =
        nativeComplementaryPoint (ellNMatrix z w) := by
  rw [ell_n_readout, complementary_readout, hz, hw]

private theorem unit_product (z w : ℂ)
    (hz : z * star z = 1) (hw : w * star w = 1) :
    (z*w) * star (z*w) = 1 := by
  calc
    _ = (z * star z) * (w * star w) := by rw [star_mul]; ring
    _ = 1 := by rw [hz, hw, one_mul]

private theorem normSq_of_unit (z : ℂ) (hz : z * star z = 1) :
    Complex.normSq z = 1 := by
  have hnorm : (Complex.normSq z : ℂ) = z * star z := by
    simpa only [starRingEnd_apply, mul_comm] using
      (Complex.normSq_eq_conj_mul_self (z := z))
  simpa using congrArg Complex.re (hnorm.trans hz)

/-- Actual rational A phase is unit, not a new normalization hypothesis. -/
theorem phase_A_unit : exactPhases 0 * star (exactPhases 0) = 1 := by
  apply Complex.ext <;>
    norm_num [exactPhases, Complex.mul_re, Complex.mul_im, Complex.div_re,
      Complex.div_im, Complex.normSq_apply]

/-- Actual rational B phase is unit, not a new normalization hypothesis. -/
theorem phase_B_unit : exactPhases 1 * star (exactPhases 1) = 1 := by
  apply Complex.ext <;>
    norm_num [exactPhases, Complex.mul_re, Complex.mul_im, Complex.div_re,
      Complex.div_im, Complex.normSq_apply]

private theorem character_unit (s : PhaseIndex) :
    UnitaryErrorBases.ThreeCycleFourier.character s *
      star (UnitaryErrorBases.ThreeCycleFourier.character s) = 1 := by
  simp only [Complex.star_def, Complex.mul_conj,
    CompactAlbert.character_normSq_eq_one, Complex.ofReal_one]

/-- Generic special-unitary matrix from the native unit e4/e6 inputs. -/
theorem ellNMatrix_specialUnitary (z w : ℂ)
    (hz : z * star z = 1) (hw : w * star w = 1) :
    ellNMatrix z w * (ellNMatrix z w).conjTranspose = 1 ∧ (ellNMatrix z w).det = 1 := by
  have hzc : star z * z = 1 := by simpa only [mul_comm] using hz
  have hwc : star w * w = 1 := by simpa only [mul_comm] using hw
  have hzw := unit_product z w hz hw
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [ellNMatrix, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.conjTranspose_apply, Matrix.one_apply]
    · change (z*w) * (star z * star w) = 1
      have h : (z*w) * (star w * star z) = 1 := by
        simpa only [star_mul] using hzw
      calc
        _ = (z*w) * (star w * star z) := by ring
        _ = 1 := h
    · change star w * w = 1
      exact hwc
    · change star z * z = 1
      exact hzc
  · calc
      _ = (z * star z) * (w * star w) := by
        simp [ellNMatrix, Matrix.det_fin_three] <;> ring
      _ = 1 := by rw [hz, hw, one_mul]

theorem qTwoUnitary_specialUnitary (s : PhaseIndex) :
    qTwoUnitary s * (qTwoUnitary s).conjTranspose = 1 ∧ (qTwoUnitary s).det = 1 := by
  exact ellNMatrix_specialUnitary _ _ phase_A_unit
    (unit_product _ _ phase_B_unit (character_unit s))

/-- Scalar phase product already carried by the accepted q1 matrix identity. -/
private theorem character_product_sum (s t : PhaseIndex) :
    UnitaryErrorBases.ThreeCycleFourier.character t *
      UnitaryErrorBases.ThreeCycleFourier.character (s+t) =
      star (UnitaryErrorBases.ThreeCycleFourier.character t) *
        UnitaryErrorBases.ThreeCycleFourier.character s := by
  have h := congrArg (fun M : TitsComplexMatrix => M 0 2)
    (ExactCKMThreeHiddenFrames.twoInputMatrix_character s t)
  simpa [ExactCKMThreeHiddenFrames.twoInputMatrix,
    ExactCKMThreeHiddenFrames.qOneUnitary, Matrix.smul_apply] using h

/-- Uniform matrix matching uses exact character multiplication, no native expansion. -/
theorem ellNMatrix_AB_character (s t : PhaseIndex) :
    ellNMatrix (exactPhases 0 * UnitaryErrorBases.ThreeCycleFourier.character t)
      (exactPhases 1 * UnitaryErrorBases.ThreeCycleFourier.character (s+t)) =
      star (UnitaryErrorBases.ThreeCycleFourier.character t) • qTwoUnitary s := by
  have hp : (exactPhases 0 * UnitaryErrorBases.ThreeCycleFourier.character t) *
      (exactPhases 1 * UnitaryErrorBases.ThreeCycleFourier.character (s+t)) =
      star (UnitaryErrorBases.ThreeCycleFourier.character t) *
        (exactPhases 0 * (exactPhases 1 * UnitaryErrorBases.ThreeCycleFourier.character s)) := by
    calc
      _ = (exactPhases 0 * exactPhases 1) *
          (UnitaryErrorBases.ThreeCycleFourier.character t *
           UnitaryErrorBases.ThreeCycleFourier.character (s+t)) := by ring
      _ = _ := by rw [character_product_sum]; ring
  have hstar (a b c : ℂ) : star a * star (b*c) = star a * star c * star b := by
    rw [star_mul]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ellNMatrix, qTwoUnitary, Matrix.smul_apply, hp]
  all_goals try simp only [ExactCKMThreeHiddenFrames.character_add]
  all_goals try ring
  -- The one remaining lower-block cell is exactly the scalar hstar identity.
  simpa only [starRingEnd_apply] using
    (hstar (exactPhases 1) (UnitaryErrorBases.ThreeCycleFourier.character s)
      (UnitaryErrorBases.ThreeCycleFourier.character t))

/-- Exact raw A/B point to its uniform native complementary matrix. -/
theorem qTwoFamilyPoint_eq_matrix (s t : PhaseIndex) :
    nativeFamilyPoint 2 s t = nativeComplementaryPoint
      (star (UnitaryErrorBases.ThreeCycleFourier.character t) • qTwoUnitary s) := by
  have hz : Complex.normSq (exactPhases 0 * UnitaryErrorBases.ThreeCycleFourier.character t) = 1 :=
    normSq_of_unit _ (unit_product _ _ phase_A_unit (character_unit t))
  have hw : Complex.normSq
      (exactPhases 1 * UnitaryErrorBases.ThreeCycleFourier.character (s+t)) = 1 :=
    normSq_of_unit _ (unit_product _ _ phase_B_unit (character_unit (s+t)))
  rw [nativeFamilyPoint, if_neg (by decide), if_neg (by decide), if_pos rfl,
    nativeOuterProduct_ell_n_eq_complementary _ _ hz hw, ellNMatrix_AB_character]

private theorem character_zero : UnitaryErrorBases.ThreeCycleFourier.character 0 = (1 : ℂ) := rfl

private theorem character_one : UnitaryErrorBases.ThreeCycleFourier.character 1 =
    UnitaryErrorBases.ThreeCycleFourier.omega := by
  rw [UnitaryErrorBases.ThreeCycleFourier.character,
    show (1 : PhaseIndex).val = 1 by decide, pow_one]

private theorem character_two : UnitaryErrorBases.ThreeCycleFourier.character 2 =
    UnitaryErrorBases.ThreeCycleFourier.omega ^ 2 := by
  rw [UnitaryErrorBases.ThreeCycleFourier.character,
    show (2 : PhaseIndex).val = 2 by decide]

private theorem star_omega : star UnitaryErrorBases.ThreeCycleFourier.omega =
    UnitaryErrorBases.ThreeCycleFourier.omega ^ 2 := by
  rw [UnitaryErrorBases.ThreeCycleFourier.omega_sq]
  apply Complex.ext <;>
    norm_num [UnitaryErrorBases.ThreeCycleFourier.omega, Complex.div_re,
      Complex.div_im, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

private theorem star_omega_sq : star (UnitaryErrorBases.ThreeCycleFourier.omega ^ 2) =
    UnitaryErrorBases.ThreeCycleFourier.omega := by
  have h := congrArg (fun z : ℂ => star z) star_omega
  simpa only [star_star] using h.symm

/-- Exact raw outcome0,1,2 is uniformly reverse central order0,2,1. -/
theorem qTwoFamily_eq_reverseCentral (s : PhaseIndex) :
    (fun t : Fin 3 => nativeFamilyPoint 2 s (t.val : PhaseIndex)) =
      nativeReverseCentralTriple (qTwoUnitary s) := by
  funext t
  fin_cases t
  · change nativeFamilyPoint 2 s (0 : PhaseIndex) = nativeComplementaryPoint (qTwoUnitary s)
    simpa only [character_zero, star_one, one_smul] using qTwoFamilyPoint_eq_matrix s 0
  · change nativeFamilyPoint 2 s (1 : PhaseIndex) = nativeComplementaryPoint
      ((UnitaryErrorBases.ThreeCycleFourier.omega ^ 2) • qTwoUnitary s)
    simpa only [character_one, star_omega] using qTwoFamilyPoint_eq_matrix s 1
  · change nativeFamilyPoint 2 s (2 : PhaseIndex) = nativeComplementaryPoint
      (UnitaryErrorBases.ThreeCycleFourier.omega • qTwoUnitary s)
    simpa only [character_two, star_omega_sq] using qTwoFamilyPoint_eq_matrix s 2

/-- Each actual A/B family frame is trace1, idempotent, orthogonal and sums1. -/
theorem qTwoFamily_frame (s : PhaseIndex) :
    Glennie.Frame (fun t : Fin 3 => nativeFamilyPoint 2 s (t.val : PhaseIndex)) := by
  rw [qTwoFamily_eq_reverseCentral]
  exact (native_central_triples_are_frames (qTwoUnitary s) (qTwoUnitary_specialUnitary s)).2

/-- Original frames7+s, retaining every original raw outcome label. -/
def qTwoFrameLabel (s : Fin 3) : Fin 13 := ⟨7 + s.val, by omega⟩

theorem nativePoint_qTwo_frame_eq_family (s : Fin 3) :
    (fun t : Fin 3 => nativePoint (framePointIndex (qTwoFrameLabel s) t)) =
      (fun t : Fin 3 => nativeFamilyPoint 2 (s.val : PhaseIndex) (t.val : PhaseIndex)) := by
  funext t
  fin_cases s <;> fin_cases t <;> rfl

/-- Whole actual shared configuration frames7,8,9; no cross-row claim. -/
theorem nativePoint_qTwo_frames (s : Fin 3) :
    Glennie.Frame (fun t : Fin 3 => nativePoint (framePointIndex (qTwoFrameLabel s) t)) := by
  rw [nativePoint_qTwo_frame_eq_family]
  exact qTwoFamily_frame (s.val : PhaseIndex)

end QuadraticCertificate.ExactCKMABFrames

#print axioms QuadraticCertificate.ExactCKMABFrames.nativeOuterProduct_ell_n_eq_complementary
#print axioms QuadraticCertificate.ExactCKMABFrames.qTwoFamily_eq_reverseCentral
#print axioms QuadraticCertificate.ExactCKMABFrames.nativePoint_qTwo_frames

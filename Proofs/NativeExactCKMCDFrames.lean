module

public import NativeExactCKMABFrames

/-!
# Remaining raw C/D CKM frames via a fixed cyclic column permutation

Only original within-frames10,11,12 are concluded. For the actual C,D phases,
U_s has rows[0,CD character(s),0],[-star(D character(s)),0,0],
[0,0,star C]. The generic n/j matrix is the accepted e4/e6 matrix times one
fixed determinant-one column cycle; special unitarity is transferred without
expanding another nine SU cells. One staged native n/j readout proves the
actual point binder. Raw t retains REVERSE central order0,2,1.

First-party native readout and accepted theorem composition. No accepted
point or q2 source changes, no cross-frame equation or all39 solution claim.
No third-party proof copied. Inherited native/mathlib Apache-2.0 pins:
compact-albert-recognition40d3b344180d9ddb78aaa2876873377c1e631515;
mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55. Thanks to their
contributors and the original CKM construction. No release license assigned.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke,1676.
-/

@[expose] public section
noncomputable section
namespace QuadraticCertificate.ExactCKMCDFrames
open CompactAlbert NativePolynomial
open NativePolynomial.ConfigurationResiduals
open UnitaryErrorBases.ComplexQuartet
open ExactCKMConfiguration

/-- Actual n/j matrix, retaining all signs from the native Tits dictionary. -/
def njMatrix (z w : ℂ) : TitsComplexMatrix :=
  !![0, z*w, 0; -star w, 0, 0; 0, 0, star z]

/-- Fixed even column cycle old0→new1, old1→new2, old2→new0. -/
def columnCycle : TitsComplexMatrix := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

/-- Exact C/D matrix for raw frame s, with no determinant gauge change. -/
def qThreeUnitary (s : PhaseIndex) : TitsComplexMatrix :=
  njMatrix (exactPhases 2)
    (exactPhases 3 * UnitaryErrorBases.ThreeCycleFourier.character s)

/-- The new matrix differs from the accepted e4/e6 matrix only by this cycle. -/
theorem njMatrix_eq_ellN_mul_cycle (z w : ℂ) :
    njMatrix z w = ExactCKMABFrames.ellNMatrix z w * columnCycle := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [njMatrix, ExactCKMABFrames.ellNMatrix, columnCycle,
      Matrix.mul_apply, Fin.sum_univ_three]

private theorem columnCycle_specialUnitary :
    columnCycle * columnCycle.conjTranspose = 1 ∧ columnCycle.det = 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [columnCycle, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.conjTranspose_apply, Matrix.one_apply]
  · norm_num [columnCycle, Matrix.det_fin_three]

/-- Special unitarity transfers from the accepted generic q2 matrix. -/
theorem njMatrix_specialUnitary (z w : ℂ)
    (hz : z * star z = 1) (hw : w * star w = 1) :
    njMatrix z w * (njMatrix z w).conjTranspose = 1 ∧ (njMatrix z w).det = 1 := by
  have hM := ExactCKMABFrames.ellNMatrix_specialUnitary z w hz hw
  have hP := columnCycle_specialUnitary
  simp only [njMatrix_eq_ellN_mul_cycle]
  constructor
  · calc
      _ = ExactCKMABFrames.ellNMatrix z w *
          (columnCycle * columnCycle.conjTranspose) *
          (ExactCKMABFrames.ellNMatrix z w).conjTranspose := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hP.1, mul_one, hM.1]
  · rw [Matrix.det_mul, hM.2, hP.2, one_mul]

private theorem n_input (z : ℂ) :
    Glennie.octMul (complexOctonion z) (nativeOctonionBasis 6) =
      (0, ⟨0, 0, z.re, -z.im⟩) := by
  have hb : nativeOctonionBasis 6 = (0, ⟨0, 0, 1, 0⟩) := rfl
  rw [hb]
  apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [complexOctonion, Glennie.octMul, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem j_input (w : ℂ) :
    Glennie.octMul (complexOctonion w) (nativeOctonionBasis 2) =
      (⟨0, 0, w.re, w.im⟩, 0) := by
  have hb : nativeOctonionBasis 2 = (⟨0, 0, 1, 0⟩, 0) := rfl
  rw [hb]
  apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [complexOctonion, Glennie.octMul, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem n_j_readout (z w : ℂ) :
    nativeOuterProductThird
      (Glennie.octMul (complexOctonion z) (nativeOctonionBasis 6))
      (Glennie.octMul (complexOctonion w) (nativeOctonionBasis 2)) =
      (⟨1/3, Complex.normSq z/3, Complex.normSq w/3,
        (0, ⟨0, 0, -z.re/3, z.im/3⟩),
        (⟨0, 0, -w.re/3, -w.im/3⟩, 0),
        (0, ⟨-(z*w).re/3, (z*w).im/3, 0, 0⟩)⟩ : Glennie.Albert) := by
  rw [n_input, j_input]
  apply Glennie.Albert.extExplicit
  all_goals first | (apply Prod.ext <;> apply Quaternion.ext) | skip
  all_goals
    norm_num [nativeOuterProductThird, Glennie.octNormSq, Quaternion.normSq_def',
      Glennie.octMul, Glennie.octConj, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring

private theorem complementary_readout (z w : ℂ) :
    nativeComplementaryPoint (njMatrix z w) =
      (⟨1/3, 1/3, 1/3,
        (0, ⟨0, 0, -z.re/3, z.im/3⟩),
        (⟨0, 0, -w.re/3, -w.im/3⟩, 0),
        (0, ⟨-(z*w).re/3, (z*w).im/3, 0, 0⟩)⟩ : Glennie.Albert) := by
  apply Glennie.Albert.extExplicit
  all_goals first | (apply Prod.ext <;> apply Quaternion.ext) | skip
  all_goals
    norm_num [nativeComplementaryPoint, njMatrix, fromTitsCoordinates,
      octonionFromTitsRow, Glennie.octConj, Matrix.smul_apply,
      Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring

/-- One actual native n/j binder for unit inputs; not nine point expansions. -/
theorem nativeOuterProduct_n_j_eq_complementary (z w : ℂ)
    (hz : Complex.normSq z = 1) (hw : Complex.normSq w = 1) :
    nativeOuterProductThird
      (Glennie.octMul (complexOctonion z) (nativeOctonionBasis 6))
      (Glennie.octMul (complexOctonion w) (nativeOctonionBasis 2)) =
        nativeComplementaryPoint (njMatrix z w) := by
  rw [n_j_readout, complementary_readout, hz, hw]

private theorem unit_product (z w : ℂ)
    (hz : z * star z = 1) (hw : w * star w = 1) :
    (z*w) * star (z*w) = 1 := by
  calc
    _ = (z * star z) * (w * star w) := by rw [star_mul]; ring
    _ = 1 := by rw [hz, hw, one_mul]

private theorem normSq_of_unit (z : ℂ) (hz : z * star z = 1) : Complex.normSq z = 1 := by
  have hnorm : (Complex.normSq z : ℂ) = z * star z := by
    simpa only [starRingEnd_apply, mul_comm] using
      (Complex.normSq_eq_conj_mul_self (z := z))
  simpa using congrArg Complex.re (hnorm.trans hz)

/-- Actual exact rational C phase is unit. -/
theorem phase_C_unit : exactPhases 2 * star (exactPhases 2) = 1 := by
  apply Complex.ext <;>
    norm_num [exactPhases, Complex.mul_re, Complex.mul_im, Complex.div_re,
      Complex.div_im, Complex.normSq_apply]

/-- Actual exact rational D phase is unit. -/
theorem phase_D_unit : exactPhases 3 * star (exactPhases 3) = 1 := by
  apply Complex.ext <;>
    norm_num [exactPhases, Complex.mul_re, Complex.mul_im, Complex.div_re,
      Complex.div_im, Complex.normSq_apply]

private theorem character_unit (s : PhaseIndex) :
    UnitaryErrorBases.ThreeCycleFourier.character s *
      star (UnitaryErrorBases.ThreeCycleFourier.character s) = 1 := by
  simp only [Complex.star_def, Complex.mul_conj,
    CompactAlbert.character_normSq_eq_one, Complex.ofReal_one]

theorem qThreeUnitary_specialUnitary (s : PhaseIndex) :
    qThreeUnitary s * (qThreeUnitary s).conjTranspose = 1 ∧ (qThreeUnitary s).det = 1 := by
  exact njMatrix_specialUnitary _ _ phase_C_unit
    (unit_product _ _ phase_D_unit (character_unit s))

private theorem character_product_sum (s t : PhaseIndex) :
    UnitaryErrorBases.ThreeCycleFourier.character t *
      UnitaryErrorBases.ThreeCycleFourier.character (s+t) =
      star (UnitaryErrorBases.ThreeCycleFourier.character t) *
        UnitaryErrorBases.ThreeCycleFourier.character s := by
  have h := congrArg (fun M : TitsComplexMatrix => M 0 2)
    (ExactCKMThreeHiddenFrames.twoInputMatrix_character s t)
  simpa [ExactCKMThreeHiddenFrames.twoInputMatrix,
    ExactCKMThreeHiddenFrames.qOneUnitary, Matrix.smul_apply] using h

/-- Generic input phase factor, using the already accepted q1 scalar identity. -/
theorem njMatrix_CD_character (s t : PhaseIndex) :
    njMatrix (exactPhases 2 * UnitaryErrorBases.ThreeCycleFourier.character t)
      (exactPhases 3 * UnitaryErrorBases.ThreeCycleFourier.character (s+t)) =
      star (UnitaryErrorBases.ThreeCycleFourier.character t) • qThreeUnitary s := by
  have hp : (exactPhases 2 * UnitaryErrorBases.ThreeCycleFourier.character t) *
      (exactPhases 3 * UnitaryErrorBases.ThreeCycleFourier.character (s+t)) =
      star (UnitaryErrorBases.ThreeCycleFourier.character t) *
        (exactPhases 2 * (exactPhases 3 * UnitaryErrorBases.ThreeCycleFourier.character s)) := by
    calc
      _ = (exactPhases 2 * exactPhases 3) *
          (UnitaryErrorBases.ThreeCycleFourier.character t *
           UnitaryErrorBases.ThreeCycleFourier.character (s+t)) := by ring
      _ = _ := by rw [character_product_sum]; ring
  have hstar (a b c : ℂ) : star a * star (b*c) = star a * star c * star b := by
    rw [star_mul]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [njMatrix, qThreeUnitary, Matrix.smul_apply, hp]
  all_goals try simp only [ExactCKMThreeHiddenFrames.character_add]
  all_goals try ring
  simpa only [starRingEnd_apply] using
    (hstar (exactPhases 3) (UnitaryErrorBases.ThreeCycleFourier.character s)
      (UnitaryErrorBases.ThreeCycleFourier.character t))

/-- Literal raw q3 native point at its uniform complementary matrix. -/
theorem qThreeFamilyPoint_eq_matrix (s t : PhaseIndex) :
    nativeFamilyPoint 3 s t = nativeComplementaryPoint
      (star (UnitaryErrorBases.ThreeCycleFourier.character t) • qThreeUnitary s) := by
  have hz : Complex.normSq (exactPhases 2 * UnitaryErrorBases.ThreeCycleFourier.character t) = 1 :=
    normSq_of_unit _ (unit_product _ _ phase_C_unit (character_unit t))
  have hw : Complex.normSq
      (exactPhases 3 * UnitaryErrorBases.ThreeCycleFourier.character (s+t)) = 1 :=
    normSq_of_unit _ (unit_product _ _ phase_D_unit (character_unit (s+t)))
  rw [nativeFamilyPoint, if_neg (by decide), if_neg (by decide), if_neg (by decide),
    nativeOuterProduct_n_j_eq_complementary _ _ hz hw, njMatrix_CD_character]

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

/-- Raw outcome order is again exactly reverse central0,2,1. -/
theorem qThreeFamily_eq_reverseCentral (s : PhaseIndex) :
    (fun t : Fin 3 => nativeFamilyPoint 3 s (t.val : PhaseIndex)) =
      nativeReverseCentralTriple (qThreeUnitary s) := by
  funext t
  fin_cases t
  · change nativeFamilyPoint 3 s (0 : PhaseIndex) = nativeComplementaryPoint (qThreeUnitary s)
    simpa only [character_zero, star_one, one_smul] using qThreeFamilyPoint_eq_matrix s 0
  · change nativeFamilyPoint 3 s (1 : PhaseIndex) = nativeComplementaryPoint
      ((UnitaryErrorBases.ThreeCycleFourier.omega ^ 2) • qThreeUnitary s)
    simpa only [character_one, star_omega] using qThreeFamilyPoint_eq_matrix s 1
  · change nativeFamilyPoint 3 s (2 : PhaseIndex) = nativeComplementaryPoint
      (UnitaryErrorBases.ThreeCycleFourier.omega • qThreeUnitary s)
    simpa only [character_two, star_omega_sq] using qThreeFamilyPoint_eq_matrix s 2

/-- Every actual raw C/D family frame is trace1, idempotent, orthogonal, sum1. -/
theorem qThreeFamily_frame (s : PhaseIndex) :
    Glennie.Frame (fun t : Fin 3 => nativeFamilyPoint 3 s (t.val : PhaseIndex)) := by
  rw [qThreeFamily_eq_reverseCentral]
  exact (native_central_triples_are_frames (qThreeUnitary s) (qThreeUnitary_specialUnitary s)).2

/-- Literal original frames10+s and unchanged raw outcome labels. -/
def qThreeFrameLabel (s : Fin 3) : Fin 13 := ⟨10 + s.val, by omega⟩

theorem nativePoint_qThree_frame_eq_family (s : Fin 3) :
    (fun t : Fin 3 => nativePoint (framePointIndex (qThreeFrameLabel s) t)) =
      (fun t : Fin 3 => nativeFamilyPoint 3 (s.val : PhaseIndex) (t.val : PhaseIndex)) := by
  funext t
  fin_cases s <;> fin_cases t <;> rfl

/-- Whole actual shared configuration frames10,11,12, points30..38. -/
theorem nativePoint_qThree_frames (s : Fin 3) :
    Glennie.Frame (fun t : Fin 3 => nativePoint (framePointIndex (qThreeFrameLabel s) t)) := by
  rw [nativePoint_qThree_frame_eq_family]
  exact qThreeFamily_frame (s.val : PhaseIndex)

end QuadraticCertificate.ExactCKMCDFrames

#print axioms QuadraticCertificate.ExactCKMCDFrames.njMatrix_specialUnitary
#print axioms QuadraticCertificate.ExactCKMCDFrames.nativeOuterProduct_n_j_eq_complementary
#print axioms QuadraticCertificate.ExactCKMCDFrames.qThreeFamily_eq_reverseCentral
#print axioms QuadraticCertificate.ExactCKMCDFrames.nativePoint_qThree_frames

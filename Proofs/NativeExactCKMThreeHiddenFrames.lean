module

public import NativeExactCKMFirstHiddenFrame

/-!
# All three raw q1 CKM frames from a uniform special-unitary matrix

The uniform matrix is anti-diagonal[character(s),-star(character(s)),1].
Raw outcome t is star(character(t)) times that matrix, hence the accepted
reverse central order. One generic two-complex-input native readout replaces
native point expansions; the only finite arithmetic is the scalar character
addition table and original labels. Frame4 is reused from its accepted owner.

The earlier staged input lemmas are private. Their small first-party input
reductions are adapted here to two independent complex inputs with public
endpoints; no accepted source is changed. No third-party proof body copied.
Inherited native/mathlib Apache-2.0 pins: compact-albert-recognition at
40d3b344180d9ddb78aaa2876873377c1e631515 and mathlib at
065356127b1dc0016f66b7283ce0ce2c4055aa55. Thanks to their contributors and
the original CKM construction. No release license assigned.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke,1676.
-/

@[expose] public section
noncomputable section
namespace QuadraticCertificate.ExactCKMThreeHiddenFrames
open CompactAlbert NativePolynomial
open NativePolynomial.ConfigurationResiduals
open UnitaryErrorBases.ComplexQuartet
open ExactCKMConfiguration

private theorem character_zero : UnitaryErrorBases.ThreeCycleFourier.character 0 = (1 : ℂ) := rfl

private theorem character_one : UnitaryErrorBases.ThreeCycleFourier.character 1 =
    UnitaryErrorBases.ThreeCycleFourier.omega := by
  rw [UnitaryErrorBases.ThreeCycleFourier.character,
    show (1 : PhaseIndex).val = 1 by decide, pow_one]

private theorem character_two : UnitaryErrorBases.ThreeCycleFourier.character 2 =
    UnitaryErrorBases.ThreeCycleFourier.omega ^ 2 := by
  rw [UnitaryErrorBases.ThreeCycleFourier.character,
    show (2 : PhaseIndex).val = 2 by decide]

/-- Exact finite phase multiplication, independent of native coordinates. -/
theorem character_add (s t : PhaseIndex) :
    UnitaryErrorBases.ThreeCycleFourier.character (s + t) =
      UnitaryErrorBases.ThreeCycleFourier.character s *
        UnitaryErrorBases.ThreeCycleFourier.character t := by
  have cases3 : ∀ i : PhaseIndex, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases cases3 s with rfl | rfl | rfl
  · simp only [zero_add, character_zero, one_mul]
  · rcases cases3 t with rfl | rfl | rfl
    · simp only [add_zero, character_zero, mul_one]
    · rw [show (1 + 1 : PhaseIndex) = 2 by decide, character_two, character_one, pow_two]
    · rw [show (1 + 2 : PhaseIndex) = 0 by decide, character_zero, character_one, character_two]
      calc
        1 = UnitaryErrorBases.ThreeCycleFourier.omega ^ 3 :=
          UnitaryErrorBases.ThreeCycleFourier.omega_cube.symm
        _ = _ := by ring
  · rcases cases3 t with rfl | rfl | rfl
    · simp only [add_zero, character_zero, mul_one]
    · rw [show (2 + 1 : PhaseIndex) = 0 by decide, character_zero, character_two, character_one]
      calc
        1 = UnitaryErrorBases.ThreeCycleFourier.omega ^ 3 :=
          UnitaryErrorBases.ThreeCycleFourier.omega_cube.symm
        _ = _ := by ring
    · rw [show (2 + 2 : PhaseIndex) = 1 by decide, character_one, character_two]
      calc
        UnitaryErrorBases.ThreeCycleFourier.omega =
            UnitaryErrorBases.ThreeCycleFourier.omega ^ 3 *
              UnitaryErrorBases.ThreeCycleFourier.omega := by
          rw [UnitaryErrorBases.ThreeCycleFourier.omega_cube, one_mul]
        _ = _ := by ring

private theorem character_mul_star (t : PhaseIndex) :
    UnitaryErrorBases.ThreeCycleFourier.character t *
      star (UnitaryErrorBases.ThreeCycleFourier.character t) = 1 := by
  simpa only [Complex.star_def, Complex.mul_conj,
    CompactAlbert.character_normSq_eq_one, Complex.ofReal_one]

private theorem character_square_star (t : PhaseIndex) :
    UnitaryErrorBases.ThreeCycleFourier.character t *
      UnitaryErrorBases.ThreeCycleFourier.character t =
        star (UnitaryErrorBases.ThreeCycleFourier.character t) := by
  have hc : UnitaryErrorBases.ThreeCycleFourier.character t ^ 3 = 1 := by
    rw [UnitaryErrorBases.ThreeCycleFourier.character, ← pow_mul,
      Nat.mul_comm t.val 3, pow_mul,
      UnitaryErrorBases.ThreeCycleFourier.omega_cube, one_pow]
  calc
    _ = (UnitaryErrorBases.ThreeCycleFourier.character t ^ 3) *
        star (UnitaryErrorBases.ThreeCycleFourier.character t) := by
      rw [show UnitaryErrorBases.ThreeCycleFourier.character t ^ 3 *
          star (UnitaryErrorBases.ThreeCycleFourier.character t) =
          (UnitaryErrorBases.ThreeCycleFourier.character t *
           UnitaryErrorBases.ThreeCycleFourier.character t) *
          (UnitaryErrorBases.ThreeCycleFourier.character t *
           star (UnitaryErrorBases.ThreeCycleFourier.character t)) by ring,
        character_mul_star, mul_one]
    _ = _ := by rw [hc, one_mul]

/-- Generic raw q1 matrix before the phase-addition simplification. -/
def twoInputMatrix (z w : ℂ) : TitsComplexMatrix :=
  !![0, 0, z*w; 0, -star w, 0; star z, 0, 0]

/-- The matrix for raw frame s. No determinant gauge or permutation is inserted. -/
def qOneUnitary (s : PhaseIndex) : TitsComplexMatrix :=
  !![0, 0, UnitaryErrorBases.ThreeCycleFourier.character s;
     0, -star (UnitaryErrorBases.ThreeCycleFourier.character s), 0;
     1, 0, 0]

private theorem j_input (z : ℂ) :
    Glennie.octMul (complexOctonion z) (nativeOctonionBasis 2) =
      (⟨0, 0, z.re, z.im⟩, 0) := by
  have hj : nativeOctonionBasis 2 = (⟨0, 0, 1, 0⟩, 0) := rfl
  rw [hj]
  apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [complexOctonion, Glennie.octMul, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem ell_input (w : ℂ) :
    Glennie.octMul (complexOctonion w) (nativeOctonionBasis 4) =
      (0, ⟨w.re, w.im, 0, 0⟩) := by
  have hell : nativeOctonionBasis 4 = (0, 1) := rfl
  rw [hell]
  apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [complexOctonion, Glennie.octMul, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem outer_readout (z w : ℂ) :
    nativeOuterProductThird
      (⟨0, 0, z.re, z.im⟩, 0) (0, ⟨w.re, w.im, 0, 0⟩) =
      (⟨1/3, Complex.normSq z/3, Complex.normSq w/3,
        (⟨0, 0, -z.re/3, -z.im/3⟩, 0),
        (0, ⟨-w.re/3, -w.im/3, 0, 0⟩),
        (0, ⟨0, 0, -(z*w).re/3, -(z*w).im/3⟩)⟩ : Glennie.Albert) := by
  apply Glennie.Albert.extExplicit
  all_goals first | (apply Prod.ext <;> apply Quaternion.ext) | skip
  all_goals
    norm_num [nativeOuterProductThird, Glennie.octNormSq, Quaternion.normSq_def',
      Glennie.octMul, Glennie.octConj, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring

private theorem complementary_readout (z w : ℂ) :
    nativeComplementaryPoint (twoInputMatrix z w) =
      (⟨1/3, 1/3, 1/3,
        (⟨0, 0, -z.re/3, -z.im/3⟩, 0),
        (0, ⟨-w.re/3, -w.im/3, 0, 0⟩),
        (0, ⟨0, 0, -(z*w).re/3, -(z*w).im/3⟩)⟩ : Glennie.Albert) := by
  apply Glennie.Albert.extExplicit
  all_goals first | (apply Prod.ext <;> apply Quaternion.ext) | skip
  all_goals
    norm_num [nativeComplementaryPoint, twoInputMatrix, fromTitsCoordinates,
      octonionFromTitsRow, Glennie.octConj, Matrix.smul_apply,
      Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring

/-- Generic native binder for unit complex inputs on j and ell. -/
theorem nativeOuterProduct_j_ell_eq_complementary (z w : ℂ)
    (hz : Complex.normSq z = 1) (hw : Complex.normSq w = 1) :
    nativeOuterProductThird
      (Glennie.octMul (complexOctonion z) (nativeOctonionBasis 2))
      (Glennie.octMul (complexOctonion w) (nativeOctonionBasis 4)) =
        nativeComplementaryPoint (twoInputMatrix z w) := by
  rw [j_input, ell_input, outer_readout, complementary_readout, hz, hw]

/-- Exact matrix phase factor, retaining raw t as the reverse central phase. -/
theorem twoInputMatrix_character (s t : PhaseIndex) :
    twoInputMatrix (UnitaryErrorBases.ThreeCycleFourier.character t)
      (UnitaryErrorBases.ThreeCycleFourier.character (s+t)) =
      star (UnitaryErrorBases.ThreeCycleFourier.character t) • qOneUnitary s := by
  have hp : UnitaryErrorBases.ThreeCycleFourier.character t *
      UnitaryErrorBases.ThreeCycleFourier.character (s+t) =
      star (UnitaryErrorBases.ThreeCycleFourier.character t) *
        UnitaryErrorBases.ThreeCycleFourier.character s := by
    rw [character_add]
    calc
      _ = UnitaryErrorBases.ThreeCycleFourier.character s *
          (UnitaryErrorBases.ThreeCycleFourier.character t *
           UnitaryErrorBases.ThreeCycleFourier.character t) := by ring
      _ = _ := by rw [character_square_star]; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoInputMatrix, qOneUnitary, Matrix.smul_apply, hp]
  all_goals rw [character_add, map_mul]
  all_goals ring

theorem qOneUnitary_specialUnitary (s : PhaseIndex) :
    qOneUnitary s * (qOneUnitary s).conjTranspose = 1 ∧ (qOneUnitary s).det = 1 := by
  have hc := character_mul_star s
  have hsc : star (UnitaryErrorBases.ThreeCycleFourier.character s) *
      UnitaryErrorBases.ThreeCycleFourier.character s = 1 := by
    simpa only [mul_comm] using hc
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [qOneUnitary, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.conjTranspose_apply, Matrix.one_apply]
    · change UnitaryErrorBases.ThreeCycleFourier.character s *
        star (UnitaryErrorBases.ThreeCycleFourier.character s) = 1
      exact hc
    · change star (UnitaryErrorBases.ThreeCycleFourier.character s) *
        UnitaryErrorBases.ThreeCycleFourier.character s = 1
      exact hsc
  · simpa [qOneUnitary, Matrix.det_fin_three] using hc

/-- Uniform actual native matrix point for every raw q1,s,t label. -/
theorem qOneFamilyPoint_eq_matrix (s t : PhaseIndex) :
    nativeFamilyPoint 1 s t = nativeComplementaryPoint
      (star (UnitaryErrorBases.ThreeCycleFourier.character t) • qOneUnitary s) := by
  rw [nativeFamilyPoint, if_neg (by decide), if_pos rfl,
    nativeOuterProduct_j_ell_eq_complementary _ _
      (CompactAlbert.character_normSq_eq_one t)
      (CompactAlbert.character_normSq_eq_one (s+t)),
    twoInputMatrix_character]

private theorem star_omega : star UnitaryErrorBases.ThreeCycleFourier.omega =
    UnitaryErrorBases.ThreeCycleFourier.omega ^ 2 := by
  have h := character_square_star (1 : PhaseIndex)
  rw [character_one] at h
  simpa only [pow_two] using h.symm

private theorem star_omega_sq : star (UnitaryErrorBases.ThreeCycleFourier.omega ^ 2) =
    UnitaryErrorBases.ThreeCycleFourier.omega := by
  have h := congrArg (fun z : ℂ => star z) star_omega
  simpa only [star_star] using h.symm

/-- Uniform whole-triple binder, in the same reverse order for all s. -/
theorem qOneFamily_eq_reverseCentral (s : PhaseIndex) :
    (fun t : Fin 3 => nativeFamilyPoint 1 s (t.val : PhaseIndex)) =
      nativeReverseCentralTriple (qOneUnitary s) := by
  funext t
  fin_cases t
  · change nativeFamilyPoint 1 s (0 : PhaseIndex) = nativeComplementaryPoint (qOneUnitary s)
    simpa only [character_zero, star_one, one_smul] using qOneFamilyPoint_eq_matrix s 0
  · change nativeFamilyPoint 1 s (1 : PhaseIndex) = nativeComplementaryPoint
      ((UnitaryErrorBases.ThreeCycleFourier.omega ^ 2) • qOneUnitary s)
    simpa only [character_one, star_omega] using qOneFamilyPoint_eq_matrix s 1
  · change nativeFamilyPoint 1 s (2 : PhaseIndex) = nativeComplementaryPoint
      (UnitaryErrorBases.ThreeCycleFourier.omega • qOneUnitary s)
    simpa only [character_two, star_omega_sq] using qOneFamilyPoint_eq_matrix s 2

/-- Three actual raw q1 frames; s0 reuses the independently accepted frame4. -/
theorem qOneFamily_frame (s : PhaseIndex) :
    Glennie.Frame (fun t : Fin 3 => nativeFamilyPoint 1 s (t.val : PhaseIndex)) := by
  by_cases hs : s = 0
  · subst s
    exact ExactCKMFirstHiddenFrame.firstHiddenFamily_frame
  · rw [qOneFamily_eq_reverseCentral]
    exact (native_central_triples_are_frames (qOneUnitary s)
      (qOneUnitary_specialUnitary s)).2

/-- Original grouped frame4+s, with the original outcome t unchanged. -/
def qOneFrameLabel (s : Fin 3) : Fin 13 := ⟨4 + s.val, by omega⟩

theorem nativePoint_qOne_frame_eq_family (s : Fin 3) :
    (fun t : Fin 3 => nativePoint (framePointIndex (qOneFrameLabel s) t)) =
      (fun t : Fin 3 => nativeFamilyPoint 1 (s.val : PhaseIndex) (t.val : PhaseIndex)) := by
  funext t
  fin_cases s <;> fin_cases t <;> rfl

/-- Whole actual shared frames4,5,6, preserving every original point label. -/
theorem nativePoint_qOne_frames (s : Fin 3) :
    Glennie.Frame (fun t : Fin 3 => nativePoint (framePointIndex (qOneFrameLabel s) t)) := by
  rw [nativePoint_qOne_frame_eq_family]
  exact qOneFamily_frame (s.val : PhaseIndex)

end QuadraticCertificate.ExactCKMThreeHiddenFrames

#print axioms QuadraticCertificate.ExactCKMThreeHiddenFrames.nativeOuterProduct_j_ell_eq_complementary
#print axioms QuadraticCertificate.ExactCKMThreeHiddenFrames.qOneFamily_eq_reverseCentral
#print axioms QuadraticCertificate.ExactCKMThreeHiddenFrames.nativePoint_qOne_frames

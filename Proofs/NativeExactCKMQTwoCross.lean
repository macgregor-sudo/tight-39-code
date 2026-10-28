module

public import NativeCoordinateTracePairing
public import NativeExactCKMABFrames

@[expose] public section

/-!
All original cross equations between the three actual A/B frames7,8,9.
The existing q2 matrices have a common three-entry support. Their complex
trace pairing is1+character(s-u)+character(u-s), hence zero for distinct
frame labels. Outcome phases preserve that complex zero. The accepted
actual point binder and native overlap theorem then supply every original
cross-row value, with its original constant subtraction and same point.

There are no native coordinate expansions by outcome pair and no supplied
frame, norm, gauge or row-zero premises. The q2 frame labels, point family,
reverse central outcome order and coefficient values remain in their
accepted owners. Only the increasing original frame-pair index is named here.

First-party elementary matrix/character algebra and accepted native theorem
composition, with no novelty claim or copied proof body. Inherited native
Apache-2.0 provenance remains in THIRD_PARTY_NOTICES.md#native-albert-code and imports,
https://github.com/macgregor-sudo/compact-albert-recognition at
40d3b344180d9ddb78aaa2876873377c1e631515. Lean4.35.0-rc2; mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55. Thanks to their contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke,1676. No release license is selected here.
-/

noncomputable section

namespace QuadraticCertificate.ExactCKMQTwoCross

open NativePolynomial CompactAlbert
open NativePolynomial.ConfigurationResiduals
open NativePolynomial.ConfigurationResiduals.MixedCoefficients
open NativePolynomial.ConfigurationResiduals.Evaluation
open NativePolynomial.CoordinateMaps ConfigurationResidualIndices
open UnitaryErrorBases.ComplexQuartet UnitaryErrorBases.ThreeCycleFourier
open QuadraticCertificate.ExactCKMConfiguration
open QuadraticCertificate.ExactCKMABFrames

/-- Increasing original labels7+s,7+u; no new ordering of the three frames. -/
def qTwoFramePair (s u : Fin 3) (hsu : s < u) : Pair 13 :=
  ⟨(qTwoFrameLabel s, qTwoFrameLabel u), by
    change 7 + s.val < 7 + u.val
    have h : s.val < u.val := hsu
    omega⟩

private theorem character_zero : character 0 = (1 : ℂ) := rfl

private theorem character_one : character 1 = omega := by
  rw [character, show (1 : PhaseIndex).val = 1 by decide, pow_one]

private theorem character_two : character 2 = omega ^ 2 := by
  rw [character, show (2 : PhaseIndex).val = 2 by decide]

private theorem character_unit (a : PhaseIndex) :
    character a * star (character a) = 1 := by
  simp only [Complex.star_def, Complex.mul_conj,
    CompactAlbert.character_normSq_eq_one, Complex.ofReal_one]

private theorem character_star (a : PhaseIndex) :
    star (character a) = character (-a) := by
  have hneg : character a * character (-a) = 1 := by
    rw [← ExactCKMThreeHiddenFrames.character_add, add_neg_cancel, character_zero]
  calc
    star (character a) = (character a * character (-a)) * star (character a) := by
      rw [hneg, one_mul]
    _ = character (-a) * (character a * star (character a)) := by ring
    _ = character (-a) := by rw [character_unit, mul_one]

private theorem character_pair (s u : PhaseIndex) :
    character s * star (character u) = character (s-u) := by
  rw [character_star, ← ExactCKMThreeHiddenFrames.character_add, sub_eq_add_neg]

private theorem character_nonzero_sum (d : PhaseIndex) (hd : d ≠ 0) :
    (1 : ℂ) + character d + character (-d) = 0 := by
  have cases3 : ∀ t : PhaseIndex, t = 0 ∨ t = 1 ∨ t = 2 := by decide
  rcases cases3 d with h | h | h
  · exact False.elim (hd h)
  · subst d
    rw [show (-1 : PhaseIndex) = 2 by decide,
      character_one, character_two, omega_sq]
    ring
  · subst d
    rw [show (-2 : PhaseIndex) = 1 by decide,
      character_two, character_one, omega_sq]
    ring

private theorem ellNMatrix_trace_pair (z w z' w' : ℂ) :
    (ellNMatrix z w * (ellNMatrix z' w').conjTranspose).trace =
      (z*w) * star (z'*w') + star w * w' + star z * z' := by
  -- Expand applied matrix products before exposing the literal rows, so
  -- matrix-notation simp rules cannot introduce a remaining vecMul.
  simp only [Matrix.trace_fin_three, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_three]
  norm_num [ellNMatrix] <;> ring

/-- Exact monomial trace pairing, before imposing distinct frame labels. -/
theorem qTwo_matrix_trace_formula (s u : PhaseIndex) :
    (qTwoUnitary s * (qTwoUnitary u).conjTranspose).trace =
      1 + character (s-u) + character (u-s) := by
  rw [qTwoUnitary, qTwoUnitary, ellNMatrix_trace_pair]
  calc
    _ = (exactPhases 0 * star (exactPhases 0)) *
          (exactPhases 1 * star (exactPhases 1)) *
          (character s * star (character u)) +
        (exactPhases 1 * star (exactPhases 1)) *
          (star (character s) * character u) +
        (exactPhases 0 * star (exactPhases 0)) := by
      simp only [star_mul]
      ring
    _ = character s * star (character u) +
        star (character s) * character u + 1 := by
      rw [phase_A_unit, phase_B_unit]
      ring
    _ = 1 + character (s-u) + character (u-s) := by
      rw [character_pair, mul_comm (star (character s)) (character u), character_pair]
      ring

/-- Distinct actual q2 frame matrices are complex trace-orthogonal. -/
theorem qTwo_matrix_trace_zero (s u : PhaseIndex) (hsu : s ≠ u) :
    (qTwoUnitary s * (qTwoUnitary u).conjTranspose).trace = 0 := by
  rw [qTwo_matrix_trace_formula]
  have hd : s-u ≠ 0 := sub_ne_zero.mpr hsu
  have hreverse : u-s = -(s-u) := by ring
  rw [hreverse]
  exact character_nonzero_sum (s-u) hd

private theorem qTwo_phased_trace_zero (s u : PhaseIndex) (hsu : s ≠ u)
    (a b : PhaseIndex) :
    ((star (character a) • qTwoUnitary s) *
      (star (character b) • qTwoUnitary u).conjTranspose).trace = 0 := by
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, qTwo_matrix_trace_zero s u hsu, smul_zero]

/-- All outcomes of two distinct actual q2 family frames have overlap1/3. -/
theorem qTwo_family_pairing (s u : PhaseIndex) (hsu : s ≠ u)
    (a b : PhaseIndex) :
    coordinatePairing (upperCoordinates (nativeFamilyPoint 2 s a))
      (upperCoordinates (nativeFamilyPoint 2 u b)) = (1/3 : ℝ) := by
  rw [coordinatePairing_upperCoordinates_eq_native_trace,
    qTwoFamilyPoint_eq_matrix, qTwoFamilyPoint_eq_matrix,
    nativeComplementaryPoint_overlap, qTwo_phased_trace_zero s u hsu a b]
  norm_num

private theorem qTwo_original_pairing (s u : Fin 3) (hsu : s < u)
    (a b : PhaseIndex) :
    coordinatePairing
      (upperCoordinates (nativePoint (framePointIndex (qTwoFrameLabel s) a)))
      (upperCoordinates (nativePoint (framePointIndex (qTwoFrameLabel u) b))) =
        (1/3 : ℝ) := by
  have hphase : (s.val : PhaseIndex) ≠ (u.val : PhaseIndex) := by
    intro h
    have hv := congrArg (fun z : PhaseIndex => ZMod.val z) h
    rw [ZMod.val_natCast_of_lt s.isLt, ZMod.val_natCast_of_lt u.isLt] at hv
    exact (ne_of_lt hsu) (Fin.ext hv)
  rw [congrFun (nativePoint_qTwo_frame_eq_family s) a,
    congrFun (nativePoint_qTwo_frame_eq_family u) b]
  exact qTwo_family_pairing (s.val : PhaseIndex) (u.val : PhaseIndex) hphase
    (a.val : PhaseIndex) (b.val : PhaseIndex)

/-- All27 canonical original cross-row values between frames7,8,9. -/
theorem qTwo_cross_value_zero (s u : Fin 3) (hsu : s < u) (a b : PhaseIndex) :
    valueRow (1/2 : ℝ) (1/3 : ℝ) pointCoordinates
      (gNumber (gCross (qTwoFramePair s u hsu) a b)) = 0 := by
  simp only [valueRow, Equiv.symm_apply_apply, valueResidual, gCross, qTwoFramePair]
  rw [pointValues_pointCoordinates, pointValues_pointCoordinates]
  exact sub_eq_zero.mpr (qTwo_original_pairing s u hsu a b)

/-- The same27 original numbered polynomials vanish at the unchanged real point. -/
theorem qTwo_cross_eval_zero (s u : Fin 3) (hsu : s < u) (a b : PhaseIndex) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross (qTwoFramePair s u hsu) a b))) = 0 := by
  rw [gRow_eval]
  exact qTwo_cross_value_zero s u hsu a b

/-- The identical original evaluations reject the changed value1. -/
theorem qTwo_cross_changed_value_control (s u : Fin 3) (hsu : s < u)
    (a b : PhaseIndex) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross (qTwoFramePair s u hsu) a b))) ≠ 1 := by
  rw [qTwo_cross_eval_zero]
  exact zero_ne_one

/-- First previously unproved frame-pair representative: frames7/9, outcomes0/0. -/
theorem original_g3033_representative :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow
        (1/2 : ℝ) (1/3 : ℝ) (3033 : Fin 3159)) = 0 := by
  have hn : gNumber (gCross (qTwoFramePair 0 2 (by decide)) 0 0) =
      (3033 : Fin 3159) := by
    apply Fin.ext
    rw [gNumber_cross_val]
    decide +kernel
  rw [← hn]
  exact qTwo_cross_eval_zero 0 2 (by decide) 0 0

/-- Second new strict frame pair: frames8/9, outcomes0/0. -/
theorem original_g3069_representative :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow
        (1/2 : ℝ) (1/3 : ℝ) (3069 : Fin 3159)) = 0 := by
  have hn : gNumber (gCross (qTwoFramePair 1 2 (by decide)) 0 0) =
      (3069 : Fin 3159) := by
    apply Fin.ext
    rw [gNumber_cross_val]
    decide +kernel
  rw [← hn]
  exact qTwo_cross_eval_zero 1 2 (by decide) 0 0

/-- The old frame7/8 outcome-zero equation follows from the uniform matrix proof. -/
theorem original_g3024_regression :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow
        (1/2 : ℝ) (1/3 : ℝ) (3024 : Fin 3159)) = 0 := by
  have hn : gNumber (gCross (qTwoFramePair 0 1 (by decide)) 0 0) =
      (3024 : Fin 3159) := by
    apply Fin.ext
    rw [gNumber_cross_val]
    decide +kernel
  rw [← hn]
  exact qTwo_cross_eval_zero 0 1 (by decide) 0 0

end QuadraticCertificate.ExactCKMQTwoCross

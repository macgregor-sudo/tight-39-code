module

public import NativeCoordinateTracePairing
public import NativeExactCKMThreeHiddenFrames

@[expose] public section

/-!
All original cross equations between the three actual j/ell frames4,5,6.
The existing q1 matrices have a common three-entry support. Their complex
trace pairing is1+character(s-u)+character(u-s), hence zero for distinct
frame labels. Outcome phases preserve that complex zero. The accepted
actual point binder and native overlap theorem then supply every original
cross-row value, with its original constant subtraction and same point.

There are no native coordinate expansions by outcome pair and no supplied
frame, norm, gauge or row-zero premises. The q1 frame labels, point family,
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

namespace QuadraticCertificate.ExactCKMQOneCross

open NativePolynomial CompactAlbert
open NativePolynomial.ConfigurationResiduals
open NativePolynomial.ConfigurationResiduals.MixedCoefficients
open NativePolynomial.ConfigurationResiduals.Evaluation
open NativePolynomial.CoordinateMaps ConfigurationResidualIndices
open UnitaryErrorBases.ComplexQuartet UnitaryErrorBases.ThreeCycleFourier
open QuadraticCertificate.ExactCKMConfiguration
open QuadraticCertificate.ExactCKMThreeHiddenFrames

/-- Increasing original labels4+s,4+u; no new ordering of the three frames. -/
def qOneFramePair (s u : Fin 3) (hsu : s < u) : Pair 13 :=
  ⟨(qOneFrameLabel s, qOneFrameLabel u), by
    change 4 + s.val < 4 + u.val
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

private theorem qOne_matrix_trace_pair (s u : PhaseIndex) :
    (qOneUnitary s * (qOneUnitary u).conjTranspose).trace =
      character s * star (character u) +
      star (character s) * character u + 1 := by
  simp only [Matrix.trace_fin_three, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_three]
  norm_num [qOneUnitary] <;> ring

/-- Exact monomial trace pairing for the original j/ell frame matrices. -/
theorem qOne_matrix_trace_formula (s u : PhaseIndex) :
    (qOneUnitary s * (qOneUnitary u).conjTranspose).trace =
      1 + character (s-u) + character (u-s) := by
  rw [qOne_matrix_trace_pair, character_pair s u,
    mul_comm (star (character s)) (character u), character_pair u s]
  ring

/-- Distinct actual q1 frame matrices are complex trace-orthogonal. -/
theorem qOne_matrix_trace_zero (s u : PhaseIndex) (hsu : s ≠ u) :
    (qOneUnitary s * (qOneUnitary u).conjTranspose).trace = 0 := by
  rw [qOne_matrix_trace_formula]
  have hd : s-u ≠ 0 := sub_ne_zero.mpr hsu
  have hreverse : u-s = -(s-u) := by ring
  rw [hreverse]
  exact character_nonzero_sum (s-u) hd

private theorem qOne_phased_trace_zero (s u : PhaseIndex) (hsu : s ≠ u)
    (a b : PhaseIndex) :
    ((star (character a) • qOneUnitary s) *
      (star (character b) • qOneUnitary u).conjTranspose).trace = 0 := by
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, qOne_matrix_trace_zero s u hsu, smul_zero]

/-- All outcomes of two distinct actual q1 family frames have overlap1/3. -/
theorem qOne_family_pairing (s u : PhaseIndex) (hsu : s ≠ u)
    (a b : PhaseIndex) :
    coordinatePairing (upperCoordinates (nativeFamilyPoint 1 s a))
      (upperCoordinates (nativeFamilyPoint 1 u b)) = (1/3 : ℝ) := by
  rw [coordinatePairing_upperCoordinates_eq_native_trace,
    qOneFamilyPoint_eq_matrix, qOneFamilyPoint_eq_matrix,
    nativeComplementaryPoint_overlap, qOne_phased_trace_zero s u hsu a b]
  norm_num

private theorem qOne_original_pairing (s u : Fin 3) (hsu : s < u)
    (a b : PhaseIndex) :
    coordinatePairing
      (upperCoordinates (nativePoint (framePointIndex (qOneFrameLabel s) a)))
      (upperCoordinates (nativePoint (framePointIndex (qOneFrameLabel u) b))) =
        (1/3 : ℝ) := by
  have hphase : (s.val : PhaseIndex) ≠ (u.val : PhaseIndex) := by
    intro h
    have hv := congrArg (fun z : PhaseIndex => ZMod.val z) h
    rw [ZMod.val_natCast_of_lt s.isLt, ZMod.val_natCast_of_lt u.isLt] at hv
    exact (ne_of_lt hsu) (Fin.ext hv)
  rw [congrFun (nativePoint_qOne_frame_eq_family s) a,
    congrFun (nativePoint_qOne_frame_eq_family u) b]
  exact qOne_family_pairing (s.val : PhaseIndex) (u.val : PhaseIndex) hphase
    (a.val : PhaseIndex) (b.val : PhaseIndex)

/-- All27 canonical original cross-row values between frames4,5,6. -/
theorem qOne_cross_value_zero (s u : Fin 3) (hsu : s < u) (a b : PhaseIndex) :
    valueRow (1/2 : ℝ) (1/3 : ℝ) pointCoordinates
      (gNumber (gCross (qOneFramePair s u hsu) a b)) = 0 := by
  simp only [valueRow, Equiv.symm_apply_apply, valueResidual, gCross, qOneFramePair]
  rw [pointValues_pointCoordinates, pointValues_pointCoordinates]
  exact sub_eq_zero.mpr (qOne_original_pairing s u hsu a b)

/-- The same27 original numbered polynomials vanish at the unchanged real point. -/
theorem qOne_cross_eval_zero (s u : Fin 3) (hsu : s < u) (a b : PhaseIndex) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross (qOneFramePair s u hsu) a b))) = 0 := by
  rw [gRow_eval]
  exact qOne_cross_value_zero s u hsu a b

/-- The identical original evaluations reject the changed value1. -/
theorem qOne_cross_changed_value_control (s u : Fin 3) (hsu : s < u)
    (a b : PhaseIndex) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross (qOneFramePair s u hsu) a b))) ≠ 1 := by
  rw [qOne_cross_eval_zero]
  exact zero_ne_one

/-- First actual q1 cross row: frames4/5, outcomes0/0, row2835. -/
theorem original_g2835_representative :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow
        (1/2 : ℝ) (1/3 : ℝ) (2835 : Fin 3159)) = 0 := by
  have hn : gNumber (gCross (qOneFramePair 0 1 (by decide)) 0 0) =
      (2835 : Fin 3159) := by
    apply Fin.ext
    rw [gNumber_cross_val]
    decide +kernel
  rw [← hn]
  exact qOne_cross_eval_zero 0 1 (by decide) 0 0

end QuadraticCertificate.ExactCKMQOneCross

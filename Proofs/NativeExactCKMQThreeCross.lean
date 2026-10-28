module

public import NativeExactCKMCDFrames
public import NativeCoordinateTracePairing

/-!
# Original cross equations among the three actual C/D frames10,11,12

One sparse complex trace identity is1+character(s-u)+character(u-s), zero
for distinct raw frame labels. The actual reverse-central outcome phases
preserve that zero. The accepted point binder, native overlap theorem and
coordinate/native trace bridge give the original G equations at their same
real point, including the constant subtraction. G3132 is the first literal
numbered representative; the uniform theorem covers exactly27rows.

No native point or Jordan pair is expanded by outcome. The scalar character
and original-row composition proofs adapt the first-party q2 cross-proof pattern, with new q3 sparse matrices and original row labels.
That numerical module is neither imported nor edited; inherited scalar
character identities are elementary. Native/mathlib Apache-2.0 pins remain in imported owners:
compact-albert-recognition40d3b344180d9ddb78aaa2876873377c1e631515;
mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55. Thanks to their
contributors and the original CKM construction. No release license assigned.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke,1676.
-/

@[expose] public section
noncomputable section
namespace QuadraticCertificate.ExactCKMQThreeCross
open NativePolynomial CompactAlbert
open NativePolynomial.ConfigurationResiduals
open NativePolynomial.ConfigurationResiduals.MixedCoefficients
open NativePolynomial.ConfigurationResiduals.Evaluation
open NativePolynomial.CoordinateMaps ConfigurationResidualIndices
open UnitaryErrorBases.ComplexQuartet
open ExactCKMConfiguration ExactCKMCDFrames

/-- Increasing original frames10+s,10+u, with unchanged outcome order. -/
def qThreeFramePair (s u : Fin 3) (hsu : s < u) : Pair 13 :=
  ⟨(qThreeFrameLabel s, qThreeFrameLabel u), by
    change 10 + s.val < 10 + u.val
    have h : s.val < u.val := hsu
    omega⟩

/-- The first literal original q3 cross-row number, not a new row ordering. -/
theorem qThree_first_row_number :
    gNumber (gCross (qThreeFramePair 0 1 (by decide)) 0 0) = (3132 : Fin 3159) := by
  apply Fin.ext
  rw [gNumber_cross_val]
  decide +kernel

private theorem character_zero : UnitaryErrorBases.ThreeCycleFourier.character 0 = (1 : ℂ) := rfl

private theorem character_one : UnitaryErrorBases.ThreeCycleFourier.character 1 =
    UnitaryErrorBases.ThreeCycleFourier.omega := by
  rw [UnitaryErrorBases.ThreeCycleFourier.character,
    show (1 : PhaseIndex).val = 1 by decide, pow_one]

private theorem character_two : UnitaryErrorBases.ThreeCycleFourier.character 2 =
    UnitaryErrorBases.ThreeCycleFourier.omega ^ 2 := by
  rw [UnitaryErrorBases.ThreeCycleFourier.character,
    show (2 : PhaseIndex).val = 2 by decide]

private theorem character_unit (a : PhaseIndex) :
    UnitaryErrorBases.ThreeCycleFourier.character a *
      star (UnitaryErrorBases.ThreeCycleFourier.character a) = 1 := by
  simp only [Complex.star_def, Complex.mul_conj,
    CompactAlbert.character_normSq_eq_one, Complex.ofReal_one]

private theorem character_star (a : PhaseIndex) :
    star (UnitaryErrorBases.ThreeCycleFourier.character a) =
      UnitaryErrorBases.ThreeCycleFourier.character (-a) := by
  have hn : UnitaryErrorBases.ThreeCycleFourier.character a *
      UnitaryErrorBases.ThreeCycleFourier.character (-a) = 1 := by
    rw [← ExactCKMThreeHiddenFrames.character_add, add_neg_cancel, character_zero]
  calc
    _ = (UnitaryErrorBases.ThreeCycleFourier.character a *
        UnitaryErrorBases.ThreeCycleFourier.character (-a)) *
        star (UnitaryErrorBases.ThreeCycleFourier.character a) := by rw [hn, one_mul]
    _ = UnitaryErrorBases.ThreeCycleFourier.character (-a) *
        (UnitaryErrorBases.ThreeCycleFourier.character a *
         star (UnitaryErrorBases.ThreeCycleFourier.character a)) := by ring
    _ = _ := by rw [character_unit, mul_one]

private theorem character_pair (s u : PhaseIndex) :
    UnitaryErrorBases.ThreeCycleFourier.character s *
      star (UnitaryErrorBases.ThreeCycleFourier.character u) =
        UnitaryErrorBases.ThreeCycleFourier.character (s-u) := by
  rw [character_star, ← ExactCKMThreeHiddenFrames.character_add, sub_eq_add_neg]

private theorem character_nonzero_sum (d : PhaseIndex) (hd : d ≠ 0) :
    (1 : ℂ) + UnitaryErrorBases.ThreeCycleFourier.character d +
      UnitaryErrorBases.ThreeCycleFourier.character (-d) = 0 := by
  have cases3 : ∀ t : PhaseIndex, t = 0 ∨ t = 1 ∨ t = 2 := by decide
  rcases cases3 d with h | h | h
  · exact False.elim (hd h)
  · subst d
    rw [show (-1 : PhaseIndex) = 2 by decide, character_one, character_two,
      UnitaryErrorBases.ThreeCycleFourier.omega_sq]
    ring
  · subst d
    rw [show (-2 : PhaseIndex) = 1 by decide, character_two, character_one,
      UnitaryErrorBases.ThreeCycleFourier.omega_sq]
    ring

/-- Sparse trace formula before unit or phase hypotheses; no native expansion. -/
theorem njMatrix_trace_pair (z w z' w' : ℂ) :
    (njMatrix z w * (njMatrix z' w').conjTranspose).trace =
      (z*w) * star (z'*w') + star w * w' + star z * z' := by
  simp only [Matrix.trace_fin_three, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_three]
  norm_num [njMatrix] <;> ring

/-- Actual C/D frame matrices have the exact three-character trace pairing. -/
theorem qThree_matrix_trace_formula (s u : PhaseIndex) :
    (qThreeUnitary s * (qThreeUnitary u).conjTranspose).trace =
      1 + UnitaryErrorBases.ThreeCycleFourier.character (s-u) +
        UnitaryErrorBases.ThreeCycleFourier.character (u-s) := by
  rw [qThreeUnitary, qThreeUnitary, njMatrix_trace_pair]
  calc
    _ = (exactPhases 2 * star (exactPhases 2)) *
          (exactPhases 3 * star (exactPhases 3)) *
          (UnitaryErrorBases.ThreeCycleFourier.character s *
           star (UnitaryErrorBases.ThreeCycleFourier.character u)) +
        (exactPhases 3 * star (exactPhases 3)) *
          (star (UnitaryErrorBases.ThreeCycleFourier.character s) *
           UnitaryErrorBases.ThreeCycleFourier.character u) +
        (exactPhases 2 * star (exactPhases 2)) := by
      simp only [star_mul]
      ring
    _ = UnitaryErrorBases.ThreeCycleFourier.character s *
          star (UnitaryErrorBases.ThreeCycleFourier.character u) +
        star (UnitaryErrorBases.ThreeCycleFourier.character s) *
          UnitaryErrorBases.ThreeCycleFourier.character u + 1 := by
      rw [phase_C_unit, phase_D_unit]
      ring
    _ = _ := by
      rw [character_pair,
        mul_comm (star (UnitaryErrorBases.ThreeCycleFourier.character s))
          (UnitaryErrorBases.ThreeCycleFourier.character u), character_pair]
      ring

/-- Distinct actual q3 matrices are complex trace-orthogonal. -/
theorem qThree_matrix_trace_zero (s u : PhaseIndex) (hsu : s ≠ u) :
    (qThreeUnitary s * (qThreeUnitary u).conjTranspose).trace = 0 := by
  rw [qThree_matrix_trace_formula]
  have hd : s-u ≠ 0 := sub_ne_zero.mpr hsu
  have hr : u-s = -(s-u) := by ring
  rw [hr]
  exact character_nonzero_sum (s-u) hd

private theorem qThree_phased_trace_zero (s u : PhaseIndex) (hsu : s ≠ u)
    (a b : PhaseIndex) :
    ((star (UnitaryErrorBases.ThreeCycleFourier.character a) • qThreeUnitary s) *
      (star (UnitaryErrorBases.ThreeCycleFourier.character b) • qThreeUnitary u).conjTranspose).trace = 0 := by
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, qThree_matrix_trace_zero s u hsu, smul_zero]

/-- All outcomes of two distinct actual q3 frames have native overlap1/3. -/
theorem qThree_family_pairing (s u : PhaseIndex) (hsu : s ≠ u) (a b : PhaseIndex) :
    coordinatePairing (upperCoordinates (nativeFamilyPoint 3 s a))
      (upperCoordinates (nativeFamilyPoint 3 u b)) = (1/3 : ℝ) := by
  rw [coordinatePairing_upperCoordinates_eq_native_trace,
    qThreeFamilyPoint_eq_matrix, qThreeFamilyPoint_eq_matrix,
    nativeComplementaryPoint_overlap, qThree_phased_trace_zero s u hsu a b]
  norm_num

private theorem phase_ne_of_lt (s u : Fin 3) (hsu : s < u) :
    (s.val : PhaseIndex) ≠ (u.val : PhaseIndex) := by
  fin_cases s <;> fin_cases u
  all_goals first | omega | decide

private theorem qThree_original_pairing (s u : Fin 3) (hsu : s < u) (a b : Fin 3) :
    coordinatePairing
      (upperCoordinates (nativePoint (framePointIndex (qThreeFrameLabel s) a)))
      (upperCoordinates (nativePoint (framePointIndex (qThreeFrameLabel u) b))) = (1/3 : ℝ) := by
  rw [congrFun (nativePoint_qThree_frame_eq_family s) a,
    congrFun (nativePoint_qThree_frame_eq_family u) b]
  exact qThree_family_pairing (s.val : PhaseIndex) (u.val : PhaseIndex)
    (phase_ne_of_lt s u hsu) (a.val : PhaseIndex) (b.val : PhaseIndex)

/-- All27 original valueRow equations between frames10,11,12, same1053variable point. -/
theorem qThree_cross_value_zero (s u : Fin 3) (hsu : s < u) (a b : Fin 3) :
    valueRow (1/2 : ℝ) (1/3 : ℝ) pointCoordinates
      (gNumber (gCross (qThreeFramePair s u hsu) a b)) = 0 := by
  simp only [valueRow, Equiv.symm_apply_apply, valueResidual, gCross, qThreeFramePair]
  rw [pointValues_pointCoordinates, pointValues_pointCoordinates]
  exact sub_eq_zero.mpr (qThree_original_pairing s u hsu a b)

/-- Exact original numbered G polynomials, with constant1/3 subtraction intact. -/
theorem qThree_cross_eval_zero (s u : Fin 3) (hsu : s < u) (a b : Fin 3) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross (qThreeFramePair s u hsu) a b))) = 0 := by
  rw [gRow_eval]
  exact qThree_cross_value_zero s u hsu a b

/-- The identical original evaluations reject changed value1 for every outcome. -/
theorem qThree_cross_changed_value_control (s u : Fin 3) (hsu : s < u) (a b : Fin 3) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross (qThreeFramePair s u hsu) a b))) ≠ 1 := by
  rw [qThree_cross_eval_zero]
  exact zero_ne_one

/-- First representative actual numbered equation, frames10/11, outcomes0/0. -/
theorem original_g3132_representative :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ) (3132 : Fin 3159)) = 0 := by
  rw [← qThree_first_row_number]
  exact qThree_cross_eval_zero 0 1 (by decide) 0 0

/-- Changed-value control for that exact same G3132 evaluation. -/
theorem original_g3132_changed_value_control :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ) (3132 : Fin 3159)) ≠ 1 := by
  rw [original_g3132_representative]
  exact zero_ne_one

end QuadraticCertificate.ExactCKMQThreeCross

#print axioms QuadraticCertificate.ExactCKMQThreeCross.njMatrix_trace_pair
#print axioms QuadraticCertificate.ExactCKMQThreeCross.qThree_matrix_trace_zero
#print axioms QuadraticCertificate.ExactCKMQThreeCross.qThree_cross_eval_zero
#print axioms QuadraticCertificate.ExactCKMQThreeCross.original_g3132_representative
#print axioms QuadraticCertificate.ExactCKMQThreeCross.original_g3132_changed_value_control

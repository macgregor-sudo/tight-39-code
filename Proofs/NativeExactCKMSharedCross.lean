module

public import NativeExactCKMSharedPhaseFrames
public import NativeExactCKMThreeHiddenFrames
public import LiteralComplexCharacterNorm
public import NativeCoordinateTracePairing

/-!
# The54 original cross equations among shared CKM frames0–3

Different phase frames reduce to the single scalar expression
1+character(delta)+character(epsilon-delta), where epsilon is their nonzero
frame difference and delta is the outcome difference. Its squared norm is3
by six scalar cases; normalized rank-one products therefore have trace1/3.
Coordinate/phase products use only the unit character norm. The actual native
trace dictionary and original point-coordinate packing retain all labels.

Only character_add is reused from the accepted q1 frame module; no hidden
cross equations are imported or proved. First-party composition and finite
scalar proofs; no third-party proof body copied. Existing native/mathlib
Apache-2.0 notices remain with their source owners: compact-albert-recognition
40d3b344180d9ddb78aaa2876873377c1e631515, mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55; Lean4.35.0-rc2.
Thanks to the original CKM construction, native-model and Lean/mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke,1676. No release license assigned.
-/

@[expose] public section
noncomputable section
namespace QuadraticCertificate.ExactCKMSharedCross
open CompactAlbert NativePolynomial
open NativePolynomial.ConfigurationResiduals
open NativePolynomial.ConfigurationResiduals.MixedCoefficients
open NativePolynomial.ConfigurationResiduals.Evaluation
open NativePolynomial.CoordinateMaps ConfigurationResidualIndices
open UnitaryErrorBases.ComplexQuartet UnitaryErrorBases.ThreeCycleFourier
open ExactCKMConfiguration ExactCKMSharedFrames
open scoped BigOperators

private theorem phase_cases (r : PhaseIndex) : r = 0 ∨ r = 1 ∨ r = 2 := by
  exact (by decide : ∀ r : PhaseIndex, r = 0 ∨ r = 1 ∨ r = 2) r

@[simp] private theorem phase_two_ne_zero : (2 : PhaseIndex) ≠ 0 := by decide
@[simp] private theorem phase_two_ne_one : (2 : PhaseIndex) ≠ 1 := by decide
private theorem phase_neg_one_ne_one : -(1 : PhaseIndex) ≠ 1 := by decide
private theorem phase_neg_two : -(2 : PhaseIndex) = 1 := by decide

private theorem phase_character_value (r : PhaseIndex) :
    character r = if r = 0 then 1 else if r = 1 then omega else -1 - omega := by
  rcases phase_cases r with rfl | rfl | rfl <;>
    norm_num [character, ZMod.val_one_eq_one_mod, ZMod.val_two_eq_two_mod, omega_sq]

private theorem character_unit (r : PhaseIndex) : character r * star (character r) = 1 := by
  simp only [Complex.star_def, Complex.mul_conj, character_normSq_eq_one, Complex.ofReal_one]

private theorem character_pair (a b : PhaseIndex) :
    star (character a) * character b = character (b-a) := by
  have ha : a + (b-a) = b := by ring
  have hadd := ExactCKMThreeHiddenFrames.character_add a (b-a)
  rw [ha] at hadd
  calc
    _ = star (character a) * (character a * character (b-a)) := by rw [← hadd]
    _ = (character a * star (character a)) * character (b-a) := by ring
    _ = _ := by rw [character_unit, one_mul]

set_option maxHeartbeats 2000000 in
/-- One six-case Gauss-sum norm identity, independent of absolute frame/outcome labels. -/
theorem character_gauss_norm (e d : PhaseIndex) (he : e ≠ 0) :
    Complex.normSq (1 + character d + character (e-d)) = 3 := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) := Real.mul_self_sqrt (by norm_num)
  rcases phase_cases e with rfl | rfl | rfl
  · exact False.elim (he rfl)
  all_goals
    rcases phase_cases d with rfl | rfl | rfl <;>
      norm_num [phase_character_value, omega, Complex.normSq_apply,
        Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im] <;>
      (try simp only [if_neg phase_neg_one_ne_one, if_pos phase_neg_two]) <;>
      norm_num [omega, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
        Complex.div_re, Complex.div_im] <;> nlinarith [hs]

/-- Actual cross-Gram entry depends only on the two label differences. -/
theorem phaseRay_cross_gram (s r t u : PhaseIndex) :
    dotProduct (star (phaseRay s t)) (phaseRay r u) =
      1 + character (u-t) + character ((r-s)-(u-t)) := by
  simp only [dotProduct, Fin.sum_univ_three, Pi.star_apply]
  change (star (1 : ℂ) * 1 + star (character t) * character u) +
    star (character (s-t)) * character (r-u) = _
  rw [star_one, one_mul, character_pair, character_pair]
  have h : (r-u)-(s-t) = (r-s)-(u-t) := by ring
  rw [h]

private theorem normalized_outer_trace (v w : Fin 3 → ℂ) :
    (((1/3 : ℂ) • Matrix.vecMulVec v (star v)) *
      ((1/3 : ℂ) • Matrix.vecMulVec w (star w))).trace =
      (1/9 : ℂ) * (Complex.normSq (dotProduct (star v) w) : ℂ) := by
  have hd : dotProduct v (star w) = star (dotProduct (star v) w) := by
    simp only [dotProduct, star_sum, star_mul, Pi.star_apply, star_star]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hn : (Complex.normSq (dotProduct (star v) w) : ℂ) =
      dotProduct (star v) w * star (dotProduct (star v) w) := by
    simpa only [starRingEnd_apply, mul_comm] using
      (Complex.normSq_eq_conj_mul_self (z := dotProduct (star v) w))
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_vecMulVec,
    dotProduct_smul, hd, hn]
  simp only [smul_eq_mul]
  ring

/-- All cross outcomes in distinct phase frames have the exact complex trace1/3. -/
theorem phaseProjector_cross_trace (s r : PhaseIndex) (hsr : s ≠ r) (t u : PhaseIndex) :
    (phaseProjector s t * phaseProjector r u).trace = (1/3 : ℂ) := by
  unfold phaseProjector
  rw [normalized_outer_trace, phaseRay_cross_gram,
    character_gauss_norm (r-s) (u-t) (sub_ne_zero.mpr (Ne.symm hsr))]
  norm_num

private theorem phaseProjector_diagonal (s t : PhaseIndex) (i : Fin 3) :
    phaseProjector s t i i = (1/3 : ℂ) := by
  rw [phaseProjector, Matrix.smul_apply, Matrix.vecMulVec_apply]
  simp only [smul_eq_mul, Pi.star_apply]
  have hu : phaseRay s t i * star (phaseRay s t i) = 1 := by
    fin_cases i
    · change (1 : ℂ) * star 1 = 1
      simp
    · exact character_unit t
    · exact character_unit (s-t)
  rw [hu, mul_one]

/-- Coordinate/phase overlap holds for every original outcome. -/
theorem coordinate_phase_trace (i : Fin 3) (s t : PhaseIndex) :
    (coordinateProjector i * phaseProjector s t).trace = (1/3 : ℂ) := by
  fin_cases i <;>
    norm_num [coordinateProjector, Matrix.trace_fin_three, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.diagonal_apply, phaseProjector_diagonal]

private theorem included_trace
    (P Q : {M : TitsComplexMatrix // M.IsHermitian}) :
    Glennie.trace (Glennie.jordan (includeHermitianMatrix P) (includeHermitianMatrix Q)) =
      (P.val * Q.val).trace.re := by
  rw [native_trace_jordan_includeHermitianMatrix]
  have hv := congrArg (fun p : TitsMatrixPair => p.1) (includeHermitianMatrix_pair P)
  change hermitianMatrix (toTitsCoordinates (includeHermitianMatrix P)) = P.val at hv
  rw [hv]

private theorem literal_coordinate_phase (i : Fin 3) (s t : PhaseIndex) :
    Glennie.trace (Glennie.jordan (literalNativeCoordinatePoint i)
      (literalNativePhasePoint s t)) = (1/3 : ℝ) := by
  rw [literalNativeCoordinatePoint_eq_included, literalNativePhasePoint_eq_included]
  change Glennie.trace (Glennie.jordan (includeHermitianMatrix _)
    (includeHermitianMatrix _)) = _
  rw [included_trace, coordinate_phase_trace]
  norm_num

private theorem literal_phase_phase (s r : PhaseIndex) (hsr : s ≠ r) (t u : PhaseIndex) :
    Glennie.trace (Glennie.jordan (literalNativePhasePoint s t)
      (literalNativePhasePoint r u)) = (1/3 : ℝ) := by
  rw [literalNativePhasePoint_eq_included, literalNativePhasePoint_eq_included]
  change Glennie.trace (Glennie.jordan (includeHermitianMatrix _)
    (includeHermitianMatrix _)) = _
  rw [included_trace, phaseProjector_cross_trace s r hsr t u]
  norm_num

private theorem original_coordinate_phase (s : Fin 3) (a b : Fin 3) :
    Glennie.trace (Glennie.jordan (nativePoint (framePointIndex 0 a))
      (nativePoint (framePointIndex (sharedPhaseFrameLabel s) b))) = (1/3 : ℝ) := by
  rw [congrFun nativePoint_coordinate_eq_literal a,
    congrFun (nativePoint_phase_eq_literal s) b]
  exact literal_coordinate_phase a (s.val : PhaseIndex) (b.val : PhaseIndex)

private theorem original_phase_phase (s r : Fin 3) (hsr : s < r) (a b : Fin 3) :
    Glennie.trace (Glennie.jordan
      (nativePoint (framePointIndex (sharedPhaseFrameLabel s) a))
      (nativePoint (framePointIndex (sharedPhaseFrameLabel r) b))) = (1/3 : ℝ) := by
  have hn : (s.val : PhaseIndex) ≠ (r.val : PhaseIndex) := by
    fin_cases s <;> fin_cases r
    all_goals first | omega | decide
  rw [congrFun (nativePoint_phase_eq_literal s) a,
    congrFun (nativePoint_phase_eq_literal r) b]
  exact literal_phase_phase _ _ hn _ _

/-- Uniform actual native shared overlap: six increasing frame pairs, nine outcomes each. -/
theorem shared_native_overlap (f g : Fin 4) (hfg : f < g) (a b : Fin 3) :
    Glennie.trace (Glennie.jordan
      (nativePoint (framePointIndex (sharedFrameLabel f) a))
      (nativePoint (framePointIndex (sharedFrameLabel g) b))) = (1/3 : ℝ) := by
  have hval : f.val < g.val := hfg
  fin_cases f <;> fin_cases g
  all_goals norm_num at hval
  all_goals first
    | exact original_coordinate_phase 0 a b
    | exact original_coordinate_phase 1 a b
    | exact original_coordinate_phase 2 a b
    | exact original_phase_phase 0 1 (by decide) a b
    | exact original_phase_phase 0 2 (by decide) a b
    | exact original_phase_phase 1 2 (by decide) a b

/-- Increasing original shared frame pair, unchanged by the cross-row binder. -/
def sharedFramePair (f g : Fin 4) (hfg : f < g) : Pair 13 :=
  ⟨(sharedFrameLabel f, sharedFrameLabel g), by
    change f.val < g.val
    exact hfg⟩

/-- The unchanged canonical cross-row integer, including strict original pair order. -/
theorem shared_cross_row_val (f g : Fin 4) (hfg : f < g) (a b : Fin 3) :
    (gNumber (gCross (sharedFramePair f g hfg) a b)).val =
      2457 + 9 * lexRank 13 (sharedFrameLabel f) (sharedFrameLabel g) +
        3 * a.val + b.val :=
  gNumber_cross_val (sharedFramePair f g hfg) a b

/-- All54 original value rows at the literal shared1053-variable CKM point. -/
theorem shared_cross_value_zero (f g : Fin 4) (hfg : f < g) (a b : Fin 3) :
    valueRow (1/2 : ℝ) (1/3 : ℝ) pointCoordinates
      (gNumber (gCross (sharedFramePair f g hfg) a b)) = 0 := by
  simp only [valueRow, Equiv.symm_apply_apply, valueResidual, gCross, sharedFramePair]
  rw [pointValues_pointCoordinates, pointValues_pointCoordinates,
    coordinatePairing_upperCoordinates_eq_native_trace, shared_native_overlap f g hfg a b]
  exact sub_self _

/-- The literal original numbered G polynomials, h=1/2,t=1/3 and all labels retained. -/
theorem shared_cross_eval_zero (f g : Fin 4) (hfg : f < g) (a b : Fin 3) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross (sharedFramePair f g hfg) a b))) = 0 := by
  rw [gRow_eval]
  exact shared_cross_value_zero f g hfg a b

/-- The identical evaluations reject changed value1, without an extra premise. -/
theorem shared_cross_changed_value_control (f g : Fin 4) (hfg : f < g) (a b : Fin 3) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross (sharedFramePair f g hfg) a b))) ≠ 1 := by
  rw [shared_cross_eval_zero]
  exact zero_ne_one

theorem shared_first_row_number :
    gNumber (gCross (sharedFramePair 0 1 (by decide)) 0 0) = (2457 : Fin 3159) := by
  apply Fin.ext
  rw [gNumber_cross_val]
  decide +kernel

/-- First representative actual numbered shared cross equation, same point and row. -/
theorem original_g2457_representative :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ) (2457 : Fin 3159)) = 0 := by
  rw [← shared_first_row_number]
  exact shared_cross_eval_zero 0 1 (by decide) 0 0

end QuadraticCertificate.ExactCKMSharedCross

#print axioms QuadraticCertificate.ExactCKMSharedCross.character_gauss_norm
#print axioms QuadraticCertificate.ExactCKMSharedCross.phaseProjector_cross_trace
#print axioms QuadraticCertificate.ExactCKMSharedCross.shared_native_overlap
#print axioms QuadraticCertificate.ExactCKMSharedCross.shared_cross_eval_zero
#print axioms QuadraticCertificate.ExactCKMSharedCross.shared_cross_changed_value_control
#print axioms QuadraticCertificate.ExactCKMSharedCross.original_g2457_representative

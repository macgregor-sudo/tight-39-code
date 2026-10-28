module

public import NativeExactCKMCDFrames
public import NativeCoordinateTracePairing

/-!
# All original shared-versus-hidden cross equations at the actual CKM point

Existing nativeComplementaryPoint_literal_readouts holds for every matrix,
so all twelve actual shared-anchor readouts of each hidden point are1/3.
The accepted q1/q2/q3 point binders and exact original label maps give all
36shared/hidden frame pairs and324original G equations. No phase sum,
unitary assumption, native point expansion or row-by-row computation is added.

This is first-party composition of accepted native/literal point owners and
the original polynomial evaluation API. Shared within-frame proofs and hidden
cross assembly are separate. Actual point bytes, gNumber/gCross, h=1/2,
t=1/3 and constant subtraction are unchanged. No full39solution claim.
Inherited native/mathlib Apache-2.0 pins: compact-albert-recognition at
40d3b344180d9ddb78aaa2876873377c1e631515; mathlib at
065356127b1dc0016f66b7283ce0ce2c4055aa55. No copied third-party proof.
Thanks to their contributors and the original CKM construction.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke,1676. No release license assigned.
-/

@[expose] public section
noncomputable section
namespace QuadraticCertificate.ExactCKMSharedHiddenCross
open NativePolynomial CompactAlbert
open NativePolynomial.ConfigurationResiduals
open NativePolynomial.ConfigurationResiduals.MixedCoefficients
open NativePolynomial.ConfigurationResiduals.Evaluation
open NativePolynomial.CoordinateMaps ConfigurationResidualIndices
open UnitaryErrorBases.ComplexQuartet
open ExactCKMConfiguration

/-- Literal original shared-frame inclusion0..3. -/
def sharedFrameLabel (f : Fin 4) : Fin 13 := ⟨f.val, by have hf := f.isLt; omega⟩

/-- Reuse actual accepted q1/q2/q3 original frame labels, without a new point. -/
def hiddenFrameLabel (q s : Fin 3) : Fin 13 :=
  ![ExactCKMThreeHiddenFrames.qOneFrameLabel s,
    ExactCKMABFrames.qTwoFrameLabel s, ExactCKMCDFrames.qThreeFrameLabel s] q

theorem hiddenFrameLabel_val (q s : Fin 3) :
    (hiddenFrameLabel q s).val = 4 + 3 * q.val + s.val := by
  fin_cases q <;> rfl

/-- Every original hidden frame occurs, retaining its original value. -/
theorem hiddenFrameLabel_covers (g : Fin 13) (hg : 4 ≤ g.val) :
    ∃ q s : Fin 3, hiddenFrameLabel q s = g := by
  let q : Fin 3 := ⟨(g.val - 4) / 3, by have hg13 := g.isLt; omega⟩
  let s : Fin 3 := ⟨(g.val - 4) % 3, Nat.mod_lt _ (by decide)⟩
  refine ⟨q, s, ?_⟩
  apply Fin.ext
  rw [hiddenFrameLabel_val]
  dsimp only [q, s]
  omega

/-- Increasing original frame pair, with shared frame left and hidden frame right. -/
def sharedHiddenFramePair (f : Fin 4) (q s : Fin 3) : Pair 13 :=
  ⟨(sharedFrameLabel f, hiddenFrameLabel q s), by
    change f.val < (hiddenFrameLabel q s).val
    rw [hiddenFrameLabel_val]
    have hf := f.isLt
    omega⟩

/-- Coordinate shared frame0 uses the existing literal native anchors. -/
theorem nativePoint_shared_coordinate (a : Fin 3) :
    nativePoint (framePointIndex (sharedFrameLabel 0) a) = literalNativeCoordinatePoint a := by
  fin_cases a <;> rfl

/-- Shared phase frames1+s retain exactly the existing raw(t,s-t) anchors. -/
theorem nativePoint_shared_phase (s a : Fin 3) :
    nativePoint (framePointIndex ⟨1+s.val, by omega⟩ a) =
      literalNativePhasePoint (s.val : PhaseIndex) (a.val : PhaseIndex) := by
  fin_cases s <;> fin_cases a <;> rfl

/-- Every actual hidden point is an existing native complementary point.
The matrix is supplied by accepted actual family binders, not assumed. -/
theorem nativePoint_hidden_eq_complementary (q s b : Fin 3) :
    ∃ U : TitsComplexMatrix,
      nativePoint (framePointIndex (hiddenFrameLabel q s) b) = nativeComplementaryPoint U := by
  have hq : q = 0 ∨ q = 1 ∨ q = 2 :=
    (by decide : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2) q
  rcases hq with rfl | rfl | rfl
  · refine ⟨star (UnitaryErrorBases.ThreeCycleFourier.character (b.val : PhaseIndex)) •
      ExactCKMThreeHiddenFrames.qOneUnitary (s.val : PhaseIndex), ?_⟩
    rw [show hiddenFrameLabel 0 s = ExactCKMThreeHiddenFrames.qOneFrameLabel s from rfl,
      congrFun (ExactCKMThreeHiddenFrames.nativePoint_qOne_frame_eq_family s) b,
      ExactCKMThreeHiddenFrames.qOneFamilyPoint_eq_matrix]
  · refine ⟨star (UnitaryErrorBases.ThreeCycleFourier.character (b.val : PhaseIndex)) •
      ExactCKMABFrames.qTwoUnitary (s.val : PhaseIndex), ?_⟩
    rw [show hiddenFrameLabel 1 s = ExactCKMABFrames.qTwoFrameLabel s from rfl,
      congrFun (ExactCKMABFrames.nativePoint_qTwo_frame_eq_family s) b,
      ExactCKMABFrames.qTwoFamilyPoint_eq_matrix]
  · refine ⟨star (UnitaryErrorBases.ThreeCycleFourier.character (b.val : PhaseIndex)) •
      ExactCKMCDFrames.qThreeUnitary (s.val : PhaseIndex), ?_⟩
    rw [show hiddenFrameLabel 2 s = ExactCKMCDFrames.qThreeFrameLabel s from rfl,
      congrFun (ExactCKMCDFrames.nativePoint_qThree_frame_eq_family s) b,
      ExactCKMCDFrames.qThreeFamilyPoint_eq_matrix]

/-- All12literal readouts of each actual hidden point, using the existing owner. -/
theorem nativePoint_hidden_literal_readouts (q s b : Fin 3) :
    (∀ a : Fin 3, Glennie.trace (Glennie.jordan
      (nativePoint (framePointIndex (hiddenFrameLabel q s) b))
      (literalNativeCoordinatePoint a)) = (1/3 : ℝ)) ∧
    (∀ a c : PhaseIndex, Glennie.trace (Glennie.jordan
      (nativePoint (framePointIndex (hiddenFrameLabel q s) b))
      (literalNativePhasePoint a c)) = (1/3 : ℝ)) := by
  rcases nativePoint_hidden_eq_complementary q s b with ⟨U, hU⟩
  simp only [hU]
  exact nativeComplementaryPoint_literal_readouts U

/-- Uniform actual shared/hidden coordinate pairing, in original left/right order. -/
theorem shared_hidden_pairing (f : Fin 4) (q s a b : Fin 3) :
    coordinatePairing
      (upperCoordinates (nativePoint (framePointIndex (sharedFrameLabel f) a)))
      (upperCoordinates (nativePoint (framePointIndex (hiddenFrameLabel q s) b))) = (1/3 : ℝ) := by
  rw [coordinatePairing_upperCoordinates_eq_native_trace]
  have h := nativePoint_hidden_literal_readouts q s b
  have hf : f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 :=
    (by decide : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) f
  rcases hf with rfl | rfl | rfl | rfl
  · rw [nativePoint_shared_coordinate, Glennie.jordan_comm]
    exact h.1 a
  · rw [show sharedFrameLabel 1 = (⟨1+(0 : Fin 3).val, by omega⟩ : Fin 13) from rfl,
      nativePoint_shared_phase 0 a, Glennie.jordan_comm]
    exact h.2 0 (a.val : PhaseIndex)
  · rw [show sharedFrameLabel 2 = (⟨1+(1 : Fin 3).val, by omega⟩ : Fin 13) from rfl,
      nativePoint_shared_phase 1 a, Glennie.jordan_comm]
    exact h.2 1 (a.val : PhaseIndex)
  · rw [show sharedFrameLabel 3 = (⟨1+(2 : Fin 3).val, by omega⟩ : Fin 13) from rfl,
      nativePoint_shared_phase 2 a, Glennie.jordan_comm]
    exact h.2 2 (a.val : PhaseIndex)

/-- All324original shared-versus-hidden valueRow equations at the same point. -/
theorem shared_hidden_cross_value_zero (f : Fin 4) (q s a b : Fin 3) :
    valueRow (1/2 : ℝ) (1/3 : ℝ) pointCoordinates
      (gNumber (gCross (sharedHiddenFramePair f q s) a b)) = 0 := by
  simp only [valueRow, Equiv.symm_apply_apply, valueResidual, gCross, sharedHiddenFramePair]
  rw [pointValues_pointCoordinates, pointValues_pointCoordinates]
  exact sub_eq_zero.mpr (shared_hidden_pairing f q s a b)

/-- Same original numbered G polynomials, including constant1/3 subtraction. -/
theorem shared_hidden_cross_eval_zero (f : Fin 4) (q s a b : Fin 3) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross (sharedHiddenFramePair f q s) a b))) = 0 := by
  rw [gRow_eval]
  exact shared_hidden_cross_value_zero f q s a b

/-- All admissible ORIGINAL strict pairs are covered without changing fg. -/
theorem original_shared_hidden_cross_eval_zero (fg : Pair 13)
    (hshared : fg.val.1.val < 4) (hhidden : 4 ≤ fg.val.2.val) (a b : Fin 3) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross fg a b))) = 0 := by
  rcases hiddenFrameLabel_covers fg.val.2 hhidden with ⟨q, s, hg⟩
  let f : Fin 4 := ⟨fg.val.1.val, hshared⟩
  have hf : sharedFrameLabel f = fg.val.1 := by apply Fin.ext; rfl
  have hfg : sharedHiddenFramePair f q s = fg := by
    apply Subtype.ext
    exact Prod.ext hf hg
  rw [← hfg]
  exact shared_hidden_cross_eval_zero f q s a b

/-- Same-expression changed-value control for every original shared/hidden row. -/
theorem original_shared_hidden_changed_value_control (fg : Pair 13)
    (hshared : fg.val.1.val < 4) (hhidden : 4 ≤ fg.val.2.val) (a b : Fin 3) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gCross fg a b))) ≠ 1 := by
  rw [original_shared_hidden_cross_eval_zero fg hshared hhidden a b]
  exact zero_ne_one

/-- Exact first original row, sharedframe0/hiddenframe4/outcomes0,0. -/
theorem shared_hidden_first_row_number :
    gNumber (gCross (sharedHiddenFramePair 0 0 0) 0 0) = (2484 : Fin 3159) := by
  apply Fin.ext
  rw [gNumber_cross_val]
  decide +kernel

theorem original_g2484_representative :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ) (2484 : Fin 3159)) = 0 := by
  rw [← shared_hidden_first_row_number]
  exact shared_hidden_cross_eval_zero 0 0 0 0 0

theorem original_g2484_changed_value_control :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ) (2484 : Fin 3159)) ≠ 1 := by
  rw [original_g2484_representative]
  exact zero_ne_one

end QuadraticCertificate.ExactCKMSharedHiddenCross

#print axioms QuadraticCertificate.ExactCKMSharedHiddenCross.hiddenFrameLabel_covers
#print axioms QuadraticCertificate.ExactCKMSharedHiddenCross.shared_hidden_pairing
#print axioms QuadraticCertificate.ExactCKMSharedHiddenCross.original_shared_hidden_cross_eval_zero
#print axioms QuadraticCertificate.ExactCKMSharedHiddenCross.original_g2484_representative
#print axioms QuadraticCertificate.ExactCKMSharedHiddenCross.original_g2484_changed_value_control

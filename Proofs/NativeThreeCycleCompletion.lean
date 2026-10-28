module

public import ThreeCycleNormalizedFamilyFibres
public import NativeChallengeUEBDictionary
public import NativeActualNineFrameDictionary

@[expose] public section

/-!
The actual normalized three-cycle construction gives native nine-frame arrays.
The accepted Challenge dictionary supplies the explicit ZMod3/Fin3 matrix
reindexing and clock-first Label→Fin9 convention val=3a+b, without transpose or
star. Its compound UEB transport preserves SU3 and full complex orthogonality.
Only the actual normalized constructed family's validity is proved here; no
native validity, seed equality, topology, quotient/global embedding, full A2 or
original2184F conclusion is assumed or asserted.
First-party composition of exact accepted owners and pinned matrix APIs.
Thanks to their contributors. “If I have seen further it is by standing on the
sholders of Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
namespace UnitaryErrorBases.ThreeCycleNormalized

private theorem su_mul (A B : Mat) (hA : IsSpecialUnitary A) (hB : IsSpecialUnitary B) :
    IsSpecialUnitary (A * B) := by
  constructor
  · rw [Matrix.conjTranspose_mul]
    calc
      (B.conjTranspose * A.conjTranspose) * (A * B) =
          B.conjTranspose * ((A.conjTranspose * A) * B) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA.1, Matrix.one_mul, hB.1]
  · rw [Matrix.det_mul, hA.2, hB.2, one_mul]

private theorem su_adjoint (A : Mat) (hA : IsSpecialUnitary A) :
    IsSpecialUnitary A.conjTranspose := by
  constructor
  · rw [Matrix.conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hA.1
  · rw [Matrix.det_conjTranspose, hA.2, star_one]

private theorem conjugate_cross_trace (Q A B : Mat) (hQ : IsSpecialUnitary Q) :
    ((Q * A * Q.conjTranspose).conjTranspose * (Q * B * Q.conjTranspose)).trace =
      (A.conjTranspose * B).trace := by
  calc
    _ = (Q * (A.conjTranspose * (Q.conjTranspose * Q) * B) * Q.conjTranspose).trace := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = (Q * (A.conjTranspose * B) * Q.conjTranspose).trace := by
      rw [hQ.1, Matrix.mul_one]
    _ = ((Q.conjTranspose * Q) * (A.conjTranspose * B)).trace := Matrix.trace_mul_cycle _ _ _
    _ = (A.conjTranspose * B).trace := by rw [hQ.1, Matrix.one_mul]

/-- The exact accepted normalizedFamily construction is a UEB under precisely
the original special-unitary Q and PhaseTriple d hypotheses. -/
theorem normalizedFamily_isUnitaryErrorBasis (Q : Mat) (d : PhaseTriple)
    (hQ : IsSpecialUnitary Q) : IsUnitaryErrorBasis (normalizedFamily Q d) := by
  constructor
  · intro p
    exact su_mul _ _ (su_mul Q _ hQ (ThreeCycleMatrix.monomialFamily_specialUnitary d p))
      (su_adjoint Q hQ)
  · intro p q hpq
    change ((Q * monomialFamily d p * Q.conjTranspose).conjTranspose *
      (Q * monomialFamily d q * Q.conjTranspose)).trace = 0
    rw [conjugate_cross_trace Q _ _ hQ]
    exact ThreeCycleMatrix.monomialFamily_pair_orthogonal d p q hpq

end UnitaryErrorBases.ThreeCycleNormalized

namespace CompactAlbert
open UnitaryErrorBases
open UnitaryErrorBases.ThreeCycleNormalized
open ActualNineFrameDictionary
open QuadraticCertificate.ExactCKMConfiguration

/-- Reuse the accepted inverse matrix/label reindexing; no new flattening. -/
def nativeThreeCycleArray (Q : Mat) (d : PhaseTriple) : Fin 9 → TitsComplexMatrix :=
  nativeArrayOfChallengeFamily (normalizedFamily Q d)

/-- Explicit formula: the Fin9 label is inverted by the accepted clock-first
bijection, and row/column indices are both sent Fin3→ZMod3 with no star/swap. -/
theorem nativeThreeCycleArray_apply (Q : Mat) (d : PhaseTriple) (r : Fin 9) (i j : Fin 3) :
    nativeThreeCycleArray Q d r i j =
      normalizedFamily Q d (challengeLabelEquiv.symm r)
        (challengeMatrixIndexEquiv i) (challengeMatrixIndexEquiv j) := rfl

/-- Zeroth actual label corresponds exactly to the original (clock,shift)=(0,0). -/
theorem nativeThreeCycleArray_zero (Q : Mat) (d : PhaseTriple) (hQ : IsSpecialUnitary Q) :
    nativeThreeCycleArray Q d 0 = (1 : TitsComplexMatrix) := by
  have hlabel : challengeLabelEquiv.symm (0 : Fin 9) = (0, 0) := rfl
  have hm : monomialFamily d (0, 0) = (1 : Mat) := by
    simp [monomialFamily, phaseMatrix, show (0 : Index) ≠ 2 by decide]
  have hn : normalizedFamily Q d (0, 0) = (1 : Mat) := by
    rw [normalizedFamily, hm, Matrix.mul_one]
    exact mul_eq_one_comm.mp hQ.1
  change challengeMatrixEquiv.symm (normalizedFamily Q d (challengeLabelEquiv.symm 0)) = _
  rw [hlabel, hn]
  rfl

/-- The accepted compound index transport gives all actual SU3 matrices and
full complex cross-traces, without a native-correspondence premise. -/
theorem nativeThreeCycleArray_conditions (Q : Mat) (d : PhaseTriple) (hQ : IsSpecialUnitary Q) :
    (∀ r : Fin 9, nativeThreeCycleArray Q d r * (nativeThreeCycleArray Q d r).conjTranspose = 1 ∧
      (nativeThreeCycleArray Q d r).det = 1) ∧
    (∀ r s : Fin 9, r ≠ s →
      ((nativeThreeCycleArray Q d r).conjTranspose * nativeThreeCycleArray Q d s).trace = 0) := by
  apply (challengeFamilyOfNativeArray_isUnitaryErrorBasis_iff (nativeThreeCycleArray Q d)).mp
  rw [nativeThreeCycleArray, challengeFamilyOfNativeArray_nativeArrayOfChallengeFamily]
  exact normalizedFamily_isUnitaryErrorBasis Q d hQ

/-- The actual reindexed normalized three-cycle family constructs nine native
central triples with every original first12readout and all labelled cross-readouts. -/
theorem nativeThreeCycleArray_actual_nine_frames (Q : Mat) (d : PhaseTriple) (hQ : IsSpecialUnitary Q) :
    ((∀ r : Fin 9, Glennie.Frame (nativeCentralTriple (nativeThreeCycleArray Q d r)) ∧
      ∀ k : Fin 3, ∀ i : Fin 39, i.val < 12 →
        Glennie.trace (Glennie.jordan (nativeCentralTriple (nativeThreeCycleArray Q d r) k)
          (nativePoint i)) = (1 / 3 : ℝ)) ∧
    (∀ r s : Fin 9, r ≠ s → ∀ k l : Fin 3,
      Glennie.trace (Glennie.jordan (nativeCentralTriple (nativeThreeCycleArray Q d r) k)
        (nativeCentralTriple (nativeThreeCycleArray Q d s) l)) = (1 / 3 : ℝ))) := by
  have hc := nativeThreeCycleArray_conditions Q d hQ
  apply (actual_nine_frames_iff_trace_orthogonal_array _).mpr
  exact ⟨nativeThreeCycleArray Q d, hc.1, fun r => Or.inl rfl, hc.2⟩

end CompactAlbert

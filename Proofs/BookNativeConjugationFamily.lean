module

public import BookFamilyDerivativeBridge
public import BookSheetRealStructure

@[expose] public section

/-! Simultaneous conjugation is the actual accepted A5 family derivative with X=Y. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.BookHT.TangentCoordinates
open CKM.NativeFirstOrder CKM.NativeFourFamily NativePolynomial CompactAlbert UnitaryErrorBases
open scoped Matrix

def nativeHiddenConjugation (X : Mat) (a : Glennie.Albert) : Glennie.Albert :=
  Elim.mkPoint 0 Matrix.isHermitian_zero
    (X * (show Mat from (nativeTitsMatrixPair a).2) -
      (show Mat from (nativeTitsMatrixPair a).2) * X)

theorem nativeHiddenConjugation_pair (X : Mat) (a : Glennie.Albert) :
    nativeTitsMatrixPair (nativeHiddenConjugation X a) =
      (0, X * (show Mat from (nativeTitsMatrixPair a).2) -
        (show Mat from (nativeTitsMatrixPair a).2) * X) :=
  Elim.mkPoint_pair _ _ _

theorem hidVar_same_conjugation (ξ : Fin 4 → ℂ) (H : Fin 4) (d : PhaseTriple)
    (k : Fin 8 → ℝ) (l : Label) :
    hidVar ξ H d (suMat k) (suMat k) 0 l =
      (show Mat from suMat k) * hidFamily ξ H 1 1 d l -
        hidFamily ξ H 1 1 d l * (show Mat from suMat k) := by
  let X : Mat := suMat k
  have hX : Xᴴ = -X := suMat_conjTranspose k
  have hdiag : Matrix.diagonal (0 : Index → ℂ) = (0 : Mat) := Matrix.diagonal_zero
  have hm : monomialVar (0 : Index → ℂ) l = 0 := by
    rw [monomialVar, hdiag, ite_self, Matrix.mul_zero, Matrix.zero_mul]
  change gaugeScalar H l •
    (X * gaugeLeft ξ H * monomialFamily d (gaugeLabel H l) * gaugeRight ξ H +
      gaugeLeft ξ H * monomialFamily d (gaugeLabel H l) * gaugeRight ξ H * Xᴴ +
      gaugeLeft ξ H * monomialVar 0 (gaugeLabel H l) * gaugeRight ξ H) =
      X * hidFamily ξ H 1 1 d l - hidFamily ξ H 1 1 d l * X
  have hm' : monomialVar (0 : Index → ℂ) (gaugeLabel H l) = 0 := by
    rw [monomialVar, hdiag, ite_self, Matrix.mul_zero, Matrix.zero_mul]
  rw [hX, hm']
  simp only [hidFamily, Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, sub_eq_add_neg,
    Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_neg, Matrix.mul_assoc]

theorem stdAnchoredVar_conjugation
    (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : Family) (X : Mat) (i : Fin 39) :
    stdAnchoredVar (fun l => X * W l - W l * X) i =
      if i.val < 12 then 0 else nativeHiddenConjugation X (stdAnchored q W i) := by
  by_cases hi : i.val < 12
  · simp only [stdAnchoredVar, hi, dite_true, ite_true]
  · simp only [stdAnchoredVar, hi, dite_false, ite_false, stdAnchored]
    apply nativeTitsMatrixPair_injective
    have hv (U : Mat) : nativeTitsMatrixPair (hiddenVec U) = (0, (1/3 : ℂ) • U) :=
      faman_hiddenVec_pair U
    have hp (U : Mat) : nativeTitsMatrixPair (nativeComplementaryPoint U) =
        ((1/3 : ℂ) • 1, (1/3 : ℂ) • U) := nativeComplementaryPoint_pair U
    rw [hv, nativeHiddenConjugation_pair, hp]
    congr 1
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]

theorem preVar_same_conjugation {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ)
    (H : Fin 4) (k : Fin 8 → ℝ) (i : Fin 39) :
    preVar ξ hξ H (k, k, 0) i =
      upperCoordinates (anchorΨinv H
        (if ((anchorRelabel H).symm i).val < 12 then 0 else
          nativeHiddenConjugation (suMat k) (anchorΨ H (literalPoint ξ i)))) := by
  have hz : torusVar (anchorTriple ξ hξ H) 0 = 0 := by
    funext j
    fin_cases j <;> simp [torusVar, torusAngles] <;> rfl
  unfold preVar
  simp only [hz]
  have he : hidVar ξ H (anchorTriple ξ hξ H) (suMat k) (suMat k) 0 =
      fun l => (show Mat from suMat k) * hidFamily ξ H 1 1 (anchorTriple ξ hξ H) l -
        hidFamily ξ H 1 1 (anchorTriple ξ hξ H) l * (show Mat from suMat k) := by
    funext l
    exact hidVar_same_conjugation ξ H _ k l
  rw [he, stdAnchoredVar_conjugation, ← anchor_form hξ H ((anchorRelabel H).symm i),
    Equiv.apply_symm_apply]

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.preVar_same_conjugation
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.preVar_same_conjugation


module

public import NativePhaseBookChange
public import NativeBookDictionaryChange

@[expose] public section

/-! The existing normalized native kernel in the exact Dictionary coordinates.
The common56 factor is fixed; the Book factor uses the proved signed-pair change.
All matrix inverses below come from the existing linear equivalences. -/

noncomputable section
namespace Option2.NativeStress.PhaseDictionaryKernelA6
open Matrix Module SliceLemmas
open PhasePivotA6 PhasePivotLocusA6 PhaseBookComplexificationA6
open PhaseBookChangeA6 PhaseBookDictionaryChangeA6
open CKM.NativeFourFamily BookHT
open scoped BigOperators

abbrev DictionaryCoordinateIndex := Fin 56 ⊕ Fin 24

/-- Identity on common56, and the literal signed Dictionary change on Book24. -/
def dictionaryCoordinatesChange :
    (CoordinateIndex → ℂ) ≃ₗ[ℂ] (DictionaryCoordinateIndex → ℂ) where
  toFun x := Sum.elim (fun i => x (.inl i))
    (dictionaryChange (fun p => x (.inr p)))
  invFun y := Sum.elim (fun i => y (.inl i))
    (dictionaryChange.symm (fun j => y (.inr j)))
  left_inv x := by
    funext k
    cases k with
    | inl i => rfl
    | inr p => exact congrFun (dictionaryChange.symm_apply_apply (fun p => x (.inr p))) p
  right_inv y := by
    funext k
    cases k with
    | inl i => rfl
    | inr j => exact congrFun (dictionaryChange.apply_symm_apply (fun j => y (.inr j))) j
  map_add' x y := by
    funext k
    cases k with
    | inl i => rfl
    | inr j => exact congrFun (dictionaryChange.map_add (fun p => x (.inr p))
        (fun p => y (.inr p))) j
  map_smul' c x := by
    funext k
    cases k with
    | inl i => rfl
    | inr j => exact congrFun (dictionaryChange.map_smul c (fun p => x (.inr p))) j

@[simp] theorem dictionaryCoordinatesChange_common (x : CoordinateIndex → ℂ) (i : Fin 56) :
    dictionaryCoordinatesChange x (.inl i) = x (.inl i) := rfl

@[simp] theorem dictionaryCoordinatesChange_inverse_common
    (y : DictionaryCoordinateIndex → ℂ) (i : Fin 56) :
    dictionaryCoordinatesChange.symm y (.inl i) = y (.inl i) := rfl

theorem dictionaryCoordinatesChange_independent (x : CoordinateIndex → ℂ)
    (i : Fin 4) (a : Fin 3) :
    dictionaryCoordinatesChange x (.inr (Dictionary.independentIndex i a)) =
      x (.inr ((i,a),0)) + Complex.I * x (.inr ((i,a),1)) :=
  dictionaryChange_independent (fun p => x (.inr p)) i a

theorem dictionaryCoordinatesChange_partner (x : CoordinateIndex → ℂ)
    (i : Fin 4) (a : Fin 3) :
    dictionaryCoordinatesChange x
        (.inr (Dictionary.coordinateBar (Dictionary.independentIndex i a))) =
      -x (.inr ((i,a),0)) + Complex.I * x (.inr ((i,a),1)) :=
  dictionaryChange_partner (fun p => x (.inr p)) i a

theorem dictionaryCoordinatesChange_realCoordinates (g : Fin 56 → ℂ) (z : BookHT.Blocks) :
    dictionaryCoordinatesChange
      (Sum.elim g (fun p => ((bookRealEquiv z p : ℝ) : ℂ))) =
      Sum.elim g (Dictionary.realCoordinates z) := by
  funext k
  cases k with
  | inl i => rfl
  | inr j => exact congrFun (dictionaryChange_realCoordinates z) j

def dictionaryCoordinatesMatrix : Matrix DictionaryCoordinateIndex CoordinateIndex ℂ :=
  LinearMap.toMatrix' dictionaryCoordinatesChange.toLinearMap

def dictionaryCoordinatesInverseMatrix : Matrix CoordinateIndex DictionaryCoordinateIndex ℂ :=
  LinearMap.toMatrix' dictionaryCoordinatesChange.symm.toLinearMap

theorem dictionaryCoordinatesMatrix_mul_inverse :
    dictionaryCoordinatesMatrix * dictionaryCoordinatesInverseMatrix = 1 := by
  rw [dictionaryCoordinatesMatrix, dictionaryCoordinatesInverseMatrix,
    ← LinearMap.toMatrix'_comp]
  have h : dictionaryCoordinatesChange.toLinearMap.comp
      dictionaryCoordinatesChange.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact dictionaryCoordinatesChange.apply_symm_apply x
  rw [h, LinearMap.toMatrix'_id]

theorem dictionaryCoordinatesInverseMatrix_mul :
    dictionaryCoordinatesInverseMatrix * dictionaryCoordinatesMatrix = 1 := by
  rw [dictionaryCoordinatesMatrix, dictionaryCoordinatesInverseMatrix,
    ← LinearMap.toMatrix'_comp]
  have h : dictionaryCoordinatesChange.symm.toLinearMap.comp
      dictionaryCoordinatesChange.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact dictionaryCoordinatesChange.symm_apply_apply x
  rw [h, LinearMap.toMatrix'_id]

/-- The actual native kernel equivalence, now with exact Fin56 ⊕ Fin24 labels. -/
def nativeDictionaryComplexEquiv {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    (DictionaryCoordinateIndex → ℂ) ≃ₗ[ℂ] LinearMap.ker (nativeJ ξ).mulVecLin :=
  dictionaryCoordinatesChange.symm.trans (nativeBookComplexEquiv hξ)

def nativeDictionaryComplexMatrix {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    Matrix (Fin 1053) DictionaryCoordinateIndex ℂ :=
  nativeComplexMatrix hξ * dictionaryCoordinatesInverseMatrix

theorem nativeDictionaryComplexEquiv_matrix {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (y : DictionaryCoordinateIndex → ℂ) :
    (nativeDictionaryComplexEquiv hξ y).val = nativeDictionaryComplexMatrix hξ *ᵥ y := by
  change (nativeBookComplexEquiv hξ (dictionaryCoordinatesChange.symm y)).val = _
  rw [nativeBookComplexEquiv_matrix, nativeDictionaryComplexMatrix,
    ← Matrix.mulVec_mulVec, dictionaryCoordinatesInverseMatrix, LinearMap.toMatrix'_mulVec]
  rfl

theorem nativeDictionaryComplexEquiv_changed {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (x : CoordinateIndex → ℂ) :
    nativeDictionaryComplexEquiv hξ (dictionaryCoordinatesChange x) =
      nativeBookComplexEquiv hξ x := by
  change nativeBookComplexEquiv hξ
    (dictionaryCoordinatesChange.symm (dictionaryCoordinatesChange x)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Compose the already proved M/N with the already proved Dictionary inverse.
The normalized native columns B and their literal pivots are unchanged. -/
theorem native_dictionary_change (u : NativePhaseTorus) (hgood : IsGoodPhase u.1)
    (hpivot : u ∈ nativePivotLocus) :
    ∃ (B : Matrix (Fin 1053) (Fin 80) ℂ) (piv : Fin 80 → Fin 1053)
      (M : Matrix (Fin 80) DictionaryCoordinateIndex ℂ)
      (N : Matrix DictionaryCoordinateIndex (Fin 80) ℂ),
      IsPivot B piv ∧
      (∀ r t, ∑ j, nativeJ u.1 r j * B j t = 0) ∧
      (∀ i j, M i j = nativeDictionaryComplexMatrix hgood (piv i) j) ∧
      B * M = nativeDictionaryComplexMatrix hgood ∧ M * N = 1 ∧ N * M = 1 := by
  classical
  obtain ⟨B,piv,M,N,hB,hJB,hM,hBM,hMN,hNM⟩ := native_book_change u hgood hpivot
  refine ⟨B,piv,M * dictionaryCoordinatesInverseMatrix,
    dictionaryCoordinatesMatrix * N,hB,hJB,?_,?_,?_,?_⟩
  · intro i j
    simp only [nativeDictionaryComplexMatrix, Matrix.mul_apply, hM]
  · rw [← Matrix.mul_assoc, hBM]
    rfl
  · calc
      (M * dictionaryCoordinatesInverseMatrix) * (dictionaryCoordinatesMatrix * N) =
          M * (dictionaryCoordinatesInverseMatrix * dictionaryCoordinatesMatrix) * N := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [dictionaryCoordinatesInverseMatrix_mul, Matrix.mul_one, hMN]
  · calc
      (dictionaryCoordinatesMatrix * N) * (M * dictionaryCoordinatesInverseMatrix) =
          dictionaryCoordinatesMatrix * (N * M) * dictionaryCoordinatesInverseMatrix := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hNM, Matrix.mul_one, dictionaryCoordinatesMatrix_mul_inverse]

#print axioms Option2.NativeStress.PhaseDictionaryKernelA6.nativeDictionaryComplexEquiv_matrix
#print axioms Option2.NativeStress.PhaseDictionaryKernelA6.native_dictionary_change
end Option2.NativeStress.PhaseDictionaryKernelA6

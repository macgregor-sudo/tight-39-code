module

public import BookRealCoordinates
public import BookQuadricDictionary

@[expose] public section

noncomputable section
namespace Option2.NativeStress.PhaseBookDictionaryChangeA6
open PhaseBookComplexificationA6 BookHT
open scoped BigOperators ComplexConjugate

/-- On each entry, (real,imaginary) ↦ (independent,negative-conjugate partner).
All four variables here are ordinary independent complex scalar coordinates. -/
def pairChange : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun x := ![x 0 + Complex.I*x 1,-x 0 + Complex.I*x 1]
  invFun y := ![(y 0-y 1)/2,(y 0+y 1)/(2*Complex.I)]
  left_inv x := by
    funext i
    fin_cases i
    · change ((x 0+Complex.I*x 1)-(-x 0+Complex.I*x 1))/2 = x 0
      ring
    · change ((x 0+Complex.I*x 1)+(-x 0+Complex.I*x 1))/(2*Complex.I) = x 1
      field_simp
      ring
  right_inv y := by
    funext i
    fin_cases i
    · change (y 0-y 1)/2 + Complex.I*((y 0+y 1)/(2*Complex.I)) = y 0
      field_simp
      ring
    · change -((y 0-y 1)/2) + Complex.I*((y 0+y 1)/(2*Complex.I)) = y 1
      field_simp
      ring
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp <;> ring

def entrywisePairChange : (BookRealIndex → ℂ) ≃ₗ[ℂ] (BookRealIndex → ℂ) where
  toFun x p := pairChange (fun b => x (p.1,b)) p.2
  invFun y p := pairChange.symm (fun b => y (p.1,b)) p.2
  left_inv x := by
    funext p
    change pairChange.symm (pairChange (fun b => x (p.1,b))) p.2 = x p
    rw [LinearEquiv.symm_apply_apply]
  right_inv y := by
    funext p
    change pairChange (pairChange.symm (fun b => y (p.1,b))) p.2 = y p
    rw [LinearEquiv.apply_symm_apply]
  map_add' x y := by
    funext p
    exact congrFun (pairChange.map_add (fun b => x (p.1,b)) (fun b => y (p.1,b))) p.2
  map_smul' c x := by
    funext p
    exact congrFun (pairChange.map_smul c (fun b => x (p.1,b))) p.2

/-- Literal Dictionary Fin24 labels: final bit0=independent,1=its paired partner. -/
def dictionaryLabel : Fin 24 → BookRealIndex :=
  ![((0,0),0),((0,1),0),((0,2),0),((0,0),1),((0,2),1),((0,1),1),
    ((1,0),0),((3,0),0),((2,0),0),((1,1),0),((3,1),0),((2,1),0),
    ((1,2),0),((3,2),0),((2,2),0),((1,0),1),((2,0),1),((3,0),1),
    ((1,2),1),((2,2),1),((3,2),1),((1,1),1),((2,1),1),((3,1),1)]

theorem dictionaryLabel_bijective : Function.Bijective dictionaryLabel := by decide +kernel

def dictionaryLabelEquiv : Fin 24 ≃ BookRealIndex := Equiv.ofBijective dictionaryLabel dictionaryLabel_bijective

/-- The explicit invertible complex coordinate change, not a dimension-only map. -/
def dictionaryChange : (BookRealIndex → ℂ) ≃ₗ[ℂ] (Fin 24 → ℂ) :=
  entrywisePairChange.trans (LinearEquiv.funCongrLeft ℂ ℂ dictionaryLabelEquiv)

theorem dictionaryChange_independent (x : BookRealIndex → ℂ) (i : Fin 4) (a : Fin 3) :
    dictionaryChange x (Dictionary.independentIndex i a) = x ((i,a),0)+Complex.I*x ((i,a),1) := by
  fin_cases i <;> fin_cases a <;> rfl

theorem dictionaryChange_partner (x : BookRealIndex → ℂ) (i : Fin 4) (a : Fin 3) :
    dictionaryChange x (Dictionary.coordinateBar (Dictionary.independentIndex i a)) =
      -x ((i,a),0)+Complex.I*x ((i,a),1) := by
  fin_cases i <;> fin_cases a <;> rfl

/-- Exact specialization to the SAME existing signed/conjugated Dictionary real form. -/
theorem dictionaryChange_realCoordinates (z : Blocks) :
    dictionaryChange (fun p => ((bookRealEquiv z p : ℝ) : ℂ)) = Dictionary.realCoordinates z := by
  funext j
  fin_cases j <;> apply Complex.ext <;>
    simp [dictionaryChange,entrywisePairChange,pairChange,dictionaryLabelEquiv,dictionaryLabel,
      Dictionary.realCoordinates,bookRealEquiv,Complex.mul_re,Complex.mul_im]

theorem dictionaryChange_inverse_re (y : Fin 24 → ℂ) (i : Fin 4) (a : Fin 3) :
    dictionaryChange.symm y ((i,a),0) =
      (y (Dictionary.independentIndex i a)-y (Dictionary.coordinateBar (Dictionary.independentIndex i a)))/2 := by
  have h0 := dictionaryChange_independent (dictionaryChange.symm y) i a
  have h1 := dictionaryChange_partner (dictionaryChange.symm y) i a
  rw [LinearEquiv.apply_symm_apply] at h0 h1
  rw [h0,h1]
  ring

theorem dictionaryChange_inverse_im (y : Fin 24 → ℂ) (i : Fin 4) (a : Fin 3) :
    dictionaryChange.symm y ((i,a),1) =
      (y (Dictionary.independentIndex i a)+y (Dictionary.coordinateBar (Dictionary.independentIndex i a)))/(2*Complex.I) := by
  have h0 := dictionaryChange_independent (dictionaryChange.symm y) i a
  have h1 := dictionaryChange_partner (dictionaryChange.symm y) i a
  rw [LinearEquiv.apply_symm_apply] at h0 h1
  rw [h0,h1]
  field_simp
  ring

#print axioms Option2.NativeStress.PhaseBookDictionaryChangeA6.dictionaryChange
#print axioms Option2.NativeStress.PhaseBookDictionaryChangeA6.dictionaryChange_realCoordinates
end Option2.NativeStress.PhaseBookDictionaryChangeA6

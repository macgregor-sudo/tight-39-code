module

public import BookHTQuartic
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

noncomputable section
namespace Option2.NativeStress.PhaseBookComplexificationA6
open BookHT WithLp

/-- Twelve actual complex Book entries, each split into its real0/imaginary1 parts. -/
abbrev BookRealIndex := (Fin 4 × Fin 3) × Fin 2
abbrev CoordinateIndex := Fin 56 ⊕ BookRealIndex

def bookRealEquiv : Blocks ≃ₗ[ℝ] (BookRealIndex → ℝ) where
  toFun z p := if p.2 = 0 then (z p.1.1 p.1.2).re else (z p.1.1 p.1.2).im
  invFun x i := toLp 2 (fun a => (⟨x ((i,a),0),x ((i,a),1)⟩ : ℂ))
  left_inv z := by
    funext i
    apply PiLp.ext
    intro a
    apply Complex.ext <;> rfl
  right_inv x := by
    funext p
    rcases p with ⟨⟨i,a⟩,b⟩
    fin_cases b <;> rfl
  map_add' z w := by
    funext p
    by_cases h : p.2 = 0 <;> simp [h]
  map_smul' c z := by
    funext p
    by_cases h : p.2 = 0 <;> simp [h,Complex.real_smul]

@[simp] theorem bookRealEquiv_re (z : Blocks) (i : Fin 4) (a : Fin 3) :
    bookRealEquiv z ((i,a),0) = (z i a).re := rfl
@[simp] theorem bookRealEquiv_im (z : Blocks) (i : Fin 4) (a : Fin 3) :
    bookRealEquiv z ((i,a),1) = (z i a).im := rfl
@[simp] theorem bookRealEquiv_symm_apply (x : BookRealIndex → ℝ) (i : Fin 4) (a : Fin 3) :
    bookRealEquiv.symm x i a = (⟨x ((i,a),0),x ((i,a),1)⟩ : ℂ) := rfl

theorem card_BookRealIndex : Fintype.card BookRealIndex = 24 := by decide +kernel
theorem card_CoordinateIndex : Fintype.card CoordinateIndex = 80 := by decide +kernel

/-- Common56 and Book24 coordinates stay distinguished at the type level. -/
def splitCoordinates (R : Type*) [Semiring R] :
    (CoordinateIndex → R) ≃ₗ[R] ((Fin 56 → R) × (BookRealIndex → R)) :=
  LinearEquiv.sumArrowLequivProdArrow _ _ R R

end Option2.NativeStress.PhaseBookComplexificationA6

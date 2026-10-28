module

public import A5Misc

@[expose] public section

/-!
# The twelve native resonance tests as one polynomial

`IsGoodPhase ξ` (A5) asks that `ξ` be a unit phase and that each of the twelve signed anchor phases
`anchorPhases ξ H j` (A3, `A3Interfaces`) have cube `≠ 1`. On unit phases every coordinate is
nonzero, so each test clears its denominators to the nonvanishing of one ordinary complex polynomial
`resonanceFactor H j` in the four phase variables `A, B, C, D = X 0, X 1, X 2, X 3`, and `IsGoodPhase`
becomes the nonvanishing of their product `resonancePoly`. The product is nonzero because it does not
vanish at the accepted nonresonant phase `xiNonres`.
-/

noncomputable section

open MvPolynomial CKM.NativeFirstOrder CKM.NativeFourFamily

namespace CKM.NativeGoodPhase

/-! ## Clearing one denominator (private algebra) -/

/-- Every coordinate of a unit phase is nonzero. -/
private lemma gpres_ne_zero {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (a : Fin 4) : ξ a ≠ 0 := by
  intro h0
  have := hξ a
  rw [h0, map_zero] at this
  exact zero_ne_one this

private lemma gpres_indexCases (j : UnitaryErrorBases.Index) : j = 0 ∨ j = 1 ∨ j = 2 :=
  (by decide : ∀ i : UnitaryErrorBases.Index, i = 0 ∨ i = 1 ∨ i = 2) j

private lemma gpres_self (a : ℂ) : a ^ 3 ≠ 1 ↔ a ^ 3 - 1 ≠ 0 := sub_ne_zero.symm

private lemma gpres_div {a b : ℂ} (hb : b ≠ 0) : (a / b) ^ 3 ≠ 1 ↔ a ^ 3 - b ^ 3 ≠ 0 := by
  rw [Ne, Ne, not_iff_not, div_pow, div_eq_one_iff_eq (pow_ne_zero 3 hb), sub_eq_zero]

private lemma gpres_inv (a : ℂ) : a⁻¹ ^ 3 ≠ 1 ↔ 1 - a ^ 3 ≠ 0 := by
  rw [Ne, Ne, not_iff_not, inv_pow, inv_eq_one, sub_eq_zero, eq_comm]

private lemma gpres_neg (a : ℂ) : (-a) ^ 3 ≠ 1 ↔ a ^ 3 + 1 ≠ 0 := by
  rw [Ne, Ne, not_iff_not, Odd.neg_pow (by decide), neg_eq_iff_eq_neg, eq_neg_iff_add_eq_zero]

private lemma gpres_neg_div {a b : ℂ} (hb : b ≠ 0) : (-(a / b)) ^ 3 ≠ 1 ↔ a ^ 3 + b ^ 3 ≠ 0 := by
  rw [Ne, Ne, not_iff_not, Odd.neg_pow (by decide), div_pow, neg_eq_iff_eq_neg,
    div_eq_iff (pow_ne_zero 3 hb)]
  constructor <;> intro h <;> linear_combination h

private lemma gpres_neg_inv (a : ℂ) : (-a⁻¹) ^ 3 ≠ 1 ↔ 1 + a ^ 3 ≠ 0 := by
  rw [Ne, Ne, not_iff_not, Odd.neg_pow (by decide), inv_pow, neg_eq_iff_eq_neg, inv_eq_iff_eq_inv,
    inv_neg, inv_one, eq_neg_iff_add_eq_zero, add_comm]

/-- The cleared form of the test `anchorPhases ξ H j ^ 3 ≠ 1`, factor by factor in the order of
`anchorPhases`. -/
def resonanceFactor : Fin 4 → UnitaryErrorBases.Index → MvPolynomial (Fin 4) ℂ
  | 0 => ![X 0 ^ 3 * X 1 ^ 3 - X 2 ^ 3, 1 - X 0 ^ 3 * X 3 ^ 3, X 2 ^ 3 * X 3 ^ 3 - X 1 ^ 3]
  | 1 => ![X 0 ^ 3 * X 2 ^ 3 * X 3 ^ 3 - 1, X 1 ^ 3 + X 2 ^ 3, 1 + X 0 ^ 3 * X 1 ^ 3 * X 3 ^ 3]
  | 2 => ![X 2 ^ 3 * X 3 ^ 3 + 1, 1 - X 2 ^ 3, 1 + X 3 ^ 3]
  | 3 => ![1 + X 0 ^ 3, 1 + X 1 ^ 3, X 0 ^ 3 * X 1 ^ 3 - 1]

/-- The product of the twelve cleared resonance tests. -/
def resonancePoly : MvPolynomial (Fin 4) ℂ := ∏ H : Fin 4, ∏ j : UnitaryErrorBases.Index, resonanceFactor H j

/-- On unit phases, each test is the nonvanishing of its factor. -/
theorem anchorPhases_cube_ne_one_iff {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4)
    (j : UnitaryErrorBases.Index) :
    anchorPhases ξ H j ^ 3 ≠ 1 ↔ eval ξ (resonanceFactor H j) ≠ 0 := by
  have hne := gpres_ne_zero hξ
  -- twelve cases, in the order (j outer, H inner); each clears one denominator
  rcases gpres_indexCases j with rfl | rfl | rfl <;> fin_cases H <;>
    simp only [anchorPhases, selectFour, resonanceFactor, Matrix.cons_val, map_sub, map_add, map_mul, map_pow,
      map_one, eval_X]
  · rw [gpres_div (hne 2), mul_pow]
  · rw [gpres_self, mul_pow, mul_pow]
  · rw [gpres_neg, mul_pow]
  · rw [gpres_neg_inv]
  · rw [gpres_inv, mul_pow]
  · rw [gpres_neg_div (hne 2)]
  · rw [gpres_inv]
  · rw [gpres_neg_inv]
  · rw [gpres_div (hne 1), mul_pow]
  · rw [gpres_neg_inv, mul_pow, mul_pow]
  · rw [gpres_neg_inv]
  · rw [gpres_self, mul_pow]

/-- **Resonance binding.** On unit phases, `IsGoodPhase` is the nonvanishing of `resonancePoly`. -/
theorem isGoodPhase_iff_eval_resonancePoly {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) :
    IsGoodPhase ξ ↔ eval ξ resonancePoly ≠ 0 := by
  -- `eval` of the double product is the double product of the evaluations
  simp only [IsGoodPhase, resonancePoly, map_prod, Finset.prod_ne_zero_iff, Finset.mem_univ,
    forall_const, ← anchorPhases_cube_ne_one_iff hξ]
  exact ⟨fun h => h.2, fun h => ⟨hξ, h⟩⟩

theorem resonancePoly_ne_zero : resonancePoly ≠ 0 := by
  -- it does not vanish at the accepted nonresonant phase
  intro h0
  have h := (isGoodPhase_iff_eval_resonancePoly isGoodPhase_xiNonres.1).1 isGoodPhase_xiNonres
  rw [h0, map_zero] at h
  exact h rfl

end CKM.NativeGoodPhase


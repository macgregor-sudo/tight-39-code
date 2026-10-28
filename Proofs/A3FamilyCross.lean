module

public import NativeExactCKMThreeHiddenFrames
public import NativeExactCKMABFrames
public import NativeExactCKMCDFrames

@[expose] public section

/-!
# Phase-generic helpers for the literal all-phase family

Everything here is proved symbolically, for arbitrary complex inputs (unit-norm hypotheses where
needed). No identity is imported from the rational seed phases.

* character arithmetic in `ZMod 3`: `star (χ a) = χ (-a)`, `1 + χ b + χ (-b) = 0` for `b ≠ 0`;
* the three monomial hidden patterns (`twoInputMatrix`, `ellNMatrix`, `njMatrix`): explicit
  `tr (U Vᴴ)` within a pattern, and `tr (U Vᴴ) = 0` across patterns (disjoint supports);
* the same-pattern cross sum vanishes at arbitrary unit multipliers `α, β` when the frame labels
  differ;
* the outcome-scaling identities `M(α χ_t, β χ_{s+t}) = star χ_t • M(α, β χ_s)`.
-/

noncomputable section

namespace CKM.NativeFirstOrder.FamilyCross

open UnitaryErrorBases.ComplexQuartet
open QuadraticCertificate.ExactCKMThreeHiddenFrames (twoInputMatrix character_add)
open QuadraticCertificate.ExactCKMABFrames (ellNMatrix)
open QuadraticCertificate.ExactCKMCDFrames (njMatrix)

local notation "χ" => UnitaryErrorBases.ThreeCycleFourier.character
local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega

/-! ## Unit complex numbers -/

theorem mul_star_of_normSq (z : ℂ) (hz : Complex.normSq z = 1) : z * star z = 1 := by
  simp only [Complex.star_def, Complex.mul_conj, hz, Complex.ofReal_one]

theorem normSq_unit_mul_character (z : ℂ) (hz : Complex.normSq z = 1) (t : PhaseIndex) :
    Complex.normSq (z * χ t) = 1 := by
  rw [Complex.normSq_mul, hz, CompactAlbert.character_normSq_eq_one, one_mul]

/-! ## Character arithmetic -/

theorem character_mul_star (t : PhaseIndex) : χ t * star (χ t) = 1 :=
  mul_star_of_normSq _ (CompactAlbert.character_normSq_eq_one t)

theorem character_zero : χ 0 = 1 := rfl

theorem character_one : χ 1 = ω := by
  rw [UnitaryErrorBases.ThreeCycleFourier.character, show (1 : PhaseIndex).val = 1 by decide,
    pow_one]

theorem character_two : χ 2 = ω ^ 2 := by
  rw [UnitaryErrorBases.ThreeCycleFourier.character, show (2 : PhaseIndex).val = 2 by decide]

theorem omega_mul_star : ω * star ω = 1 := by
  have h := character_mul_star 1
  rwa [character_one] at h

theorem star_omega : star ω = ω ^ 2 := by
  calc star ω = ω ^ 3 * star ω := by rw [UnitaryErrorBases.ThreeCycleFourier.omega_cube, one_mul]
    _ = ω ^ 2 * (ω * star ω) := by ring
    _ = ω ^ 2 := by rw [omega_mul_star, mul_one]

theorem star_omega_sq : star (ω ^ 2) = ω := by
  rw [star_pow, star_omega, ← pow_mul]
  calc ω ^ (2 * 2) = ω ^ 3 * ω := by ring
    _ = ω := by rw [UnitaryErrorBases.ThreeCycleFourier.omega_cube, one_mul]

theorem index_cases (a : PhaseIndex) : a = 0 ∨ a = 1 ∨ a = 2 := by
  revert a; decide

theorem star_character (a : PhaseIndex) : star (χ a) = χ (-a) := by
  rcases index_cases a with rfl | rfl | rfl
  · rw [neg_zero, character_zero, star_one]
  · rw [show -(1 : PhaseIndex) = 2 by decide, character_one, character_two, star_omega]
  · rw [show -(2 : PhaseIndex) = 1 by decide, character_one, character_two, star_omega_sq]

theorem character_mul_self (t : PhaseIndex) : χ t * χ t = star (χ t) := by
  rw [star_character, ← character_add]
  congr 1
  rcases index_cases t with rfl | rfl | rfl <;> decide

theorem one_add_character_add_character_neg (b : PhaseIndex) (hb : b ≠ 0) :
    1 + χ b + χ (-b) = 0 := by
  have hsq := UnitaryErrorBases.ThreeCycleFourier.omega_sq
  rcases index_cases b with rfl | rfl | rfl
  · exact absurd rfl hb
  · rw [show -(1 : PhaseIndex) = 2 by decide, character_one, character_two]
    linear_combination hsq
  · rw [show -(2 : PhaseIndex) = 1 by decide, character_one, character_two]
    linear_combination hsq

/-- The character sum of two distinct frame labels. -/
theorem character_pair_sum (s s' : PhaseIndex) (hs : s ≠ s') :
    χ s * star (χ s') + star (χ s) * χ s' + 1 = 0 := by
  rw [star_character, star_character, ← character_add, ← character_add]
  have hb : s - s' ≠ 0 := sub_ne_zero.mpr hs
  have h := one_add_character_add_character_neg (s - s') hb
  rw [show s + -s' = s - s' by ring, show -s + s' = -(s - s') by ring]
  linear_combination h

/-- Same-pattern hidden cross sum at arbitrary unit multipliers, distinct frame labels. -/
theorem pattern_sum_zero (α β : ℂ) (hα : α * star α = 1) (hβ : β * star β = 1)
    (s t s' t' : PhaseIndex) (hs : s ≠ s') :
    (α * χ t) * (β * χ (s + t)) * star ((α * χ t') * (β * χ (s' + t'))) +
      star (β * χ (s + t)) * (β * χ (s' + t')) + star (α * χ t) * (α * χ t') = 0 := by
  rw [character_add s t, character_add s' t']
  have hX2 := character_mul_self t
  have hX'2 : star (χ t') * star (χ t') = χ t' := by
    have h := congrArg star (character_mul_self t')
    simpa only [star_mul', star_star] using h
  have hYY := character_pair_sum s s' hs
  simp only [star_mul']
  linear_combination
    (β * star β * (χ t * χ t) * χ s * (star (χ t') * star (χ t')) * star (χ s')) * hα +
    ((χ t * χ t) * χ s * (star (χ t') * star (χ t')) * star (χ s')) * hβ +
    (χ s * (star (χ t') * star (χ t')) * star (χ s')) * hX2 +
    (star (χ t) * χ s * star (χ s')) * hX'2 +
    (star (χ s) * star (χ t) * χ s' * χ t') * hβ +
    (star (χ t) * χ t') * hα +
    (star (χ t) * χ t') * hYY

/-! ## Traces of the three monomial patterns -/

theorem trace_twoInput_twoInput (z w z' w' : ℂ) :
    (twoInputMatrix z w * (twoInputMatrix z' w').conjTranspose).trace =
      z * w * star (z' * w') + star w * w' + star z * z' := by
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.conjTranspose_apply]
  simp only [twoInputMatrix, Complex.star_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, star_zero, mul_zero, Matrix.cons_val_one,
    add_zero, Matrix.cons_val, star_mul', zero_add, star_neg, RingHomCompTriple.comp_apply,
    RingHom.id_apply, mul_neg, neg_mul, neg_neg]

theorem trace_ellN_ellN (z w z' w' : ℂ) :
    (ellNMatrix z w * (ellNMatrix z' w').conjTranspose).trace =
      z * w * star (z' * w') + star w * w' + star z * z' := by
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.conjTranspose_apply]
  simp only [ellNMatrix, Complex.star_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, star_mul', Matrix.cons_val_one, star_zero,
    mul_zero, add_zero, Matrix.cons_val, star_neg, RingHomCompTriple.comp_apply, RingHom.id_apply,
    mul_neg, neg_mul, neg_neg, zero_add]

theorem trace_nj_nj (z w z' w' : ℂ) :
    (njMatrix z w * (njMatrix z' w').conjTranspose).trace =
      z * w * star (z' * w') + star w * w' + star z * z' := by
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.conjTranspose_apply]
  simp only [njMatrix, Complex.star_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, star_zero, mul_zero, Matrix.cons_val_one,
    star_mul', zero_add, Matrix.cons_val, add_zero, star_neg, RingHomCompTriple.comp_apply,
    RingHom.id_apply, mul_neg, neg_mul, neg_neg]

theorem trace_twoInput_ellN (z w z' w' : ℂ) :
    (twoInputMatrix z w * (ellNMatrix z' w').conjTranspose).trace = 0 := by
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.conjTranspose_apply]
  simp only [twoInputMatrix, Complex.star_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, ellNMatrix, star_mul', zero_mul,
    Matrix.cons_val_one, star_zero, mul_zero, add_zero, Matrix.cons_val, star_neg,
    RingHomCompTriple.comp_apply, RingHom.id_apply, mul_neg, neg_zero]

theorem trace_twoInput_nj (z w z' w' : ℂ) :
    (twoInputMatrix z w * (njMatrix z' w').conjTranspose).trace = 0 := by
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.conjTranspose_apply]
  simp only [twoInputMatrix, Complex.star_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, njMatrix, star_zero, mul_zero,
    Matrix.cons_val_one, star_mul', zero_mul, add_zero, Matrix.cons_val, star_neg,
    RingHomCompTriple.comp_apply, RingHom.id_apply, mul_neg, neg_zero]

theorem trace_ellN_twoInput (z w z' w' : ℂ) :
    (ellNMatrix z w * (twoInputMatrix z' w').conjTranspose).trace = 0 := by
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.conjTranspose_apply]
  simp only [ellNMatrix, Complex.star_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, twoInputMatrix, star_zero, mul_zero,
    Matrix.cons_val_one, add_zero, Matrix.cons_val, star_mul', zero_mul, star_neg,
    RingHomCompTriple.comp_apply, RingHom.id_apply, mul_neg, neg_zero]

theorem trace_ellN_nj (z w z' w' : ℂ) :
    (ellNMatrix z w * (njMatrix z' w').conjTranspose).trace = 0 := by
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.conjTranspose_apply]
  simp only [ellNMatrix, Complex.star_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, njMatrix, star_zero, mul_zero,
    Matrix.cons_val_one, star_mul', zero_mul, add_zero, Matrix.cons_val, star_neg,
    RingHomCompTriple.comp_apply, RingHom.id_apply, mul_neg, neg_zero]

theorem trace_nj_twoInput (z w z' w' : ℂ) :
    (njMatrix z w * (twoInputMatrix z' w').conjTranspose).trace = 0 := by
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.conjTranspose_apply]
  simp only [njMatrix, Complex.star_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, twoInputMatrix, star_zero, mul_zero,
    Matrix.cons_val_one, add_zero, Matrix.cons_val, star_mul', zero_mul, star_neg,
    RingHomCompTriple.comp_apply, RingHom.id_apply, mul_neg, neg_zero]

theorem trace_nj_ellN (z w z' w' : ℂ) :
    (njMatrix z w * (ellNMatrix z' w').conjTranspose).trace = 0 := by
  simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.conjTranspose_apply]
  simp only [njMatrix, Complex.star_def, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, ellNMatrix, star_mul', zero_mul,
    Matrix.cons_val_one, star_zero, mul_zero, add_zero, Matrix.cons_val, star_neg,
    RingHomCompTriple.comp_apply, RingHom.id_apply, mul_neg, neg_zero]

/-! ## Outcome scaling within one hidden frame -/

/-- The scalar identities behind outcome scaling, for arbitrary multipliers. -/
theorem scaling_scalars (α β : ℂ) (s t : PhaseIndex) :
    (α * χ t) * (β * χ (s + t)) = star (χ t) * ((α * χ 0) * (β * χ (s + 0))) ∧
      -star (β * χ (s + t)) = star (χ t) * -star (β * χ (s + 0)) ∧
      star (α * χ t) = star (χ t) * star (α * χ 0) := by
  have hX2 := character_mul_self t
  rw [add_zero, character_zero, character_add s t]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (α * β * χ s) * hX2
  · simp only [star_mul']; ring
  · simp only [star_mul', star_one]; ring

theorem ellN_scaling (α β : ℂ) (s t : PhaseIndex) :
    ellNMatrix (α * χ t) (β * χ (s + t)) =
      star (χ t) • ellNMatrix (α * χ 0) (β * χ (s + 0)) := by
  obtain ⟨h1, -, h3⟩ := scaling_scalars α β s t
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ellNMatrix, Matrix.smul_apply, h1, h3]
  all_goals rw [character_add, map_mul]; ring

theorem nj_scaling (α β : ℂ) (s t : PhaseIndex) :
    njMatrix (α * χ t) (β * χ (s + t)) =
      star (χ t) • njMatrix (α * χ 0) (β * χ (s + 0)) := by
  obtain ⟨h1, -, h3⟩ := scaling_scalars α β s t
  ext i j
  fin_cases i <;> fin_cases j <;> simp [njMatrix, Matrix.smul_apply, h1, h3]
  all_goals rw [character_add, map_mul]; ring

end CKM.NativeFirstOrder.FamilyCross

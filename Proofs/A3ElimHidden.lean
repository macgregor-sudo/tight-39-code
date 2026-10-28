module

public import A3ElimAlg

@[expose] public section

/-!
# Elimination helpers II: hidden-point linearizations

At a native point with visible part `I/3` and hidden part `c W/3` (`W` special unitary, `c` a cube root
of unity), and a variation with zero visible part and hidden part `c V/3`, the tangent idempotency
equation is exactly the unit and determinant rows of `SatisfiesFirstOrder`. Also: within-frame rows
follow from idempotency rows and frame sums for any frame.
-/

noncomputable section

namespace CKM.NativeFirstOrder.Elim

open CompactAlbert

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega
local notation "πp" => CompactAlbert.nativeTitsMatrixPair

theorem jordan_zero_right' (x : Glennie.Albert) : Glennie.jordan x 0 = 0 := by
  simpa using Glennie.jordan_smul_right (0 : ℝ) x 0

/-- Within-frame rows follow from the idempotency rows and the two frame sums. -/
theorem within_of_idem (p δ : Fin 3 → Glennie.Albert) (hp : ∑ a, p a = 1) (hδ : ∑ a, δ a = 0)
    (hid : ∀ a, (2 : ℝ) • Glennie.jordan (p a) (δ a) = δ a) (a b : Fin 3) (hab : a ≠ b) :
    Glennie.jordan (p a) (δ b) + Glennie.jordan (δ a) (p b) = 0 := by
  rw [Fin.sum_univ_three] at hp hδ
  have row : ∀ a, Glennie.jordan (p a) (δ 0) + Glennie.jordan (p a) (δ 1) +
      Glennie.jordan (p a) (δ 2) = 0 := fun a => by
    rw [← Glennie.jordan_add_right, ← Glennie.jordan_add_right, hδ, jordan_zero_right']
  have col : ∀ b, Glennie.jordan (p 0) (δ b) + Glennie.jordan (p 1) (δ b) +
      Glennie.jordan (p 2) (δ b) = δ b := fun b => by
    rw [← Glennie.jordan_add_left, ← Glennie.jordan_add_left, hp, Glennie.jordan_unit_left]
  have r0 := row 0; have r1 := row 1; have r2 := row 2
  have c0 := col 0; have c1 := col 1; have c2 := col 2
  have d0 := hid 0; have d1 := hid 1; have d2 := hid 2
  rw [Glennie.jordan_comm (δ a) (p b)]
  have E0 : Glennie.jordan (p 0) (δ 1) + Glennie.jordan (p 1) (δ 0) +
      (Glennie.jordan (p 0) (δ 2) + Glennie.jordan (p 2) (δ 0)) = 0 := by
    linear_combination (norm := module) r0 + c0 - d0
  have E1 : Glennie.jordan (p 0) (δ 1) + Glennie.jordan (p 1) (δ 0) +
      (Glennie.jordan (p 1) (δ 2) + Glennie.jordan (p 2) (δ 1)) = 0 := by
    linear_combination (norm := module) r1 + c1 - d1
  have E2 : Glennie.jordan (p 0) (δ 2) + Glennie.jordan (p 2) (δ 0) +
      (Glennie.jordan (p 1) (δ 2) + Glennie.jordan (p 2) (δ 1)) = 0 := by
    linear_combination (norm := module) r2 + c2 - d2
  fin_cases a <;> fin_cases b <;> simp at hab ⊢
  · linear_combination (norm := module) (1 / 2 : ℝ) • (E0 + E1 - E2)
  · linear_combination (norm := module) (1 / 2 : ℝ) • (E0 - E1 + E2)
  · linear_combination (norm := module) (1 / 2 : ℝ) • (E0 + E1 - E2)
  · linear_combination (norm := module) (1 / 2 : ℝ) • (E1 + E2 - E0)
  · linear_combination (norm := module) (1 / 2 : ℝ) • (E0 - E1 + E2)
  · linear_combination (norm := module) (1 / 2 : ℝ) • (E1 + E2 - E0)

theorem two_smul_half (Y : TitsComplexMatrix) : (2 : ℝ) • ((1 / 2 : ℂ) • Y) = Y := by
  ext i j
  simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  push_cast; ring

theorem star_eq_sq_of_cube {c : ℂ} (hc : c * star c = 1) (hc3 : c ^ 3 = 1) : star c = c ^ 2 := by
  calc star c = c ^ 3 * star c := by rw [hc3, one_mul]
    _ = c ^ 2 * (c * star c) := by ring
    _ = c ^ 2 := by rw [hc, mul_one]

theorem smul_specialUnitary_eq_zero {W : TitsComplexMatrix} (hW : W.conjTranspose * W = 1) {z : ℂ}
    (h : z • W = 0) : z = 0 := by
  have h1 := congrArg (fun M => W.conjTranspose * M) h
  simp only [Matrix.mul_smul, hW, Matrix.mul_zero] at h1
  have h2 := congrArg (fun M : TitsComplexMatrix => M 0 0) h1
  simpa using h2

/-- The visible part of the hidden-point idempotency row. -/
theorem visible_iff (X : TitsComplexMatrix) :
    (2 : ℝ) • ((1 / 2 : ℂ) • (-((1 / 9 : ℂ) • X) - (1 / 9 : ℂ) • X.conjTranspose) +
        ((((1 / 9 : ℂ) • X).trace.re : ℝ) : ℂ) • (1 : TitsComplexMatrix)) = 0 ↔
      X + X.conjTranspose = 0 := by
  have htr : (X.conjTranspose).trace = star X.trace := Matrix.trace_conjTranspose X
  constructor
  · intro h
    have h' := congrArg (fun M : TitsComplexMatrix => (Matrix.trace M).re) h
    simp only [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_neg,
      Matrix.trace_one, htr, smul_eq_mul, Complex.real_smul, Matrix.trace_zero] at h'
    simp [Complex.mul_re, Complex.mul_im] at h'
    have hre : X.trace.re = 0 := by linarith
    have hre' : (((1 / 9 : ℂ) • X).trace.re : ℝ) = 0 := by
      simp [Matrix.trace_smul, hre]
    rw [hre', Complex.ofReal_zero, zero_smul, add_zero, two_smul_half] at h
    have h2 : (-(1 / 9 : ℂ)) • (X + X.conjTranspose) = 0 := by
      rw [← h]; module
    rcases smul_eq_zero.mp h2 with h3 | h3
    · norm_num at h3
    · exact h3
  · intro h
    have hre : X.trace.re = 0 := by
      have h' := congrArg (fun M : TitsComplexMatrix => (Matrix.trace M).re) h
      simp only [Matrix.trace_add, htr, Matrix.trace_zero] at h'
      simp at h'
      linarith
    have hre' : (((1 / 9 : ℂ) • X).trace.re : ℝ) = 0 := by
      simp [Matrix.trace_smul, hre]
    rw [hre', Complex.ofReal_zero, zero_smul, add_zero, two_smul_half]
    have h2 : X.conjTranspose = -X := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm, h]
    rw [h2]; module

/-- Tangent idempotency at a hidden point `(I/3, cW/3)` for a variation `(0, cV/3)`. -/
theorem hidden_idem_iff {W V : TitsComplexMatrix} (hW : W.conjTranspose * W = 1) (hd : W.det = 1)
    {c : ℂ} (hc : c * star c = 1) (hc3 : c ^ 3 = 1) {x u : Glennie.Albert}
    (hx : πp x = ((1 / 3 : ℂ) • (1 : TitsComplexMatrix), (1 / 3 : ℂ) • (c • W)))
    (hu : πp u = (0, (1 / 3 : ℂ) • (c • V))) :
    (2 : ℝ) • Glennie.jordan x u = u ↔
      (W.conjTranspose * V + V.conjTranspose * W = 0 ∧ (W.conjTranspose * V).trace = 0) := by
  have hWW := mul_conjTranspose_of_specialUnitary hW
  have hsc := star_eq_sq_of_cube hc hc3
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have hstar3 : star (1 / 3 : ℂ) = 1 / 3 := by
    apply Complex.ext <;> simp
  have hBD : ((1 / 3 : ℂ) • (c • W)) * ((1 / 3 : ℂ) • (c • V)).conjTranspose =
      (1 / 9 : ℂ) • (W * V.conjTranspose) := by
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_mul,
      hstar3]
    congr 1
    linear_combination (1 / 9 : ℂ) * hc
  have hDB : ((1 / 3 : ℂ) • (c • V)) * ((1 / 3 : ℂ) • (c • W)).conjTranspose =
      (1 / 9 : ℂ) • (W * V.conjTranspose).conjTranspose := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_mul,
      hstar3]
    congr 1
    linear_combination (1 / 9 : ℂ) * hc
  have hpol : ((1 / 3 : ℂ) • (c • W) + (1 / 3 : ℂ) • (c • V)).adjugate.conjTranspose -
      ((1 / 3 : ℂ) • (c • W)).adjugate.conjTranspose -
      ((1 / 3 : ℂ) • (c • V)).adjugate.conjTranspose =
      (c / 9) • (star (W.conjTranspose * V).trace • W - W * V.conjTranspose * W) := by
    rw [smul_smul, smul_smul, polar_specialUnitary hW hd]
    congr 1
    rw [star_mul, star_mul, hstar3, hsc]
    linear_combination (1 / 9 : ℂ) * c * hc3
  rw [← pair_inj, map_smul, jordan_pair_third_hidden x u hx hu, hu, hBD, hDB, hpol,
    Prod.smul_mk, Prod.mk.injEq, visible_iff, two_smul_half]
  -- hidden component
  have hhid : (2 / 3 : ℂ) • ((1 / 3 : ℂ) • (c • V)) +
        (c / 9) • (star (W.conjTranspose * V).trace • W - W * V.conjTranspose * W) =
        (1 / 3 : ℂ) • (c • V) ↔
      star (W.conjTranspose * V).trace • W - W * V.conjTranspose * W = V := by
    constructor
    · intro h
      have h2 : (c / 9) • (star (W.conjTranspose * V).trace • W - W * V.conjTranspose * W) =
          (c / 9) • V := by
        rw [← sub_eq_zero, ← sub_eq_zero.mpr h]; module
      exact smul_right_injective _ (div_ne_zero hc0 (by norm_num)) h2
    · intro h
      rw [h]; module
  rw [hhid]
  constructor
  · rintro ⟨hv, hq⟩
    have hv' : W * V.conjTranspose = -(V * W.conjTranspose) := by
      rw [eq_neg_iff_add_eq_zero]
      simpa [Matrix.conjTranspose_mul] using hv
    have ha : W.conjTranspose * V + V.conjTranspose * W = 0 := by
      have h1 := congrArg (fun M => W.conjTranspose * M * W) hv
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_zero, Matrix.zero_mul] at h1
      simp only [← Matrix.mul_assoc, hW, Matrix.one_mul] at h1
      simp only [Matrix.mul_assoc, hW, Matrix.mul_one] at h1
      rw [add_comm]; exact h1
    refine ⟨ha, ?_⟩
    have hWVW : W * V.conjTranspose * W = -V := by
      rw [hv', Matrix.neg_mul, Matrix.mul_assoc, hW, Matrix.mul_one]
    rw [hWVW, sub_neg_eq_add, add_eq_right] at hq
    have := smul_specialUnitary_eq_zero hW hq
    simpa using this
  · rintro ⟨ha, ht⟩
    have hv : W * V.conjTranspose + (W * V.conjTranspose).conjTranspose = 0 := by
      have h1 := congrArg (fun M => W * M * W.conjTranspose) ha
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_zero, Matrix.zero_mul] at h1
      simp only [← Matrix.mul_assoc, hWW, Matrix.one_mul] at h1
      simp only [Matrix.mul_assoc, hWW, Matrix.mul_one] at h1
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, add_comm]; exact h1
    refine ⟨hv, ?_⟩
    have hv' : W * V.conjTranspose = -(V * W.conjTranspose) := by
      rw [eq_neg_iff_add_eq_zero]
      simpa [Matrix.conjTranspose_mul] using hv
    rw [ht, star_zero, zero_smul, zero_sub, hv', Matrix.neg_mul, neg_neg, Matrix.mul_assoc, hW,
      Matrix.mul_one]

end CKM.NativeFirstOrder.Elim

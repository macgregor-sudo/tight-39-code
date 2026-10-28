module

public import A3Anchor3Points
public import ThreeCycleMatrixSupport
public import ThreeCycleUnitaryErrorBasis

@[expose] public section

/-!
# Anchor H3: the hidden family is a gauge image of the monomial normal form

`W3 ξ l = c l • (G_L * monomialFamily (anchorTriple ξ hξ 3) (σ l) * 1)` with
`G_L = −[[0,1,0],[1,0,0],[0,0,1]]`, `σ (l₁, l₂) = (if l₁ = 2 then −l₂ else l₂, l₁)`,
`c (0, s) = χ s`, `c (1, s) = χ (−s)`, `c (2, s) = 1`, at every unit phase.
-/

noncomputable section

namespace CKM.NativeFirstOrder

namespace Anchor3

open UnitaryErrorBases

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega
local notation "χ" => UnitaryErrorBases.ThreeCycleFourier.character

/-- Left gauge factor `G_L = −[[0,1,0],[1,0,0],[0,0,1]]`. -/
def gaugeL3 : Mat := Matrix.of fun i j =>
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 2) then -1 else 0

/-- Scalar gauge factors. -/
def gaugeC3 (l : Label) : ℂ := if l.1 = 0 then χ l.2 else if l.1 = 1 then χ (-l.2) else 1

/-- Label map to the monomial labels (clock index first). -/
def gaugeσ3 : Label ≃ Label where
  toFun l := (if l.1 = 2 then -l.2 else l.2, l.1)
  invFun m := (m.2, if m.2 = 2 then -m.1 else m.1)
  left_inv := by intro l; revert l; decide
  right_inv := by intro m; revert m; decide

theorem sum_three (f : Index → ℂ) : ∑ i, f i = f 0 + f 1 + f 2 := Fin.sum_univ_three f

theorem monomialFamily_apply (d : PhaseTriple) (a b i j : Index) :
    monomialFamily d (a, b) i j =
      (if i = j + b then ThreeCycleFourier.phaseEntry d.val b j else 0) *
        (UnitaryErrorBases.omega ^ j.val) ^ a.val := by
  rw [ThreeCycleMatrix.monomialFamily_eq, ThreeCycleMatrix.rightFactor, clock,
    Matrix.diagonal_pow, Matrix.mul_diagonal, ThreeCycleMatrix.leftFactor_apply]
  rfl

theorem gaugeL3_mul_apply (Y : Mat) (i j : Index) :
    (gaugeL3 * Y) i j = -Y (if i = 0 then 1 else if i = 1 then 0 else 2) j := by
  rcases idx_cases i with rfl | rfl | rfl <;>
    simp +decide [Matrix.mul_apply, gaugeL3, sum_three]

theorem gauge3_rhs_apply (d : PhaseTriple) (l : Label) (i j : Index) :
    (gaugeC3 l • (gaugeL3 * monomialFamily d (gaugeσ3 l) * 1)) i j =
      gaugeC3 l * -((if (if i = 0 then 1 else if i = 1 then 0 else 2) = j + l.1 then
          ThreeCycleFourier.phaseEntry d.val l.1 j else 0) *
        (UnitaryErrorBases.omega ^ j.val) ^ (if l.1 = 2 then -l.2 else l.2).val) := by
  rw [Matrix.mul_one, Matrix.smul_apply, gaugeL3_mul_apply, smul_eq_mul]
  change _ * -(monomialFamily d (if l.1 = 2 then -l.2 else l.2, l.1) _ j) = _
  rw [monomialFamily_apply]

theorem omega_eq : UnitaryErrorBases.omega = ω := rfl

theorem W3_apply (ξ : Fin 4 → ℂ) (g s i j : Index) :
    W3 ξ (g, s) i j =
      if g = 0 then
        (if i = 0 ∧ j = 1 then -star (χ s) else if i = 1 ∧ j = 0 then -χ s
          else if i = 2 ∧ j = 2 then -1 else 0)
      else if g = 1 then
        (if i = 0 ∧ j = 0 then -star (χ s) else if i = 1 ∧ j = 2 then -χ s
          else if i = 2 ∧ j = 1 then -1 else 0)
      else
        (if i = 0 ∧ j = 2 then -(ξ 0 * ξ 1 * χ s) else if i = 1 ∧ j = 1 then star (ξ 1 * χ s)
          else if i = 2 ∧ j = 0 then star (ξ 0) else 0) := by
  rcases idx_cases g with rfl | rfl | rfl <;> rcases idx_cases i with rfl | rfl | rfl <;>
    rcases idx_cases j with rfl | rfl | rfl <;> rfl

/-- The hidden representatives of anchor H3 are a gauge image of the monomial normal form. -/
theorem W3_gauge (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (l : Label) :
    W3 ξ l = gaugeC3 l • (gaugeL3 * monomialFamily (anchorTriple ξ hξ 3) (gaugeσ3 l) * 1) := by
  have hneg2 : -(2 : Index) = 1 := rfl
  have h0 := ne_zero_of_unit _ (hξ 0)
  have h1 := ne_zero_of_unit _ (hξ 1)
  have hs0 := star_eq_inv_of_unit _ (hξ 0)
  have hs1 := star_eq_inv_of_unit _ (hξ 1)
  obtain ⟨g, s⟩ := l
  ext i j
  rw [gauge3_rhs_apply, W3_apply]
  rcases idx_cases g with rfl | rfl | rfl <;> rcases idx_cases s with rfl | rfl | rfl <;>
    rcases idx_cases i with rfl | rfl | rfl <;> rcases idx_cases j with rfl | rfl | rfl <;>
    simp +decide [gaugeC3, ThreeCycleFourier.phaseEntry, anchorTriple, anchorPhases, chi_val,
      star_mul', hs0, hs1, omega_eq, star_omega, val_one3, val_two3, hneg2] <;>
    (try field_simp) <;> (try ring_nf) <;>
    (try simp only [omega_cube, omega_pow_four, omega_pow_five, omega_pow_six]) <;>
    (try simp)

/-! ## Unitarity of the gauge data and the unitary-error-basis property -/

theorem gaugeL3_unitary : gaugeL3.conjTranspose * gaugeL3 = 1 := by
  ext i j
  rcases idx_cases i with rfl | rfl | rfl <;> rcases idx_cases j with rfl | rfl | rfl <;>
    simp +decide [Matrix.mul_apply, Matrix.conjTranspose_apply, gaugeL3, sum_three]

theorem one_unitary3 : (1 : Mat) * (1 : Mat).conjTranspose = 1 := by
  rw [Matrix.conjTranspose_one, Matrix.mul_one]

theorem normSq_chi3 (r : Index) : Complex.normSq (χ r) = 1 := by
  show Complex.normSq (ω ^ r.val) = 1
  rw [map_pow, normSq_omega, one_pow]

theorem gaugeC3_normSq (l : Label) : Complex.normSq (gaugeC3 l) = 1 := by
  unfold gaugeC3
  split_ifs
  · exact normSq_chi3 _
  · exact normSq_chi3 _
  · exact map_one _

/-- A gauge image of a unitary error basis with determinant-one members is a unitary error basis. -/
theorem isUnitaryErrorBasis_of_gauge3 (U U' : Family) (hU : IsUnitaryErrorBasis U) (L R : Mat)
    (hL : L.conjTranspose * L = 1) (hR : R * R.conjTranspose = 1) (c : Label → ℂ)
    (hc : ∀ p, Complex.normSq (c p) = 1) (σ : Label ≃ Label)
    (h : ∀ p, U' p = c p • (L * U (σ p) * R)) (hdet : ∀ p, (U' p).det = 1) :
    IsUnitaryErrorBasis U' := by
  have hR' : R.conjTranspose * R = 1 := mul_eq_one_comm.mp hR
  refine ⟨fun p => ⟨?_, hdet p⟩, fun p q hpq => ?_⟩
  · rw [h p, gauge_pair L R _ _ hL, star_mul_self_of_normSq _ (hc p), one_smul, (hU.1 (σ p)).1,
      Matrix.mul_one, hR']
  · rw [h p, h q, gauge_pair L R _ _ hL, Matrix.trace_smul, trace_conj_unitary R _ hR,
      hU.2 (σ p) (σ q) (σ.injective.ne hpq), smul_zero]

theorem W3_det (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (l : Label) : (W3 ξ l).det = 1 := by
  have h0 := ne_zero_of_unit _ (hξ 0)
  have h1 := ne_zero_of_unit _ (hξ 1)
  have hs0 : (starRingEnd ℂ) (ξ 0) = (ξ 0)⁻¹ := star_eq_inv_of_unit _ (hξ 0)
  have hs1 : (starRingEnd ℂ) (ξ 1) = (ξ 1)⁻¹ := star_eq_inv_of_unit _ (hξ 1)
  obtain ⟨g, s⟩ := l
  have hc : (starRingEnd ℂ) (χ s) * χ s = 1 := by rw [mul_comm]; exact chi_mul_star s
  change Matrix.det (W3T ξ (g, s)) = 1
  rcases idx_cases g with rfl | rfl | rfl
  · simp +decide only [W3T]
    rw [Matrix.det_fin_three]
    simp []
    linear_combination hc
  · simp +decide only [W3T]
    rw [Matrix.det_fin_three]
    simp []
    linear_combination hc
  · simp +decide only [W3T]
    rw [Matrix.det_fin_three]
    simp [hs0, hs1]
    field_simp
    linear_combination hc

theorem W3_ueb (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : IsUnitaryErrorBasis (W3 ξ) :=
  isUnitaryErrorBasis_of_gauge3 _ _
    (ThreeCycleMatrix.monomial_family_is_unitary_error_basis (anchorTriple ξ hξ 3))
    gaugeL3 1 gaugeL3_unitary one_unitary3 gaugeC3 gaugeC3_normSq gaugeσ3
    (W3_gauge ξ hξ) (W3_det ξ hξ)

theorem W3_finrank (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ (firstOrderSpace (W3 ξ)) = 18 + 2 * resonanceCount (anchorTriple ξ hξ 3) :=
  finrank_firstOrderSpace_of_gauge_monomial (anchorTriple ξ hξ 3) (W3 ξ) (W3_ueb ξ hξ)
    gaugeL3 1 gaugeL3_unitary one_unitary3 gaugeC3 gaugeC3_normSq gaugeσ3 (W3_gauge ξ hξ)

end Anchor3

end CKM.NativeFirstOrder

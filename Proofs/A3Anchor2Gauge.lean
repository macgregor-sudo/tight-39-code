module

public import A3Anchor2Transport
public import A3Anchor0Gauge

@[expose] public section

/-!
# Anchor H2: the nine hidden representatives and their gauge relation

* `anchor2W ξ hξ (a, b) = χ(ab − a) • (L · M_d(a, b) · R)` with `d = anchorPhases ξ 2`,
  `L = G_L · diag(1, −C⁻¹, (CD)⁻¹)` (`G_L = −[[1,0,0],[0,0,1],[0,1,0]]`), `R = diag(−1, −C, −CD)`.
* Unitary-error-basis property and the first-order dimension `18 + 2 r(d_H2)`, at every unit phase.
* The three family identities: the `T₂⁻¹`-images of the hidden literal points are `χ(t) • W l`.
-/

noncomputable section

namespace CKM.NativeFirstOrder

namespace Anchor2

open UnitaryErrorBases

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega
local notation "χ" => UnitaryErrorBases.ThreeCycleFourier.character

private theorem idx_add11 : (1 : Index) + 1 = 2 := rfl
private theorem idx_add12 : (1 : Index) + 2 = 0 := rfl
private theorem idx_add21 : (2 : Index) + 1 = 0 := rfl
private theorem idx_add22 : (2 : Index) + 2 = 1 := rfl
private theorem idx_neg1 : -(1 : Index) = 2 := rfl
private theorem idx_neg2 : -(2 : Index) = 1 := rfl
private theorem idx_sub12 : (1 : Index) - 2 = 2 := rfl
private theorem idx_sub21 : (2 : Index) - 1 = 1 := rfl
private theorem idx_mul22 : (2 : Index) * 2 = 1 := rfl
private theorem idx_val2 : (2 : Index).val = 2 := rfl

/-- Diagonal of the left gauge factor (before the signed swap `G_L`). -/
def gaugeLv (ξ : Fin 4 → ℂ) (j : Index) : ℂ :=
  if j = 0 then 1 else if j = 1 then -(ξ 2)⁻¹ else (ξ 2 * ξ 3)⁻¹

/-- Left gauge factor `G_L · diag(1, −C⁻¹, (CD)⁻¹)`, `G_L = −[[1,0,0],[0,0,1],[0,1,0]]`. -/
def gaugeL (ξ : Fin 4 → ℂ) : Mat :=
  Matrix.of fun i j => if i + j = 0 then -gaugeLv ξ j else 0

/-- Diagonal of the right gauge factor. -/
def gaugeRv (ξ : Fin 4 → ℂ) (j : Index) : ℂ :=
  if j = 0 then -1 else if j = 1 then -ξ 2 else -(ξ 2 * ξ 3)

/-- Right gauge factor `diag(−1, −C, −CD)`. -/
def gaugeR (ξ : Fin 4 → ℂ) : Mat := Matrix.diagonal (gaugeRv ξ)

/-- Scalar factors `χ(ab − a)` at label `(a, b)` (clock index first). -/
def gaugeC (l : Label) : ℂ := χ (l.1 * l.2 - l.1)

/-- The nine hidden representatives of anchor H2, in gauge form. -/
def anchor2W (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Family := fun l =>
  gaugeC l • (gaugeL ξ * monomialFamily (anchorTriple ξ hξ 2) l * gaugeR ξ)

/-! ## Images of the hidden literal points -/

/-- `T₂⁻¹`-image (times three) of a frame-1–3 phase projector. -/
def imgPh (x y : ℂ) : CompactAlbert.TitsComplexMatrix := !![star x * y, 0, 0; 0, 0, star y; 0, -x, 0]

/-- `T₂⁻¹`-image (times three) of a frame-4–6 hidden matrix. -/
def imgTwo (x y : ℂ) : CompactAlbert.TitsComplexMatrix := !![0, star (x * y), 0; -y, 0, 0; 0, 0, x]

/-- `T₂⁻¹`-image (times three) of a frame-10–12 hidden matrix. -/
def imgNj (x y : ℂ) : CompactAlbert.TitsComplexMatrix := !![0, 0, x * y; 0, star y, 0; -star x, 0, 0]

theorem imgPh_apply (x y : ℂ) (i j : Index) :
    imgPh x y i j =
      if i = 0 ∧ j = 0 then star x * y else if i = 1 ∧ j = 2 then star y
        else if i = 2 ∧ j = 1 then -x else 0 := by
  rcases Anchor0.indexCases i with rfl | rfl | rfl <;>
    rcases Anchor0.indexCases j with rfl | rfl | rfl <;> rfl

theorem imgTwo_apply (x y : ℂ) (i j : Index) :
    imgTwo x y i j =
      if i = 0 ∧ j = 1 then star (x * y) else if i = 1 ∧ j = 0 then -y
        else if i = 2 ∧ j = 2 then x else 0 := by
  rcases Anchor0.indexCases i with rfl | rfl | rfl <;>
    rcases Anchor0.indexCases j with rfl | rfl | rfl <;> rfl

theorem imgNj_apply (x y : ℂ) (i j : Index) :
    imgNj x y i j =
      if i = 0 ∧ j = 2 then x * y else if i = 1 ∧ j = 1 then star y
        else if i = 2 ∧ j = 0 then -star x else 0 := by
  rcases Anchor0.indexCases i with rfl | rfl | rfl <;>
    rcases Anchor0.indexCases j with rfl | rfl | rfl <;> rfl

theorem gaugeL_mul_apply (ξ : Fin 4 → ℂ) (Y : Mat) (i j : Index) :
    (gaugeL ξ * Y) i j = -gaugeLv ξ (-i) * Y (-i) j := by
  rcases Anchor0.indexCases i with rfl | rfl | rfl <;>
    simp +decide [Matrix.mul_apply, gaugeL, Anchor0.sum_three, idx_add11, idx_add12, idx_add21, idx_add22, idx_neg1, idx_neg2, idx_sub12, idx_sub21, idx_mul22, idx_val2]

theorem anchor2W_apply (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (l : Label) (i j : Index) :
    anchor2W ξ hξ l i j =
      gaugeC l * (-gaugeLv ξ (-i) *
        ((if -i = j + l.2 then ThreeCycleFourier.phaseEntry (anchorTriple ξ hξ 2).val l.2 j else 0) *
          (UnitaryErrorBases.omega ^ j.val) ^ l.1.val) * gaugeRv ξ j) := by
  rw [anchor2W, Matrix.smul_apply, gaugeR, Matrix.mul_diagonal, gaugeL_mul_apply, smul_eq_mul,
    Anchor0.monomialFamily_apply]

/-! ## The three family identities (all unit phases, resonant ones included) -/

/-- Literal frames `1 + s` (phase projectors): label `(−s, 0)`, outcome factor `χ t`. -/
theorem famA (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (s t i j : Index) :
    imgPh (χ t) (χ (s - t)) i j = χ t * anchor2W ξ hξ (-s, 0) i j := by
  rw [anchor2W_apply, imgPh_apply]
  have hstar : ∀ k, star (ξ k) = (ξ k)⁻¹ := fun k => Anchor0.star_eq_inv_of_unit _ (hξ k)
  have hconjω : (starRingEnd ℂ) ω = ω ^ 2 := Anchor0.star_omega
  have h2 := Anchor0.ne_zero_of_unit _ (hξ 2)
  have h3 := Anchor0.ne_zero_of_unit _ (hξ 3)
  -- Remove off-support matrix entries before splitting either phase index.
  rcases Anchor0.indexCases i with rfl | rfl | rfl <;>
    rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
    simp +decide [gaugeLv, gaugeRv, ThreeCycleFourier.phaseEntry, anchorTriple, anchorPhases,
      idx_add11, idx_add12, idx_add21, idx_add22, idx_neg1, idx_neg2, idx_sub12, idx_sub21,
      idx_mul22, idx_val2] <;>
    rcases Anchor0.indexCases s with rfl | rfl | rfl <;>
    rcases Anchor0.indexCases t with rfl | rfl | rfl <;>
    simp +decide [gaugeC, gaugeLv, gaugeRv, ThreeCycleFourier.phaseEntry,
        Anchor0.omega_eq, Anchor0.star_omega, hconjω,
        Anchor0.val_one, Anchor0.chi_zero, Anchor0.chi_one, Anchor0.chi_two,
        idx_add11, idx_add12, idx_add21, idx_add22, idx_neg1, idx_neg2, idx_sub12, idx_sub21, idx_mul22, idx_val2] <;>
    (try field_simp) <;> (try ring_nf) <;>
    (try simp only [Anchor0.omega_cube, Anchor0.omega_pow_four, Anchor0.omega_pow_five,
      Anchor0.omega_pow_six, Anchor0.omega_pow_seven])

/-- Literal frames `4 + s` (group-0 hidden matrices): label `(s, 2)`, outcome factor `χ t`. -/
theorem famB (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (s t i j : Index) :
    imgTwo (χ t) (χ (s + t)) i j = χ t * anchor2W ξ hξ (s, 2) i j := by
  rw [anchor2W_apply, imgTwo_apply]
  have hstar : ∀ k, star (ξ k) = (ξ k)⁻¹ := fun k => Anchor0.star_eq_inv_of_unit _ (hξ k)
  have hconjω : (starRingEnd ℂ) ω = ω ^ 2 := Anchor0.star_omega
  have h2 := Anchor0.ne_zero_of_unit _ (hξ 2)
  have h3 := Anchor0.ne_zero_of_unit _ (hξ 3)
  -- Remove off-support matrix entries before splitting either phase index.
  rcases Anchor0.indexCases i with rfl | rfl | rfl <;>
    rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
    simp +decide [gaugeLv, gaugeRv, ThreeCycleFourier.phaseEntry, anchorTriple, anchorPhases,
      idx_add11, idx_add12, idx_add21, idx_add22, idx_neg1, idx_neg2, idx_sub12, idx_sub21,
      idx_mul22, idx_val2] <;>
    rcases Anchor0.indexCases s with rfl | rfl | rfl <;>
    rcases Anchor0.indexCases t with rfl | rfl | rfl <;>
    simp +decide [gaugeC, gaugeLv, gaugeRv, ThreeCycleFourier.phaseEntry, anchorTriple, anchorPhases,
        star_mul', Anchor0.omega_eq, Anchor0.star_omega, hconjω,
        Anchor0.val_one, Anchor0.chi_zero, Anchor0.chi_one, Anchor0.chi_two,
        idx_add11, idx_add12, idx_add21, idx_add22, idx_neg1, idx_neg2, idx_sub12, idx_sub21, idx_mul22, idx_val2] <;>
    (try field_simp) <;> (try ring_nf) <;>
    (try simp only [Anchor0.omega_cube, Anchor0.omega_pow_four, Anchor0.omega_pow_five,
      Anchor0.omega_pow_six, Anchor0.omega_pow_seven, Anchor0.omega_pow_eight])

/-- Literal frames `10 + s` (group-2 hidden matrices) at outcome `−t`: label `(−s, 1)`, factor `χ t`. -/
theorem famC (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (s t i j : Index) :
    imgNj (ξ 2 * χ (-t)) (ξ 3 * χ (s + -t)) i j = χ t * anchor2W ξ hξ (-s, 1) i j := by
  rw [anchor2W_apply, imgNj_apply]
  have hstar : ∀ k, (starRingEnd ℂ) (ξ k) = (ξ k)⁻¹ := fun k => Anchor0.star_eq_inv_of_unit _ (hξ k)
  have hconjω : (starRingEnd ℂ) ω = ω ^ 2 := Anchor0.star_omega
  have h2 := Anchor0.ne_zero_of_unit _ (hξ 2)
  have h3 := Anchor0.ne_zero_of_unit _ (hξ 3)
  -- Remove off-support matrix entries before splitting either phase index.
  rcases Anchor0.indexCases i with rfl | rfl | rfl <;>
    rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
    simp +decide [gaugeLv, gaugeRv, ThreeCycleFourier.phaseEntry, anchorTriple, anchorPhases,
      idx_add11, idx_add12, idx_add21, idx_add22, idx_neg1, idx_neg2, idx_sub12, idx_sub21,
      idx_mul22, idx_val2] <;>
    rcases Anchor0.indexCases s with rfl | rfl | rfl <;>
    rcases Anchor0.indexCases t with rfl | rfl | rfl <;>
    simp +decide [gaugeC, gaugeLv, gaugeRv, ThreeCycleFourier.phaseEntry,
        star_mul', hstar, Anchor0.omega_eq, Anchor0.star_omega, hconjω,
        Anchor0.val_one, Anchor0.chi_zero, Anchor0.chi_one, Anchor0.chi_two,
        idx_add11, idx_add12, idx_add21, idx_add22, idx_neg1, idx_neg2, idx_sub12, idx_sub21, idx_mul22, idx_val2] <;>
    (try field_simp) <;> (try ring_nf) <;>
    (try simp only [Anchor0.omega_cube, Anchor0.omega_pow_four, Anchor0.omega_pow_five,
      Anchor0.omega_pow_six])

/-! ## Unitarity, determinant and the unitary-error-basis property -/

theorem gaugeL_unitary (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (gaugeL ξ).conjTranspose * gaugeL ξ = 1 := by
  have hstar : ∀ k, (starRingEnd ℂ) (ξ k) = (ξ k)⁻¹ := fun k => Anchor0.star_eq_inv_of_unit _ (hξ k)
  have h2 := Anchor0.ne_zero_of_unit _ (hξ 2)
  have h3 := Anchor0.ne_zero_of_unit _ (hξ 3)
  ext i j
  rcases Anchor0.indexCases i with rfl | rfl | rfl <;> rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
    simp +decide [Matrix.mul_apply, Matrix.conjTranspose_apply, gaugeL, gaugeLv, Anchor0.sum_three,
      idx_add11, idx_add12, idx_add21, idx_add22, idx_neg1, idx_neg2, idx_sub12, idx_sub21, idx_mul22, idx_val2, hstar, h2, h3, mul_inv_rev, mul_assoc] <;>
      field_simp [h2, h3]

theorem gaugeR_unitary (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    gaugeR ξ * (gaugeR ξ).conjTranspose = 1 := by
  have hstar : ∀ k, (starRingEnd ℂ) (ξ k) = (ξ k)⁻¹ := fun k => Anchor0.star_eq_inv_of_unit _ (hξ k)
  have h2 := Anchor0.ne_zero_of_unit _ (hξ 2)
  have h3 := Anchor0.ne_zero_of_unit _ (hξ 3)
  unfold gaugeR
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  change Matrix.diagonal _ = Matrix.diagonal (fun _ : Index => (1 : ℂ))
  apply congrArg Matrix.diagonal
  funext j
  by_cases h0 : j = 0
  · simp [gaugeRv, h0]
  · by_cases h1 : j = 1
    · simp [gaugeRv, h0, h1, hstar, h2]
    · simp [gaugeRv, h0, h1, hstar, mul_inv_rev, mul_assoc, h2, h3]
      <;> field_simp [h2, h3]

theorem gaugeC_normSq (l : Label) : Complex.normSq (gaugeC l) = 1 := Anchor0.normSq_chi _

theorem gaugeC_cube (l : Label) : gaugeC l ^ 3 = 1 := by
  show (ω ^ (l.1 * l.2 - l.1).val) ^ 3 = 1
  rw [← pow_mul, mul_comm, pow_mul, Anchor0.omega_cube, one_pow]

theorem gaugeL_det_mul_gaugeR_det (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (gaugeL ξ).det * (gaugeR ξ).det = 1 := by
  have h2 := Anchor0.ne_zero_of_unit _ (hξ 2)
  have h3 := Anchor0.ne_zero_of_unit _ (hξ 3)
  rw [gaugeR, Matrix.det_diagonal,
    show (∏ i : Index, gaugeRv ξ i) = gaugeRv ξ 0 * gaugeRv ξ 1 * gaugeRv ξ 2 from Fin.prod_univ_three _]
  have hL : (gaugeL ξ).det =
      gaugeL ξ 0 0 * gaugeL ξ 1 1 * gaugeL ξ 2 2 - gaugeL ξ 0 0 * gaugeL ξ 1 2 * gaugeL ξ 2 1 -
        gaugeL ξ 0 1 * gaugeL ξ 1 0 * gaugeL ξ 2 2 + gaugeL ξ 0 1 * gaugeL ξ 1 2 * gaugeL ξ 2 0 +
        gaugeL ξ 0 2 * gaugeL ξ 1 0 * gaugeL ξ 2 1 - gaugeL ξ 0 2 * gaugeL ξ 1 1 * gaugeL ξ 2 0 :=
    Matrix.det_fin_three _
  rw [hL]
  simp +decide [gaugeL, gaugeLv, gaugeRv, idx_add11, idx_add12, idx_add21, idx_add22, idx_neg1, idx_neg2, idx_sub12, idx_sub21, idx_mul22, idx_val2]
  field_simp [h2, h3]

theorem anchor2W_det (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (l : Label) : (anchor2W ξ hξ l).det = 1 := by
  have hM := ((ThreeCycleMatrix.monomial_family_is_unitary_error_basis (anchorTriple ξ hξ 2)).1 l).2
  rw [anchor2W, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, hM, ZMod.card, gaugeC_cube, one_mul,
    mul_one, gaugeL_det_mul_gaugeR_det ξ hξ]

theorem anchor2W_ueb (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : IsUnitaryErrorBasis (anchor2W ξ hξ) :=
  Anchor0.isUnitaryErrorBasis_of_gauge _ _
    (ThreeCycleMatrix.monomial_family_is_unitary_error_basis (anchorTriple ξ hξ 2))
    (gaugeL ξ) (gaugeR ξ) (gaugeL_unitary ξ hξ) (gaugeR_unitary ξ hξ) gaugeC gaugeC_normSq
    (Equiv.refl _) (fun _ => rfl) (anchor2W_det ξ hξ)

theorem anchor2W_finrank (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ (firstOrderSpace (anchor2W ξ hξ)) =
      18 + 2 * resonanceCount (anchorTriple ξ hξ 2) :=
  finrank_firstOrderSpace_of_gauge_monomial (anchorTriple ξ hξ 2) (anchor2W ξ hξ) (anchor2W_ueb ξ hξ)
    (gaugeL ξ) (gaugeR ξ) (gaugeL_unitary ξ hξ) (gaugeR_unitary ξ hξ) gaugeC gaugeC_normSq
    (Equiv.refl _) (fun _ => rfl)

end Anchor2

end CKM.NativeFirstOrder

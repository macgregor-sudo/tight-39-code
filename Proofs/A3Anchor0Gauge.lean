module

public import A3Family
public import ThreeCycleMatrixSupport
public import ThreeCycleUnitaryErrorBasis

@[expose] public section

/-!
# Anchor H0: matrix identities for the hidden frames

* `hiddenMatrix_neg`: `hiddenMatrix ξ g s (-t) = χ(t) • hiddenMatrix ξ g s 0` (at every phase).
* `anchor0W`: the nine hidden representatives `W (g, s) = hiddenMatrix ξ g s 0`.
* `anchor0W_gauge`: `W (g, s) = χ(g s) • (L * monomialFamily d (-s, -g) * R)` with
  `L = J · diag(1, -D⁻¹, C)`, `R = diag(1, D, C⁻¹)` and `d = anchorPhases ξ 0`.
-/

noncomputable section

namespace CKM.NativeFirstOrder

namespace Anchor0

open UnitaryErrorBases

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega
local notation "χ" => UnitaryErrorBases.ThreeCycleFourier.character

theorem indexCases (i : Index) : i = 0 ∨ i = 1 ∨ i = 2 :=
  (by decide : ∀ j : Index, j = 0 ∨ j = 1 ∨ j = 2) i

theorem chi_zero : χ 0 = 1 := rfl
theorem chi_one : χ 1 = ω := by
  show ω ^ (1 : ZMod 3).val = ω
  rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]
theorem chi_two : χ 2 = ω ^ 2 := rfl

theorem omega_cube : ω ^ 3 = 1 := ThreeCycleFourier.omega_cube

theorem chi_add (a b : Index) : χ (a + b) = χ a * χ b := by
  show ω ^ (a + b).val = ω ^ a.val * ω ^ b.val
  rw [ZMod.val_add, ← pow_add, pow_eq_pow_mod (a.val + b.val) omega_cube]

theorem normSq_omega : Complex.normSq ω = 1 := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  simp only [ThreeCycleFourier.omega, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  norm_num
  nlinarith [hs]

theorem star_omega_mul : star ω * ω = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, normSq_omega, Complex.ofReal_one]

theorem star_omega : star ω = ω ^ 2 := by
  calc star ω = star ω * ω ^ 3 := by rw [omega_cube, mul_one]
    _ = (star ω * ω) * ω ^ 2 := by ring
    _ = ω ^ 2 := by rw [star_omega_mul, one_mul]

theorem star_chi (a : Index) : star (χ a) = χ (-a) := by
  rcases indexCases a with rfl | rfl | rfl
  · rw [neg_zero, chi_zero, star_one]
  · rw [chi_one, star_omega, show -(1 : Index) = 2 from rfl, chi_two]
  · rw [chi_two, star_pow, star_omega, show -(2 : Index) = 1 from rfl, chi_one, ← pow_mul,
      pow_eq_pow_mod (2 * 2) omega_cube]
    norm_num

theorem normSq_chi (a : Index) : Complex.normSq (χ a) = 1 := by
  show Complex.normSq (ω ^ a.val) = 1
  rw [map_pow, normSq_omega, one_pow]

theorem chi_neg_mul_self (t : Index) : χ (-t) * χ (-t) = χ t := by
  rw [← chi_add, show -t + -t = t by
    rcases indexCases t with rfl | rfl | rfl <;> decide]

/-! ## The hidden matrices at negated outcomes -/

theorem hiddenMatrix_neg (ξ : Fin 4 → ℂ) (g : Fin 3) (s t : UnitaryErrorBases.ComplexQuartet.PhaseIndex) :
    hiddenMatrix ξ g s (-t) = χ t • hiddenMatrix ξ g s 0 := by
  have hs : χ (s + -t) = χ s * χ (-t) := chi_add s (-t)
  have hst : star (χ (-t)) = χ (-t) * χ (-t) := by
    rw [star_chi, neg_neg, chi_neg_mul_self]
  have hz := chi_neg_mul_self t
  rw [← hz]
  rcases (by decide : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2) g with rfl | rfl | rfl <;>
  · simp only [hiddenMatrix, hs, add_zero, chi_zero, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix,
        QuadraticCertificate.ExactCKMABFrames.ellNMatrix,
        QuadraticCertificate.ExactCKMCDFrames.njMatrix, star_mul', hst] <;> ring

/-! ## The gauge relation to the monomial normal form -/

/-- The nine hidden representatives of anchor H0: label `(g, s)` is frame `4 + 3g + s` at outcome 0. -/
def anchor0W (ξ : Fin 4 → ℂ) : Family := fun l => hiddenMatrix ξ l.1 l.2 0

/-- Left gauge factor `J · diag(1, -D⁻¹, C)` (with `J` the antidiagonal permutation). -/
def gaugeL (ξ : Fin 4 → ℂ) : Mat :=
  Matrix.of fun i j => if i + j = 2 then
    (if j = 0 then 1 else if j = 1 then -(ξ 3)⁻¹ else ξ 2) else 0

/-- Right gauge factor `diag(1, D, C⁻¹)`. -/
def gaugeR (ξ : Fin 4 → ℂ) : Mat :=
  Matrix.diagonal fun j => if j = 0 then 1 else if j = 1 then ξ 3 else (ξ 2)⁻¹

/-- Scalar factors `χ(g s)`. -/
def gaugeC (l : Label) : ℂ := χ (l.1 * l.2)

/-- Label map `(g, s) ↦ (-s, -g)` (clock index first). -/
def gaugeσ : Label ≃ Label where
  toFun l := (-l.2, -l.1)
  invFun l := (-l.2, -l.1)
  left_inv l := by simp
  right_inv l := by simp

private theorem index_add_one_one : (1 : Index) + 1 = 2 := rfl
private theorem index_sub_two_one : (2 : Index) - 1 = 1 := rfl
private theorem index_neg_one : -(1 : Index) = 2 := rfl
private theorem index_neg_two : -(2 : Index) = 1 := rfl
private theorem index_mul_two_two : (2 : Index) * 2 = 1 := rfl
private theorem index_val_two : (2 : Index).val = 2 := rfl

theorem sum_three (f : Index → ℂ) : ∑ i, f i = f 0 + f 1 + f 2 := Fin.sum_univ_three f

theorem gaugeL_mul_apply (ξ : Fin 4 → ℂ) (Y : Mat) (i j : Index) :
    (gaugeL ξ * Y) i j =
      (if 2 - i = 0 then 1 else if 2 - i = 1 then -(ξ 3)⁻¹ else ξ 2) * Y (2 - i) j := by
  rcases indexCases i with rfl | rfl | rfl <;>
    simp +decide [Matrix.mul_apply, gaugeL, sum_three, index_add_one_one, index_sub_two_one]

theorem monomialFamily_apply (d : PhaseTriple) (a b i j : Index) :
    monomialFamily d (a, b) i j =
      (if i = j + b then ThreeCycleFourier.phaseEntry d.val b j else 0) *
        (UnitaryErrorBases.omega ^ j.val) ^ a.val := by
  rw [ThreeCycleMatrix.monomialFamily_eq, ThreeCycleMatrix.rightFactor, clock,
    Matrix.diagonal_pow, Matrix.mul_diagonal, ThreeCycleMatrix.leftFactor_apply]
  rfl

theorem gauge_rhs_apply (ξ : Fin 4 → ℂ) (d : PhaseTriple) (l : Label) (i j : Index) :
    (gaugeC l • (gaugeL ξ * monomialFamily d (gaugeσ l) * gaugeR ξ)) i j =
      gaugeC l * ((if 2 - i = 0 then 1 else if 2 - i = 1 then -(ξ 3)⁻¹ else ξ 2) *
        ((if 2 - i = j + -l.1 then ThreeCycleFourier.phaseEntry d.val (-l.1) j else 0) *
          (UnitaryErrorBases.omega ^ j.val) ^ (-l.2).val) *
        (if j = 0 then 1 else if j = 1 then ξ 3 else (ξ 2)⁻¹)) := by
  rw [Matrix.smul_apply, gaugeR, Matrix.mul_diagonal, gaugeL_mul_apply, smul_eq_mul]
  change _ * (_ * monomialFamily d (-l.2, -l.1) (2 - i) j * _) = _
  rw [monomialFamily_apply]

theorem star_eq_inv_of_unit (z : ℂ) (hz : Complex.normSq z = 1) : star z = z⁻¹ := by
  rw [Complex.inv_def, hz, inv_one, Complex.ofReal_one, mul_one]; rfl

theorem ne_zero_of_unit (z : ℂ) (hz : Complex.normSq z = 1) : z ≠ 0 := by
  intro h; rw [h, map_zero] at hz; exact zero_ne_one hz

theorem omega_eq : UnitaryErrorBases.omega = ω := rfl

theorem omega_pow_reduce (n : ℕ) : ω ^ (n + 3) = ω ^ n := by
  rw [pow_add, omega_cube, mul_one]

theorem omega_pow_four : ω ^ 4 = ω := by rw [omega_pow_reduce 1, pow_one]
theorem omega_pow_five : ω ^ 5 = ω ^ 2 := omega_pow_reduce 2
theorem omega_pow_six : ω ^ 6 = 1 := by rw [omega_pow_reduce 3, omega_cube]
theorem omega_pow_seven : ω ^ 7 = ω := by rw [omega_pow_reduce 4, omega_pow_four]
theorem omega_pow_eight : ω ^ 8 = ω ^ 2 := by rw [omega_pow_reduce 5, omega_pow_five]
theorem val_one : (1 : Index).val = 1 := rfl
theorem val_two : (2 : Index).val = 2 := rfl

/-- Entries of the three hidden matrix shapes, at `ZMod 3` indices. -/
theorem hiddenMatrix_zero_apply (ξ : Fin 4 → ℂ) (s t i j : Index) :
    hiddenMatrix ξ (0 : Index) s t i j =
      if i = 0 ∧ j = 2 then χ t * χ (s + t) else if i = 1 ∧ j = 1 then -star (χ (s + t))
        else if i = 2 ∧ j = 0 then star (χ t) else 0 := by
  rcases indexCases i with rfl | rfl | rfl <;> rcases indexCases j with rfl | rfl | rfl <;> rfl

theorem hiddenMatrix_one_apply (ξ : Fin 4 → ℂ) (s t i j : Index) :
    hiddenMatrix ξ (1 : Index) s t i j =
      if i = 0 ∧ j = 0 then ξ 0 * χ t * (ξ 1 * χ (s + t))
        else if i = 1 ∧ j = 2 then -star (ξ 1 * χ (s + t))
        else if i = 2 ∧ j = 1 then star (ξ 0 * χ t) else 0 := by
  rcases indexCases i with rfl | rfl | rfl <;> rcases indexCases j with rfl | rfl | rfl <;> rfl

theorem hiddenMatrix_two_apply (ξ : Fin 4 → ℂ) (s t i j : Index) :
    hiddenMatrix ξ (2 : Index) s t i j =
      if i = 0 ∧ j = 1 then ξ 2 * χ t * (ξ 3 * χ (s + t))
        else if i = 1 ∧ j = 0 then -star (ξ 3 * χ (s + t))
        else if i = 2 ∧ j = 2 then star (ξ 2 * χ t) else 0 := by
  rcases indexCases i with rfl | rfl | rfl <;> rcases indexCases j with rfl | rfl | rfl <;> rfl

/-- Anchor H0 hidden representatives are a gauge image of the monomial normal form. -/
theorem anchor0W_gauge (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (l : Label) :
    anchor0W ξ l =
      gaugeC l • (gaugeL ξ * monomialFamily (anchorTriple ξ hξ 0) (gaugeσ l) * gaugeR ξ) := by
  have hstar : ∀ k, star (ξ k) = (ξ k)⁻¹ := fun k => star_eq_inv_of_unit _ (hξ k)
  have hne : ∀ k, ξ k ≠ 0 := fun k => ne_zero_of_unit _ (hξ k)
  have h0 := hne 0
  have h1 := hne 1
  have h2 := hne 2
  have h3 := hne 3
  obtain ⟨g, s⟩ := l
  ext i j
  rw [gauge_rhs_apply]
  change hiddenMatrix ξ g s 0 i j = _
  rcases indexCases g with rfl | rfl | rfl <;> rcases indexCases s with rfl | rfl | rfl <;>
    rcases indexCases i with rfl | rfl | rfl <;> rcases indexCases j with rfl | rfl | rfl <;>
    simp +decide [hiddenMatrix_zero_apply, hiddenMatrix_one_apply, hiddenMatrix_two_apply, gaugeC,
        ThreeCycleFourier.phaseEntry, anchorTriple, anchorPhases, star_mul', hstar,
        omega_eq, star_omega, val_one, chi_zero, chi_one, chi_two,
        index_add_one_one, index_sub_two_one, index_neg_one, index_neg_two,
        index_mul_two_two, index_val_two] <;>
    (try field_simp) <;> (try ring_nf) <;>
    (try simp only [omega_cube, omega_pow_four, omega_pow_five, omega_pow_six])

/-! ## Unitarity of the gauge data and the unitary-error-basis property -/

theorem gaugeL_unitary (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (gaugeL ξ).conjTranspose * gaugeL ξ = 1 := by
  have hstar : ∀ k, (starRingEnd ℂ) (ξ k) = (ξ k)⁻¹ := fun k => star_eq_inv_of_unit _ (hξ k)
  have h2 := ne_zero_of_unit _ (hξ 2)
  have h3 := ne_zero_of_unit _ (hξ 3)
  ext i j
  rcases indexCases i with rfl | rfl | rfl <;> rcases indexCases j with rfl | rfl | rfl <;>
    simp +decide [Matrix.mul_apply, Matrix.conjTranspose_apply, gaugeL, sum_three,
      index_add_one_one, hstar, h2, h3]

theorem gaugeR_unitary (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    gaugeR ξ * (gaugeR ξ).conjTranspose = 1 := by
  have hstar : ∀ k, (starRingEnd ℂ) (ξ k) = (ξ k)⁻¹ := fun k => star_eq_inv_of_unit _ (hξ k)
  have h2 := ne_zero_of_unit _ (hξ 2)
  have h3 := ne_zero_of_unit _ (hξ 3)
  unfold gaugeR
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  change Matrix.diagonal _ = Matrix.diagonal (fun _ : Index => (1 : ℂ))
  apply congrArg Matrix.diagonal
  funext j
  by_cases h0 : j = 0
  · simp [h0]
  · by_cases h1 : j = 1
    · simp [h0, h1, hstar, h3]
    · simp [h0, h1, hstar, h2]

theorem gaugeC_normSq (l : Label) : Complex.normSq (gaugeC l) = 1 := normSq_chi _

/-- A gauge image of a unitary error basis with determinant-one members is a unitary error basis. -/
theorem isUnitaryErrorBasis_of_gauge (U U' : Family) (hU : IsUnitaryErrorBasis U) (L R : Mat)
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

theorem mul_star_of_normSq (z : ℂ) (hz : Complex.normSq z = 1) : z * star z = 1 := by
  rw [mul_comm]; exact star_mul_self_of_normSq z hz

theorem normSq_mul_unit (z w : ℂ) (hz : Complex.normSq z = 1) (hw : Complex.normSq w = 1) :
    Complex.normSq (z * w) = 1 := by
  rw [map_mul, hz, hw, one_mul]

theorem det_twoInputMatrix (z w : ℂ) :
    (QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix z w).det =
      z * star z * (w * star w) := by
  simp [Matrix.det_fin_three, QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix]
  ring

theorem det_ellNMatrix (z w : ℂ) :
    (QuadraticCertificate.ExactCKMABFrames.ellNMatrix z w).det = z * star z * (w * star w) := by
  simp [Matrix.det_fin_three, QuadraticCertificate.ExactCKMABFrames.ellNMatrix]
  ring

theorem det_njMatrix (z w : ℂ) :
    (QuadraticCertificate.ExactCKMCDFrames.njMatrix z w).det = z * star z * (w * star w) := by
  simp [Matrix.det_fin_three, QuadraticCertificate.ExactCKMCDFrames.njMatrix]
  ring

theorem anchor0W_det (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (l : Label) : (anchor0W ξ l).det = 1 := by
  obtain ⟨g, s⟩ := l
  have hu : ∀ k r, Complex.normSq (ξ k * χ r) = 1 := fun k r =>
    normSq_mul_unit _ _ (hξ k) (normSq_chi r)
  change Matrix.det (hiddenMatrix ξ g s 0 : Matrix (Fin 3) (Fin 3) ℂ) = 1
  rcases indexCases g with rfl | rfl | rfl
  · change (QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix _ _).det = 1
    rw [det_twoInputMatrix, mul_star_of_normSq _ (normSq_chi _),
      mul_star_of_normSq _ (normSq_chi _), one_mul]
  · change (QuadraticCertificate.ExactCKMABFrames.ellNMatrix _ _).det = 1
    rw [det_ellNMatrix, mul_star_of_normSq _ (hu _ _), mul_star_of_normSq _ (hu _ _), one_mul]
  · change (QuadraticCertificate.ExactCKMCDFrames.njMatrix _ _).det = 1
    rw [det_njMatrix, mul_star_of_normSq _ (hu _ _), mul_star_of_normSq _ (hu _ _), one_mul]

theorem anchor0W_ueb (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : IsUnitaryErrorBasis (anchor0W ξ) :=
  isUnitaryErrorBasis_of_gauge _ _
    (ThreeCycleMatrix.monomial_family_is_unitary_error_basis (anchorTriple ξ hξ 0))
    (gaugeL ξ) (gaugeR ξ) (gaugeL_unitary ξ hξ) (gaugeR_unitary ξ hξ) gaugeC gaugeC_normSq gaugeσ
    (anchor0W_gauge ξ hξ) (anchor0W_det ξ hξ)

theorem anchor0W_finrank (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ (firstOrderSpace (anchor0W ξ)) =
      18 + 2 * resonanceCount (anchorTriple ξ hξ 0) :=
  finrank_firstOrderSpace_of_gauge_monomial (anchorTriple ξ hξ 0) (anchor0W ξ) (anchor0W_ueb ξ hξ)
    (gaugeL ξ) (gaugeR ξ) (gaugeL_unitary ξ hξ) (gaugeR_unitary ξ hξ) gaugeC gaugeC_normSq gaugeσ
    (anchor0W_gauge ξ hξ)

end Anchor0

end CKM.NativeFirstOrder

module

public import A3Anchor1Points
public import ThreeCycleMatrixSupport

@[expose] public section

/-!
# Anchor H1, part 2: the gauge-normalized unitary error basis

`W l = Lg * monomialFamily d (σ l) * Rg` with `d = d_{H1}(ξ)`, `Lg = [[0,0,−A⁻¹],[0,B,0],[−1,0,0]]`,
`Rg = diag(−1, −B⁻¹, −A)`; and the images under `T₁⁻¹` of the nine non-quartet frames.
-/

noncomputable section

namespace CKM.NativeFirstOrder

open NativePolynomial CompactAlbert UnitaryErrorBases.ComplexQuartet

namespace Anchor1

open UnitaryErrorBases

local notation "χ" => UnitaryErrorBases.ThreeCycleFourier.character

theorem omega_eq : UnitaryErrorBases.omega = UnitaryErrorBases.ThreeCycleFourier.omega := rfl

theorem clock_pow_eq (a : Index) :
    clock ^ a.val = Matrix.diagonal (fun j : Index => χ a ^ j.val) := by
  rw [clock, Matrix.diagonal_pow]
  congr 1
  funext j
  simp only [Pi.pow_apply, UnitaryErrorBases.ThreeCycleFourier.character, omega_eq, ← pow_mul,
    mul_comm]

theorem mono_apply (d : PhaseTriple) (a b i j : Index) :
    monomialFamily d (a, b) i j =
      (if i = j + b then ThreeCycleFourier.phaseEntry d.val b j else 0) * χ a ^ j.val := by
  rw [ThreeCycleMatrix.monomialFamily_eq, ThreeCycleMatrix.rightFactor, clock_pow_eq,
    Matrix.mul_diagonal, ThreeCycleMatrix.leftFactor_apply]

/-- Identity casts between the two index presentations `ZMod 3` and `Fin 3`. -/
def asT (M : Mat) : TitsComplexMatrix := M
def asMat (M : TitsComplexMatrix) : Mat := M
def idx (i : Fin 3) : Index := i

@[simp] theorem idx_val (i : Fin 3) : (idx i).val = i.val := rfl
@[simp] theorem idx_zero : idx 0 = 0 := rfl
@[simp] theorem idx_one : idx 1 = 1 := rfl
@[simp] theorem idx_two : idx 2 = 2 := rfl

/-- `mono_apply` with `Fin 3` entry indices. -/
theorem mono_apply_fin (d : PhaseTriple) (a b : Index) (i j : Fin 3) :
    asT (monomialFamily d (a, b)) i j =
      (if idx i = idx j + b then ThreeCycleFourier.phaseEntry d.val b (idx j) else 0) *
        χ a ^ j.val :=
  mono_apply d a b i j

/-! ## Gauge data -/

/-- Left gauge factor `[[0,0,−A⁻¹],[0,B,0],[−1,0,0]]`. -/
def Lg (ξ : Fin 4 → ℂ) : TitsComplexMatrix := !![0, 0, -(ξ 0)⁻¹; 0, ξ 1, 0; -1, 0, 0]

/-- Right gauge factor `diag(−1, −B⁻¹, −A)`. -/
def Rg (ξ : Fin 4 → ℂ) : TitsComplexMatrix := Matrix.diagonal ![-1, -(ξ 1)⁻¹, -(ξ 0)]

/-- Hidden label `(group, s)` to monomial label `(clock, shift)`. -/
def sigma1 : Label ≃ Label where
  toFun p := if p.1 = 2 then (-p.2, 2) else (p.2, p.1)
  invFun p := if p.2 = 2 then (2, -p.1) else (p.2, p.1)
  left_inv := by intro p; revert p; decide
  right_inv := by intro p; revert p; decide

/-- The H1 unitary error basis read from the nine non-quartet frames. -/
def W1 (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Family := fun p =>
  asMat (Lg ξ * asT (monomialFamily (anchorTriple ξ hξ 1) (sigma1 p)) * Rg ξ)

theorem monoT_zero (d : PhaseTriple) (a : Index) :
    asT (monomialFamily d (a, 0)) = !![1, 0, 0; 0, χ a, 0; 0, 0, χ a ^ 2] := by
  ext i j
  rw [mono_apply_fin]
  fin_cases i <;> fin_cases j <;> simp (config := {decide := true}) [ThreeCycleFourier.phaseEntry]

theorem monoT_one (d : PhaseTriple) (a : Index) :
    asT (monomialFamily d (a, 1)) = !![0, 0, χ a ^ 2; 1, 0, 0; 0, χ a, 0] := by
  ext i j
  rw [mono_apply_fin]
  fin_cases i <;> fin_cases j <;> simp (config := {decide := true}) [ThreeCycleFourier.phaseEntry]

theorem monoT_two (d : PhaseTriple) (a : Index) :
    asT (monomialFamily d (a, 2)) =
      !![0, d.val 1 * χ a, 0; 0, 0, d.val 2 * χ a ^ 2; d.val 0, 0, 0] := by
  ext i j
  rw [mono_apply_fin]
  fin_cases i <;> fin_cases j <;> simp (config := {decide := true}) [ThreeCycleFourier.phaseEntry]

theorem W1_zero (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (s : Index) :
    asT (W1 ξ hξ (0, s)) = Lg ξ * !![1, 0, 0; 0, χ s, 0; 0, 0, χ s ^ 2] * Rg ξ := by
  rw [← monoT_zero (anchorTriple ξ hξ 1) s]
  rfl

theorem W1_one (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (s : Index) :
    asT (W1 ξ hξ (1, s)) = Lg ξ * !![0, 0, χ s ^ 2; 1, 0, 0; 0, χ s, 0] * Rg ξ := by
  rw [← monoT_one (anchorTriple ξ hξ 1) s]
  rfl

theorem W1_two (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (s : Index) :
    asT (W1 ξ hξ (2, s)) = Lg ξ *
      !![0, anchorPhases ξ 1 1 * χ (-s), 0; 0, 0, anchorPhases ξ 1 2 * χ (-s) ^ 2;
        anchorPhases ξ 1 0, 0, 0] * Rg ξ := by
  rw [show anchorPhases ξ 1 = (anchorTriple ξ hξ 1).val from rfl, ← monoT_two]
  rfl

/-! ## Original frames 1–3: phase projectors become complementary points -/

theorem phaseProjector_apply' (s t : PhaseIndex) (i j : Fin 3) :
    phaseProjector s t i j = (1 / 3) * (phaseRay s t i * star (phaseRay s t j)) := by
  rw [phaseProjector, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]

theorem phaseProjector_diag (s t : PhaseIndex) (i : Fin 3) : (phaseProjector s t i i).re = 1 / 3 := by
  rw [phaseProjector, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply, phaseRay_normSq]
  simp

theorem hidden_frames_A (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (s t : PhaseIndex) :
    transportTinv 0 (includeHermitianMatrix ⟨phaseProjector s (-t), phaseProjector_isHermitian _ _⟩) =
      nativeComplementaryPoint (χ t • W1 ξ hξ (0, s)) := by
  have hA : ξ 0 ≠ 0 := fun h => by simpa [h] using hξ 0
  have hB : ξ 1 ≠ 0 := fun h => by simpa [h] using hξ 1
  have hu := char_cube s
  have hv := char_cube t
  obtain ⟨u4, u5, u6, u7, u8, u9, u10, u11, u12⟩ := cube_pows hu
  obtain ⟨v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := cube_pows hv
  rw [transportTinv_zero_includeHermitianMatrix_third _ (phaseProjector_diag s (-t))]
  congr 1
  ext i j
  change _ = χ t * asT (W1 ξ hξ (0, s)) i j
  rw [W1_zero]
  simp only [phaseProjector_apply']
  fin_cases i <;> fin_cases j <;>
    simp [Lg, Rg, Matrix.mul_apply, Fin.sum_univ_three, phaseRay,
      char_add, char_neg, star_mul', star_pow, star_char] <;>
    cube_close

/-! ## Original frames 7–9 and 10–12 -/

theorem hidden_frames_B (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (s t : PhaseIndex) :
    transportTinv 0 (nativeComplementaryPoint (hiddenMatrix ξ 1 s (t - s))) =
      nativeComplementaryPoint (χ t • W1 ξ hξ (1, s)) := by
  have hA : ξ 0 ≠ 0 := fun h => by simpa [h] using hξ 0
  have hB : ξ 1 ≠ 0 := fun h => by simpa [h] using hξ 1
  have sA := star_eq_inv_of_normSq (hξ 0)
  have sB := star_eq_inv_of_normSq (hξ 1)
  have hu := char_cube s
  have hv := char_cube t
  obtain ⟨u4, u5, u6, u7, u8, u9, u10, u11, u12⟩ := cube_pows hu
  obtain ⟨v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := cube_pows hv
  rw [transportTinv_zero_complementary_hidden _ (by simp [hiddenMatrix,
      QuadraticCertificate.ExactCKMABFrames.ellNMatrix])
    (by simp [hiddenMatrix, QuadraticCertificate.ExactCKMABFrames.ellNMatrix])
    (by simp [hiddenMatrix, QuadraticCertificate.ExactCKMABFrames.ellNMatrix])]
  congr 1
  ext i j
  change _ = χ t * asT (W1 ξ hξ (1, s)) i j
  rw [W1_one]
  fin_cases i <;> fin_cases j <;>
    simp [tinvB, hiddenMatrix, QuadraticCertificate.ExactCKMABFrames.ellNMatrix, Lg, Rg,
      Matrix.mul_apply, Fin.sum_univ_three, char_sub, star_mul', star_pow,
      star_char, sA, sB] <;>
    cube_close

theorem hidden_frames_C (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (s t : PhaseIndex) :
    transportTinv 0 (nativeComplementaryPoint (hiddenMatrix ξ 2 s (s - t))) =
      nativeComplementaryPoint (χ t • W1 ξ hξ (2, s)) := by
  have hA : ξ 0 ≠ 0 := fun h => by simpa [h] using hξ 0
  have hB : ξ 1 ≠ 0 := fun h => by simpa [h] using hξ 1
  have hC : ξ 2 ≠ 0 := fun h => by simpa [h] using hξ 2
  have hD : ξ 3 ≠ 0 := fun h => by simpa [h] using hξ 3
  have sC := star_eq_inv_of_normSq (hξ 2)
  have sD := star_eq_inv_of_normSq (hξ 3)
  have hu := char_cube s
  have hv := char_cube t
  obtain ⟨u4, u5, u6, u7, u8, u9, u10, u11, u12⟩ := cube_pows hu
  obtain ⟨v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := cube_pows hv
  rw [transportTinv_zero_complementary_hidden _ (by simp [hiddenMatrix,
      QuadraticCertificate.ExactCKMCDFrames.njMatrix])
    (by simp [hiddenMatrix, QuadraticCertificate.ExactCKMCDFrames.njMatrix])
    (by simp [hiddenMatrix, QuadraticCertificate.ExactCKMCDFrames.njMatrix])]
  congr 1
  ext i j
  change _ = χ t * asT (W1 ξ hξ (2, s)) i j
  rw [W1_two]
  fin_cases i <;> fin_cases j <;>
    simp [tinvB, hiddenMatrix, QuadraticCertificate.ExactCKMCDFrames.njMatrix, Lg, Rg,
      anchorPhases, Matrix.mul_apply, Fin.sum_univ_three, char_add, char_sub, char_neg, star_mul',
      star_pow, star_char, sC, sD] <;>
    cube_close

/-! ## The gauge image is a unitary error basis of the accepted dimension -/

/-- A two-sided unitary gauge image (with determinant-one product) of a UEB is a UEB. -/
theorem ueb_of_gauge (U : Family) (hU : IsUnitaryErrorBasis U) (L R : Mat)
    (hL : L.conjTranspose * L = 1) (hR : R * R.conjTranspose = 1) (hdet : L.det * R.det = 1)
    (σ : Label ≃ Label) : IsUnitaryErrorBasis (fun p => L * U (σ p) * R) := by
  have hR' : R.conjTranspose * R = 1 := mul_eq_one_comm.mp hR
  refine ⟨fun p => ⟨?_, ?_⟩, fun p q hpq => ?_⟩
  · simp only [Matrix.conjTranspose_mul]
    calc R.conjTranspose * ((U (σ p)).conjTranspose * L.conjTranspose) * (L * U (σ p) * R)
        = R.conjTranspose * ((U (σ p)).conjTranspose * (L.conjTranspose * L) * U (σ p)) * R := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hL, Matrix.mul_one, (hU.1 (σ p)).1, Matrix.mul_one, hR']
  · rw [Matrix.det_mul, Matrix.det_mul, (hU.1 (σ p)).2, mul_one, hdet]
  · simp only [Matrix.conjTranspose_mul]
    rw [show R.conjTranspose * ((U (σ p)).conjTranspose * L.conjTranspose) * (L * U (σ q) * R) =
        R.conjTranspose * ((U (σ p)).conjTranspose * (L.conjTranspose * L) * U (σ q)) * R by
          simp only [Matrix.mul_assoc], hL, Matrix.mul_one, trace_conj_unitary R _ hR]
    exact hU.2 (σ p) (σ q) (σ.injective.ne hpq)

theorem Lg_unitary (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (Lg ξ).conjTranspose * Lg ξ = 1 := by
  have hA : ξ 0 ≠ 0 := fun h => by simpa [h] using hξ 0
  have hB : ξ 1 ≠ 0 := fun h => by simpa [h] using hξ 1
  have sA := star_eq_inv_of_normSq (hξ 0)
  have sB := star_eq_inv_of_normSq (hξ 1)
  have cA : (starRingEnd ℂ) (ξ 0) = (ξ 0)⁻¹ := sA
  have cB : (starRingEnd ℂ) (ξ 1) = (ξ 1)⁻¹ := sB
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Lg, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply, cA, cB, hA, hB]

theorem Rg_unitary (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Rg ξ * (Rg ξ).conjTranspose = 1 := by
  have hA : ξ 0 ≠ 0 := fun h => by simpa [h] using hξ 0
  have hB : ξ 1 ≠ 0 := fun h => by simpa [h] using hξ 1
  have sA := star_eq_inv_of_normSq (hξ 0)
  have sB := star_eq_inv_of_normSq (hξ 1)
  rw [Rg, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  fin_cases j <;> simp [sA, sB, hA, hB]

theorem Lg_Rg_det (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : (Lg ξ).det * (Rg ξ).det = 1 := by
  have hA : ξ 0 ≠ 0 := fun h => by simpa [h] using hξ 0
  have hB : ξ 1 ≠ 0 := fun h => by simpa [h] using hξ 1
  rw [Matrix.det_fin_three, Rg, Matrix.det_diagonal, Fin.prod_univ_three]
  simp [Lg]
  field_simp

theorem W1_eq (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (p : Label) :
    W1 ξ hξ p = (fun _ => (1 : ℂ)) p •
      (asMat (Lg ξ) * monomialFamily (anchorTriple ξ hξ 1) (sigma1 p) * asMat (Rg ξ)) := by
  rw [one_smul]
  rfl

theorem W1_ueb (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : IsUnitaryErrorBasis (W1 ξ hξ) := by
  have h := ueb_of_gauge (monomialFamily (anchorTriple ξ hξ 1))
    (ThreeCycleMatrix.monomial_family_is_unitary_error_basis _) (asMat (Lg ξ)) (asMat (Rg ξ))
    (Lg_unitary ξ hξ) (Rg_unitary ξ hξ) (Lg_Rg_det ξ hξ) sigma1
  convert h using 1
  funext p
  simpa using W1_eq ξ hξ p

theorem W1_finrank (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ (firstOrderSpace (W1 ξ hξ)) =
      18 + 2 * resonanceCount (anchorTriple ξ hξ 1) :=
  finrank_firstOrderSpace_of_gauge_monomial (anchorTriple ξ hξ 1) (W1 ξ hξ) (W1_ueb ξ hξ)
    (asMat (Lg ξ)) (asMat (Rg ξ)) (Lg_unitary ξ hξ) (Rg_unitary ξ hξ) (fun _ => 1)
    (fun _ => by simp) sigma1 (W1_eq ξ hξ)

end Anchor1

end CKM.NativeFirstOrder

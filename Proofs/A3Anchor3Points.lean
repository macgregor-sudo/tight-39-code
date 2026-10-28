module

public import A3Anchor3Tits
public import A3Family
public import A3Quartet

@[expose] public section

/-!
# Anchor H3: `T₃⁻¹` on the four kinds of literal points, at every unit phase

* frame 0 (coordinate projectors) stays visible: `g E_t gᴴ = E_t`;
* frames 1–3 (phase projectors) become `p(ω^a W(0,s))` at outcome `-a`;
* frames 4–6 (`hiddenMatrix ξ 0 s`) become `p(ω^a W(1,s))` at outcome `a`;
* frames 7–9 (`hiddenMatrix ξ 1 s`) become `p(ω^a W(2,s))` at outcome `-a`;
* frames 10–12 (`hiddenMatrix ξ 2 s`) become the conjugated quartet `g P(s, a) gᴴ` at outcome `-a`,
  with `g = diag(1, C⁻¹, -D)`.
-/

noncomputable section

namespace CKM.NativeFirstOrder

namespace Anchor3

open CompactAlbert NativePolynomial UnitaryErrorBases.ComplexQuartet

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega
local notation "χ" => UnitaryErrorBases.ThreeCycleFourier.character

theorem idx_cases (i : ZMod 3) : i = 0 ∨ i = 1 ∨ i = 2 :=
  (by decide : ∀ j : ZMod 3, j = 0 ∨ j = 1 ∨ j = 2) i

theorem omega_cube : ω ^ 3 = 1 := UnitaryErrorBases.ThreeCycleFourier.omega_cube

theorem normSq_omega : Complex.normSq ω = 1 := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  simp only [UnitaryErrorBases.ThreeCycleFourier.omega, Complex.normSq_apply, Complex.div_re,
    Complex.div_im]
  norm_num
  nlinarith [hs]

theorem star_omega : star ω = ω ^ 2 := by
  have h1 : star ω * ω = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, normSq_omega, Complex.ofReal_one]
  calc star ω = star ω * ω ^ 3 := by rw [omega_cube, mul_one]
    _ = (star ω * ω) * ω ^ 2 := by ring
    _ = ω ^ 2 := by rw [h1, one_mul]

theorem chi_val (r : ZMod 3) : χ r = if r = 0 then 1 else if r = 1 then ω else ω ^ 2 := by
  rcases idx_cases r with rfl | rfl | rfl
  · rfl
  · show ω ^ (1 : ZMod 3).val = ω
    rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]
  · rfl

theorem val_zero3 : (0 : ZMod 3).val = 0 := rfl
theorem val_one3 : (1 : ZMod 3).val = 1 := rfl
theorem val_two3 : (2 : ZMod 3).val = 2 := rfl

theorem omega_pow_reduce (n : ℕ) : ω ^ (n + 3) = ω ^ n := by
  rw [pow_add, omega_cube, mul_one]

theorem omega_pow_four : ω ^ 4 = ω := by rw [omega_pow_reduce 1, pow_one]
theorem omega_pow_five : ω ^ 5 = ω ^ 2 := omega_pow_reduce 2
theorem omega_pow_six : ω ^ 6 = 1 := by rw [omega_pow_reduce 3, omega_cube]
theorem omega_pow_seven : ω ^ 7 = ω := by rw [omega_pow_reduce 4, omega_pow_four]
theorem omega_pow_eight : ω ^ 8 = ω ^ 2 := by rw [omega_pow_reduce 5, omega_pow_five]
theorem omega_pow_nine : ω ^ 9 = 1 := by rw [omega_pow_reduce 6, omega_pow_six]
theorem omega_pow_ten : ω ^ 10 = ω := by rw [omega_pow_reduce 7, omega_pow_seven]

theorem star_eq_inv_of_unit (z : ℂ) (hz : Complex.normSq z = 1) : star z = z⁻¹ := by
  rw [Complex.inv_def, hz, inv_one, Complex.ofReal_one, mul_one]; rfl

theorem ne_zero_of_unit (z : ℂ) (hz : Complex.normSq z = 1) : z ≠ 0 := by
  intro h; rw [h, map_zero] at hz; exact zero_ne_one hz

/-! ## The data of anchor H3 -/

/-- The diagonal of `g = diag(1, C⁻¹, -D)`. -/
def gD (ξ : Fin 4 → ℂ) : Fin 3 → ℂ := ![1, (ξ 2)⁻¹, -ξ 3]

/-- The quartet conjugation `g = diag(1, C⁻¹, -D)`. -/
def g3 (ξ : Fin 4 → ℂ) : TitsComplexMatrix := Matrix.diagonal (gD ξ)

/-- The nine hidden representatives (`W(0,s)`, `W(1,s)`, `W(2,s)` from literal frames
`1 + s`, `4 + s`, `7 + s` at outcome zero). -/
def W3T (ξ : Fin 4 → ℂ) (l : UnitaryErrorBases.Label) : TitsComplexMatrix :=
  if l.1 = 0 then !![0, -star (χ l.2), 0; -χ l.2, 0, 0; 0, 0, -1]
  else if l.1 = 1 then !![-star (χ l.2), 0, 0; 0, 0, -χ l.2; 0, -1, 0]
  else !![0, 0, -(ξ 0 * ξ 1 * χ l.2); 0, star (ξ 1 * χ l.2), 0; star (ξ 0), 0, 0]

/-- The hidden family of anchor H3. -/
def W3 (ξ : Fin 4 → ℂ) : UnitaryErrorBases.Family := fun l => W3T ξ l

/-- The anchor H3 quartet `g · std · gᴴ`. -/
def q3 (ξ : Fin 4 → ℂ) (k : Fin 4) (t : Fin 3) : {a : TitsComplexMatrix // a.IsHermitian} :=
  ⟨g3 ξ * (stdQuartet k t).val * (g3 ξ).conjTranspose,
    Matrix.isHermitian_mul_mul_conjTranspose _ (stdQuartet k t).property⟩

theorem conj_diag_apply (v : Fin 3 → ℂ) (M : TitsComplexMatrix) (i j : Fin 3) :
    (Matrix.diagonal v * M * (Matrix.diagonal v).conjTranspose) i j = v i * M i j * star (v j) := by
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

theorem gD_mul_star (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 3) : gD ξ i * star (gD ξ i) = 1 := by
  have h2 := ne_zero_of_unit _ (hξ 2)
  have hs2 := star_eq_inv_of_unit _ (hξ 2)
  have hs3 := star_eq_inv_of_unit _ (hξ 3)
  have h3 := ne_zero_of_unit _ (hξ 3)
  fin_cases i <;> simp [gD, star_inv₀, hs2, hs3, h2, h3]

theorem g3_unitary (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : g3 ξ * (g3 ξ).conjTranspose = 1 := by
  rw [g3, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact gD_mul_star ξ hξ i

theorem g3_unitary' (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : (g3 ξ).conjTranspose * g3 ξ = 1 :=
  mul_eq_one_comm.mp (g3_unitary ξ hξ)

theorem q3_apply (ξ : Fin 4 → ℂ) (k : Fin 4) (t i j : Fin 3) :
    (q3 ξ k t).val i j = gD ξ i * (stdQuartet k t).val i j * star (gD ξ j) :=
  conj_diag_apply _ _ i j

theorem q3_diag (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (k : Fin 4) (t i : Fin 3) :
    (q3 ξ k t).val i i = (stdQuartet k t).val i i := by
  rw [q3_apply, mul_comm (gD ξ i), mul_assoc, gD_mul_star ξ hξ i, mul_one]

theorem q3_idem (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (k : Fin 4) (t : Fin 3) :
    (q3 ξ k t).val * (q3 ξ k t).val = (q3 ξ k t).val := by
  change g3 ξ * (stdQuartet k t).val * (g3 ξ).conjTranspose *
      (g3 ξ * (stdQuartet k t).val * (g3 ξ).conjTranspose) =
    g3 ξ * (stdQuartet k t).val * (g3 ξ).conjTranspose
  have h := g3_unitary' ξ hξ
  calc _ = g3 ξ * (stdQuartet k t).val * ((g3 ξ).conjTranspose * g3 ξ) * (stdQuartet k t).val *
        (g3 ξ).conjTranspose := by simp only [Matrix.mul_assoc]
    _ = g3 ξ * ((stdQuartet k t).val * (stdQuartet k t).val) * (g3 ξ).conjTranspose := by
        rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [stdQuartet_idem]

theorem chi_mul_star (r : ZMod 3) : χ r * star (χ r) = 1 := by
  rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  change (Complex.normSq (ω ^ r.val) : ℂ) = 1
  rw [map_pow, normSq_omega, one_pow, Complex.ofReal_one]

theorem conj_omega : (starRingEnd ℂ) ω = ω ^ 2 := star_omega

theorem chi_mul_conj (r : ZMod 3) : χ r * (starRingEnd ℂ) (χ r) = 1 := chi_mul_star r

theorem phaseProjector_apply (s t : PhaseIndex) (i j : Fin 3) :
    phaseProjector s t i j = 1 / 3 * (phaseRay s t i * star (phaseRay s t j)) := by
  rw [phaseProjector, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rfl

theorem phaseProjector_diag (s t : PhaseIndex) (i : Fin 3) : phaseProjector s t i i = 1 / 3 := by
  rw [phaseProjector, Matrix.smul_apply, Matrix.vecMulVec_apply]
  fin_cases i <;> simp [phaseRay, chi_mul_conj]

theorem nativeComplementaryPoint_eq (U : TitsComplexMatrix) :
    nativeComplementaryPoint U = fromTitsCoordinates ((fun _ => (1 / 3 : ℝ)), 0, (1 / 3 : ℂ) • U) := rfl

/-- Literal frames `4 + s` (outcome `a`). -/
theorem tinv_hidden0 (ξ : Fin 4 → ℂ) (s a : ZMod 3) :
    transportTinv 2 (nativeComplementaryPoint (hiddenMatrix ξ 0 s a)) =
      nativeComplementaryPoint ((ω ^ a.val) • W3T ξ (1, s)) := by
  rw [nativeComplementaryPoint_eq, transportTinv_two_fromTits, nativeComplementaryPoint_eq]
  congr 1
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext r
    fin_cases r <;>
      simp [tits3, hiddenMatrix, QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix]
  · ext r c
    rcases idx_cases s with rfl | rfl | rfl <;> rcases idx_cases a with rfl | rfl | rfl <;>
    fin_cases r <;> fin_cases c <;>
      simp +decide [tits3, hiddenMatrix, QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix,
        W3T, chi_val, star_omega, val_one3, val_two3] <;>
      (try ring_nf) <;>
      (try simp only [omega_cube, omega_pow_four, omega_pow_five, omega_pow_six,
        omega_pow_eight])

/-- Literal frame 0: the coordinate projectors stay visible. -/
theorem tinv_coord (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (t : Fin 3) :
    transportTinv 2 (includeHermitianMatrix (stdQuartet 0 t)) = includeHermitianMatrix (q3 ξ 0 t) := by
  rw [includeHermitianMatrix, transportTinv_two_fromTits, includeHermitianMatrix]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext r
    fin_cases r <;> simp [tits3, fromHermitianPair, q3_diag ξ hξ]
  · funext r
    fin_cases r <;> fin_cases t <;>
      simp [tits3, fromHermitianPair, q3_apply, stdQuartet, coordinateProjector]
  · ext r c
    fin_cases r <;> fin_cases c <;> fin_cases t <;>
      simp [tits3, fromHermitianPair, stdQuartet, coordinateProjector]

/-- Literal frames `1 + s` (outcome `-a`). -/
theorem tinv_phase (ξ : Fin 4 → ℂ) (s a : ZMod 3) (P : {m : TitsComplexMatrix // m.IsHermitian})
    (hP : P.val = phaseProjector s (-a)) :
    transportTinv 2 (includeHermitianMatrix P) =
      nativeComplementaryPoint ((ω ^ a.val) • W3T ξ (0, s)) := by
  rw [includeHermitianMatrix, transportTinv_two_fromTits, nativeComplementaryPoint_eq]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext r
    fin_cases r <;> simp [tits3, fromHermitianPair, hP, phaseProjector_diag]
  · funext r
    fin_cases r <;> simp [tits3, fromHermitianPair]
  · ext r c
    rcases idx_cases s with rfl | rfl | rfl <;> rcases idx_cases a with rfl | rfl | rfl <;>
    fin_cases r <;> fin_cases c <;>
      simp +decide [tits3, fromHermitianPair, hP, phaseProjector_apply, phaseRay,
        W3T, chi_val, star_omega, val_one3, val_two3] <;>
      (try ring_nf) <;>
      (try simp only [omega_cube, omega_pow_four, omega_pow_five, omega_pow_six])

/-- Literal frames `7 + s` (outcome `-a`). -/
theorem tinv_hidden1 (ξ : Fin 4 → ℂ) (s a : ZMod 3) :
    transportTinv 2 (nativeComplementaryPoint (hiddenMatrix ξ 1 s (-a))) =
      nativeComplementaryPoint ((ω ^ a.val) • W3T ξ (2, s)) := by
  rw [nativeComplementaryPoint_eq, transportTinv_two_fromTits, nativeComplementaryPoint_eq]
  congr 1
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext r
    fin_cases r <;>
      simp [tits3, hiddenMatrix, QuadraticCertificate.ExactCKMABFrames.ellNMatrix]
  · ext r c
    rcases idx_cases s with rfl | rfl | rfl <;> rcases idx_cases a with rfl | rfl | rfl <;>
    fin_cases r <;> fin_cases c <;>
      simp +decide [tits3, hiddenMatrix, QuadraticCertificate.ExactCKMABFrames.ellNMatrix,
        W3T, chi_val, star_omega, val_one3, val_two3] <;>
      (try ring_nf) <;>
      (try simp only [omega_cube, omega_pow_four, omega_pow_five, omega_pow_six]) <;> (try ring_nf)

/-- Literal frames `10 + s` (outcome `-a`): the conjugated quartet. -/
theorem tinv_hidden2 (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (s a : ZMod 3) (k : Fin 4)
    (hk : (stdQuartet k a).val = phaseProjector s a) :
    transportTinv 2 (nativeComplementaryPoint (hiddenMatrix ξ 2 s (-a))) =
      includeHermitianMatrix (q3 ξ k a) := by
  have hs2 := star_eq_inv_of_unit _ (hξ 2)
  have hs3 := star_eq_inv_of_unit _ (hξ 3)
  have h2 := ne_zero_of_unit _ (hξ 2)
  have h3 := ne_zero_of_unit _ (hξ 3)
  have hq : ∀ i j, (q3 ξ k a).val i j = gD ξ i * phaseProjector s a i j * star (gD ξ j) := by
    intro i j; exact (q3_apply ξ k a i j).trans (by rw [hk])
  rw [nativeComplementaryPoint_eq, transportTinv_two_fromTits, includeHermitianMatrix]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext r
    have hd : ∀ i, (q3 ξ k a).val i i = 1 / 3 := fun i => by
      exact (q3_diag ξ hξ k a i).trans ((congrFun (congrFun hk i) i).trans (phaseProjector_diag s a i))
    fin_cases r <;> simp [tits3, fromHermitianPair, hd]
  · funext r
    rw [show (fromHermitianPair (q3 ξ k a, 0)).2.1 r =
        ![(q3 ξ k a).val 1 2, (q3 ξ k a).val 2 0, (q3 ξ k a).val 0 1] r from rfl, hq, hq, hq]
    rcases idx_cases s with rfl | rfl | rfl <;> rcases idx_cases a with rfl | rfl | rfl <;>
    fin_cases r <;>
      simp +decide [tits3, hiddenMatrix, QuadraticCertificate.ExactCKMCDFrames.njMatrix, gD,
        phaseProjector_apply, phaseRay, chi_val, star_omega,
        hs2, hs3, star_inv₀] <;>
      (try field_simp) <;> (try ring_nf) <;>
      (try simp only [omega_cube, omega_pow_four, omega_pow_five, omega_pow_six,
        omega_pow_eight])
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [tits3, hiddenMatrix, QuadraticCertificate.ExactCKMCDFrames.njMatrix, fromHermitianPair]

end Anchor3

end CKM.NativeFirstOrder

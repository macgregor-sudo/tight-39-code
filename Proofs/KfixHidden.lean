module

public import A3Family
public import KfixR1

@[expose] public section

/-!
# KFIX helper: the nine hidden matrices of the literal family, in the anchor-0 picture

`kfW ξ l = hiddenMatrix ξ l.1 l.2 0`. Shapes are the three accepted monomial matrices; all identities
here hold at every unit phase (no resonance condition enters).
-/

noncomputable section

namespace CKM.NativeFirstOrder

open CompactAlbert UnitaryErrorBases.ComplexQuartet

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega
local notation "χ" => UnitaryErrorBases.ThreeCycleFourier.character

/-- The three monomial shapes. -/
def kfS : Fin 3 → ℂ → ℂ → TitsComplexMatrix
  | 0 => QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix
  | 1 => QuadraticCertificate.ExactCKMABFrames.ellNMatrix
  | 2 => QuadraticCertificate.ExactCKMCDFrames.njMatrix

/-- First-input phases per hidden group. -/
def kfa (ξ : Fin 4 → ℂ) : Fin 3 → ℂ := ![1, ξ 0, ξ 2]
/-- Second-input phases per hidden group. -/
def kfb (ξ : Fin 4 → ℂ) : Fin 3 → ℂ := ![1, ξ 1, ξ 3]

theorem kf_hidden_eq (ξ : Fin 4 → ℂ) (g : Fin 3) (s t : PhaseIndex) :
    hiddenMatrix ξ g s t = kfS g (kfa ξ g * χ t) (kfb ξ g * χ (s + t)) := by
  fin_cases g <;> simp [hiddenMatrix, kfS, kfa, kfb]

/-- The anchor-0 hidden matrices, typed as Tits matrices. -/
def kfWt (ξ : Fin 4 → ℂ) (l : UnitaryErrorBases.Label) : TitsComplexMatrix := hiddenMatrix ξ l.1 l.2 0

/-- The anchor-0 hidden family. -/
def kfW (ξ : Fin 4 → ℂ) : UnitaryErrorBases.Family := fun l => kfWt ξ l

/-- Index reinterpretation `ZMod 3 = Fin 3`. -/
def kfToFin (i : UnitaryErrorBases.Index) : Fin 3 := i

theorem kf_char_zero : χ 0 = 1 := by
  simp [UnitaryErrorBases.ThreeCycleFourier.character]

theorem kfWt_eq (ξ : Fin 4 → ℂ) (l : UnitaryErrorBases.Label) :
    kfWt ξ l = kfS (kfToFin l.1) (kfa ξ (kfToFin l.1)) (kfb ξ (kfToFin l.1) * χ l.2) := by
  have h := kf_hidden_eq ξ l.1 l.2 0
  simp only [kf_char_zero, mul_one, add_zero] at h
  exact h

/-! ## Generic shape identities -/

theorem kfS_scale (g : Fin 3) (z w u : ℂ) (hu : u ^ 2 = (starRingEnd ℂ) u) :
    kfS g (z * u) (w * u) = star u • kfS g z w := by
  ext i j
  fin_cases g <;> fin_cases i <;> fin_cases j <;>
    simp [kfS, QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix,
      QuadraticCertificate.ExactCKMABFrames.ellNMatrix, QuadraticCertificate.ExactCKMCDFrames.njMatrix] <;>
    ring_nf <;> rw [hu] <;> ring

theorem kfS_cov (g : Fin 3) (z w : ℂ) :
    kfS g z w = ω ^ (g : ℕ) • (kfG * kfS g z w * kfH.conjTranspose) := by
  rw [kf_GH_conj]
  ext i j
  fin_cases g <;> fin_cases i <;> fin_cases j <;>
    simp [kfS, kfGH, QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix,
      QuadraticCertificate.ExactCKMABFrames.ellNMatrix, QuadraticCertificate.ExactCKMCDFrames.njMatrix] <;>
    ring_nf <;> simp only [kf_omega_cube, one_mul, mul_one]

/-- Diagonal of the Gram product of two shapes, as a function of the shifted index `k - g`. -/
def kfDiag (z w z' w' : ℂ) : Fin 3 → ℂ := ![z * star z', w * star w', star (z * w) * (z' * w')]

theorem kfS_gram_diag (g g' : Fin 3) (z w z' w' : ℂ) (k : Fin 3) :
    ((kfS g z w).conjTranspose * kfS g' z' w') k k =
      if g = g' then kfDiag z w z' w' (k - g) else 0 := by
  fin_cases g <;> fin_cases g' <;> fin_cases k <;>
    simp [kfS, kfDiag, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply,
      QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix,
      QuadraticCertificate.ExactCKMABFrames.ellNMatrix, QuadraticCertificate.ExactCKMCDFrames.njMatrix]

theorem kf_star_inv (z : ℂ) (hz : star z * z = 1) : (starRingEnd ℂ) z = z⁻¹ :=
  eq_inv_of_mul_eq_one_left hz

theorem kf_ne_zero (z : ℂ) (hz : star z * z = 1) : z ≠ 0 := by
  rintro rfl
  simp at hz

theorem kfS_unitary (g : Fin 3) (z w : ℂ) (hz : star z * z = 1) (hw : star w * w = 1) :
    (kfS g z w).conjTranspose * kfS g z w = 1 := by
  have hz0 := kf_ne_zero z hz
  have hw0 := kf_ne_zero w hw
  ext i j
  fin_cases g <;> fin_cases i <;> fin_cases j <;>
    simp [kfS, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply, 
      QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix,
      QuadraticCertificate.ExactCKMABFrames.ellNMatrix, QuadraticCertificate.ExactCKMCDFrames.njMatrix,
      kf_star_inv z hz, kf_star_inv w hw, hz0, hw0] <;> field_simp

theorem kfS_det (g : Fin 3) (z w : ℂ) (hz : star z * z = 1) (hw : star w * w = 1) :
    (kfS g z w).det = 1 := by
  have hz0 := kf_ne_zero z hz
  have hw0 := kf_ne_zero w hw
  fin_cases g <;>
    simp [kfS, Matrix.det_fin_three,
      QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix,
      QuadraticCertificate.ExactCKMABFrames.ellNMatrix, QuadraticCertificate.ExactCKMCDFrames.njMatrix,
      kf_star_inv z hz, kf_star_inv w hw] <;> field_simp


/-! ## Characters -/

theorem kf_char_one : χ 1 = ω := by
  simp [UnitaryErrorBases.ThreeCycleFourier.character, ZMod.val_one]

theorem kf_char_two : χ 2 = ω ^ 2 := by
  rw [UnitaryErrorBases.ThreeCycleFourier.character]
  rfl

theorem kf_omega_star_mul : star ω * ω = 1 := by
  rw [kf_star_omega, ← pow_succ, kf_omega_cube]

theorem kf_omega_sq_star_mul : star (ω ^ 2) * ω ^ 2 = 1 := by
  rw [star_pow, kf_star_omega, ← pow_mul, ← pow_add, show 2 * 2 + 2 = 3 * 2 by rfl, pow_mul,
    kf_omega_cube, one_pow]

theorem kf_idx_cases (t : UnitaryErrorBases.Index) : t = 0 ∨ t = 1 ∨ t = 2 := by
  revert t; decide

theorem kf_char_zero' : χ 0 = 1 := kf_char_zero

theorem kf_char_star_mul (t : UnitaryErrorBases.Index) : star (χ t) * χ t = 1 := by
  rcases kf_idx_cases t with rfl | rfl | rfl
  · rw [kf_char_zero, star_one, one_mul]
  · rw [kf_char_one]; exact kf_omega_star_mul
  · rw [kf_char_two]; exact kf_omega_sq_star_mul

theorem kf_char_neg (t : UnitaryErrorBases.Index) : star (χ (-t)) = χ t ∧ χ (-t) ^ 2 = star (χ (-t)) := by
  rcases kf_idx_cases t with rfl | rfl | rfl
  · rw [neg_zero, kf_char_zero, star_one, one_pow]; exact ⟨rfl, rfl⟩
  · rw [show -(1 : UnitaryErrorBases.Index) = 2 by decide, kf_char_two, kf_char_one, star_pow,
      kf_star_omega, ← pow_mul, show (2 * 2 : ℕ) = 4 by rfl, kf_omega_four]
    exact ⟨rfl, rfl⟩
  · rw [show -(2 : UnitaryErrorBases.Index) = 1 by decide, kf_char_two, kf_char_one, kf_star_omega]
    exact ⟨rfl, rfl⟩

theorem kf_char_add (s t : UnitaryErrorBases.Index) : χ (s + t) = χ s * χ t :=
  QuadraticCertificate.ExactCKMThreeHiddenFrames.character_add s t

/-- Outcome structure: `hiddenMatrix ξ g s (-t) = ω^t • hiddenMatrix ξ g s 0`. -/
theorem kf_hidden_neg (ξ : Fin 4 → ℂ) (g : Fin 3) (s t : PhaseIndex) :
    hiddenMatrix ξ g s (-t) = χ t • hiddenMatrix ξ g s 0 := by
  rw [kf_hidden_eq, kf_hidden_eq, kf_char_add, kf_char_zero, mul_one, add_zero,
    show kfb ξ g * (χ s * χ (-t)) = (kfb ξ g * χ s) * χ (-t) by ring,
    kfS_scale g _ _ _ (by rw [(kf_char_neg t).2]; rfl), (kf_char_neg t).1]

/-- `R1` covariance of the hidden family. -/
theorem kfW_cov (ξ : Fin 4 → ℂ) (l : UnitaryErrorBases.Label) :
    kfWt ξ l =
      ω ^ (l.1).val • (kfG * kfWt ξ l * kfH.conjTranspose) := by
  rw [kfWt_eq]
  exact kfS_cov _ _ _

theorem kf_unit_of_normSq (z : ℂ) (hz : Complex.normSq z = 1) : star z * z = 1 :=
  star_mul_self_of_normSq z hz

theorem kfa_unit (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (g : Fin 3) : star (kfa ξ g) * kfa ξ g = 1 := by
  fin_cases g
  · simp [kfa]
  · exact kf_unit_of_normSq _ (hξ 0)
  · exact kf_unit_of_normSq _ (hξ 2)

theorem kfb_unit (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (g : Fin 3) : star (kfb ξ g) * kfb ξ g = 1 := by
  fin_cases g
  · simp [kfb]
  · exact kf_unit_of_normSq _ (hξ 1)
  · exact kf_unit_of_normSq _ (hξ 3)

theorem kf_mul_unit (z w : ℂ) (hz : star z * z = 1) (hw : star w * w = 1) : star (z * w) * (z * w) = 1 := by
  rw [star_mul', show star z * star w * (z * w) = (star z * z) * (star w * w) by ring, hz, hw, one_mul]

theorem kfW_unitary (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (l : UnitaryErrorBases.Label) :
    (kfWt ξ l).conjTranspose * kfWt ξ l = 1 := by
  rw [kfWt_eq]
  exact kfS_unitary _ _ _ (kfa_unit ξ hξ _) (kf_mul_unit _ _ (kfb_unit ξ hξ _) (kf_char_star_mul _))

theorem kfW_det (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (l : UnitaryErrorBases.Label) :
    (kfWt ξ l).det = 1 := by
  rw [kfWt_eq]
  exact kfS_det _ _ _ (kfa_unit ξ hξ _) (kf_mul_unit _ _ (kfb_unit ξ hξ _) (kf_char_star_mul _))

/-- The diagonal Gram pattern of the hidden family. -/
def kfPat (s s' : UnitaryErrorBases.Index) : Fin 3 → ℂ :=
  ![1, χ s * star (χ s'), star (χ s) * χ s']

theorem kfW_gram_diag (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (p q : UnitaryErrorBases.Label) (k : Fin 3) :
    ((kfWt ξ p).conjTranspose * kfWt ξ q) k k =
      if p.1 = q.1 then kfPat p.2 q.2 (k - kfToFin p.1) else 0 := by
  rw [kfWt_eq, kfWt_eq, kfS_gram_diag]
  by_cases h : p.1 = q.1
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (show kfToFin p.1 = kfToFin q.1 from h))]
    have ha := kfa_unit ξ hξ (kfToFin p.1)
    have hb := kfb_unit ξ hξ (kfToFin p.1)
    rw [show kfToFin q.1 = kfToFin p.1 from h.symm]
    generalize k - kfToFin p.1 = m
    fin_cases m
    · simp [kfDiag, kfPat]
      rw [mul_comm]; exact ha
    · simp only [kfDiag, kfPat, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, star_mul']
      rw [show kfb ξ (kfToFin p.1) * χ p.2 * (star (kfb ξ (kfToFin p.1)) * star (χ q.2)) =
        (star (kfb ξ (kfToFin p.1)) * kfb ξ (kfToFin p.1)) * (χ p.2 * star (χ q.2)) by ring, hb, one_mul]
    · simp only [kfDiag, kfPat, Fin.reduceFinMk, Matrix.cons_val_two, 
        Matrix.tail_cons, star_mul']
      rw [show star (kfa ξ (kfToFin p.1)) * (star (kfb ξ (kfToFin p.1)) * star (χ p.2)) *
          (kfa ξ (kfToFin p.1) * (kfb ξ (kfToFin p.1) * χ q.2)) =
        (star (kfa ξ (kfToFin p.1)) * kfa ξ (kfToFin p.1)) * (star (kfb ξ (kfToFin p.1)) * kfb ξ (kfToFin p.1)) * (star (χ p.2) * χ q.2) by ring,
        ha, hb, one_mul, one_mul]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
      ite_eq_right_of_eq_false _ _ (eq_false (show ¬ kfToFin p.1 = kfToFin q.1 from h))]

end CKM.NativeFirstOrder

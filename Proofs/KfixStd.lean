module

public import A3Elimination
public import A3Quartet
public import A3Automorphisms
public import A3Action
public import KfixSixDim

@[expose] public section

/-!
# KFIX helper: the jointly fixed space in the standard anchor-0 picture

On `stdAnchored stdQuartet (kfW ξ)`, the second generator `R1` acts with the shift `kfShift1`
(frame 0: 0; frames 1–3: 1; 4–6: 0; 7–9: 1; 10–12: 2). Through `elimForward`, the space fixed by both
compensated generators is the product of `quartetClockFixed` and `kfS6 ξ`.
-/

noncomputable section

namespace CKM.NativeFirstOrder

open NativePolynomial NativePolynomial.ConfigurationResiduals CompactAlbert
open UnitaryErrorBases.ComplexQuartet

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega
local notation "χ" => UnitaryErrorBases.ThreeCycleFourier.character

/-- Outcome shift of `R1` in the outcome-negated anchor-0 picture. -/
def kfShift1 (f : Fin 13) : Fin 3 :=
  if f.val = 0 then 0 else if f.val < 4 then 1 else if f.val < 7 then 0 else if f.val < 10 then 1 else 2

theorem kfG_eq_clockInv : kfG = clockInv := rfl

theorem kf_elim_fst (x : Fin 39 → Glennie.Albert) (k : Fin 4) (t : Fin 3) :
    (elimForward x).1 k t =
      (nativeTitsMatrixPair (x (framePointIndex (Fin.castLE (by omega) k) t))).1 := rfl

theorem kf_elim_snd (x : Fin 39 → Glennie.Albert) (l : UnitaryErrorBases.Label) :
    kfT ((elimForward x).2 l) =
      (3 : ℝ) • (nativeTitsMatrixPair (x (framePointIndex (hiddenFrame l) 0))).2 := rfl

theorem kf_shift_visible (k : Fin 4) :
    kfShift1 (Fin.castLE (by omega) k) = if k = 0 then 0 else 1 := by
  fin_cases k <;> rfl

theorem kf_shift_hidden (l : UnitaryErrorBases.Label) : kfShift1 (hiddenFrame l) = kfToFin l.1 := by
  obtain ⟨g, s⟩ := l
  fin_cases g <;> fin_cases s <;> rfl

theorem kf_hiddenFrame_ge (l : UnitaryErrorBases.Label) : 4 ≤ (hiddenFrame l).val := by
  simp [hiddenFrame]

theorem kf_shift_apply (σ : Fin 13 → Fin 3) (f : Fin 13) (a : Fin 3) :
    outcomeShift σ (framePointIndex f a) = framePointIndex f (a + σ f) := by
  rw [outcomeShift, pointRelabel_framePointIndex]
  rfl

theorem kf_R0_pair (y : Glennie.Albert) :
    nativeTitsMatrixPair (R0 y) = ((nativeTitsMatrixPair y).1, ω • (nativeTitsMatrixPair y).2) := by
  rw [show R0 y = nativeRightMultiply (ω • (1 : TitsComplexMatrix)) y from rfl, nativeRightMultiply_pair,
    Matrix.mul_smul, Matrix.mul_one]

/-- `R0`-fixed variations rotate their hidden parts by `ω^a` along each hidden frame. -/
theorem kf_fix0_hidden {δ : Fin 39 → Glennie.Albert} (hδ : δ ∈ fixedSpace (compensated R0 stdShift))
    (f : Fin 13) (hf : 4 ≤ f.val) (a : Fin 3) :
    (nativeTitsMatrixPair (δ (framePointIndex f a))).2 =
      ω ^ a.val • (nativeTitsMatrixPair (δ (framePointIndex f 0))).2 := by
  rw [mem_fixedSpace] at hδ
  have hrot : ∀ b : Fin 3, (nativeTitsMatrixPair (δ (framePointIndex f b))).2 =
      ω • (nativeTitsMatrixPair (δ (framePointIndex f (b + 2)))).2 := by
    intro b
    have h := congrFun hδ (framePointIndex f b)
    rw [compensated_apply, stdShift, kf_shift_apply, ite_eq_right (by omega)] at h
    rw [← h, kf_R0_pair]
  rcases (by decide : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2) a with rfl | rfl | rfl
  · rw [show (0 : Fin 3).val = 0 from rfl, pow_zero, one_smul]
  · rw [hrot 1, show (1 : Fin 3) + 2 = 0 from rfl, show (1 : Fin 3).val = 1 from rfl, pow_one]
  · rw [hrot 2, show (2 : Fin 3) + 2 = 1 from rfl, hrot 1, show (1 : Fin 3) + 2 = 0 from rfl,
      smul_smul, show (2 : Fin 3).val = 2 from rfl, pow_two]

/-- `R1` in elimination coordinates: quartet part. -/
theorem kf_elim_R1_fst (δ : Fin 39 → Glennie.Albert) (k : Fin 4) (t : Fin 3) :
    (elimForward (compensated R1 (outcomeShift kfShift1) δ)).1 k t =
      kfG * (elimForward δ).1 k (t + if k = 0 then 0 else 1) * kfG.conjTranspose := by
  rw [kf_elim_fst, compensated_apply, kf_shift_apply, kf_pair_R1, kf_shift_visible, kf_elim_fst]

/-- `R1` in elimination coordinates: hidden part, for `R0`-fixed variations. -/
theorem kf_elim_R1_snd {δ : Fin 39 → Glennie.Albert} (hδ : δ ∈ fixedSpace (compensated R0 stdShift))
    (l : UnitaryErrorBases.Label) :
    kfT ((elimForward (compensated R1 (outcomeShift kfShift1) δ)).2 l) =
      ω ^ (l.1).val • (kfG * kfT ((elimForward δ).2 l) * kfH.conjTranspose) := by
  rw [kf_elim_snd, compensated_apply, kf_shift_apply, kf_pair_R1, zero_add, kf_shift_hidden,
    kf_fix0_hidden hδ _ (kf_hiddenFrame_ge l), kf_elim_snd]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_comm]
  rfl


/-! ## Standard anchored points -/

theorem kf_std_visible (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : UnitaryErrorBases.Family) (f : Fin 13) (hf : f.val < 4) (a : Fin 3) :
    stdAnchored q W (framePointIndex f a) = includeHermitianMatrix (q ⟨f.val, hf⟩ a) := by
  have h0 : (framePointIndex f a).val < 12 := by rw [framePointIndex_val]; omega
  unfold stdAnchored
  rw [dite_eq_left h0]
  congr 2
  · apply Fin.ext; simp only [framePointIndex_val]; omega
  · apply Fin.ext; simp only [framePointIndex_val]; omega

theorem kf_std_hidden (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : UnitaryErrorBases.Family) (l : UnitaryErrorBases.Label) (a : Fin 3) :
    stdAnchored q W (framePointIndex (hiddenFrame l) a) =
      nativeComplementaryPoint (ω ^ a.val • W l) := by
  have hl := (hiddenFrameEquiv l).isLt
  have h0 : ¬ (framePointIndex (hiddenFrame l) a).val < 12 := by
    rw [framePointIndex_val]; simp only [hiddenFrame]; omega
  have h1 : (framePointIndex (hiddenFrame l) a).val % 3 = a.val := by
    rw [framePointIndex_val]; simp only [hiddenFrame]; omega
  have h2 : hiddenFrameEquiv.symm ⟨(framePointIndex (hiddenFrame l) a).val / 3 - 4, by
      rw [framePointIndex_val]; simp only [hiddenFrame]; omega⟩ = l := by
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    simp only [framePointIndex_val, hiddenFrame]
    omega
  unfold stdAnchored
  rw [dite_eq_right h0]
  simp only [h1, h2]

theorem kf_exists_hidden (f : Fin 13) (hf : 4 ≤ f.val) : ∃ l, hiddenFrame l = f := by
  refine ⟨hiddenFrameEquiv.symm ⟨f.val - 4, by omega⟩, ?_⟩
  apply Fin.ext
  simp only [hiddenFrame, Equiv.apply_symm_apply]
  omega

theorem kf_exists_visible (f : Fin 13) (hf : f.val < 4) : ∃ k : Fin 4, Fin.castLE (by omega) k = f :=
  ⟨⟨f.val, hf⟩, Fin.ext rfl⟩

theorem kf_index_split (i : Fin 39) : ∃ f a, i = framePointIndex f a :=
  ⟨⟨i.val / 3, by omega⟩, ⟨i.val % 3, by omega⟩, by
    apply Fin.ext; rw [framePointIndex_val]; show i.val = 3 * (i.val / 3) + i.val % 3; omega⟩

/-! ## Clock covariance of the standard quartet -/

/-- The diagonal of `g`. -/
def kfgv : Fin 3 → ℂ := ![1, ω ^ 2, ω]

theorem kf_G_entry (M : TitsComplexMatrix) (i j : Fin 3) :
    (kfG * M * kfG.conjTranspose) i j = kfgv i * M i j * star (kfgv j) := by
  rw [kfG, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

theorem kf_ray_cov (s t : PhaseIndex) (i : Fin 3) :
    kfgv i * phaseRay s (t + 1) i = phaseRay s t i := by
  fin_cases i
  · simp [kfgv, phaseRay]
  · show ω ^ 2 * χ (t + 1) = χ t
    rw [kf_char_add, kf_char_one,
      show ω ^ 2 * (χ t * ω) = χ t * ω ^ 3 by ring, kf_omega_cube, mul_one]
  · show ω * χ (s - (t + 1)) = χ (s - t)
    rw [show s - (t + 1) = (s - t) + 2 by
        rw [show (2 : PhaseIndex) = -1 by decide]; ring,
      kf_char_add, kf_char_two,
      show ω * (χ (s - t) * ω ^ 2) = χ (s - t) * ω ^ 3 by ring, kf_omega_cube, mul_one]

theorem kf_phaseProjector_apply (s t : PhaseIndex) (i j : Fin 3) :
    phaseProjector s t i j = (1 / 3 : ℂ) * (phaseRay s t i * star (phaseRay s t j)) := by
  simp [phaseProjector, Matrix.vecMulVec_apply]

theorem kf_phase_cov (s t : PhaseIndex) :
    kfG * phaseProjector s (t + 1) * kfG.conjTranspose = phaseProjector s t := by
  ext i j
  rw [kf_G_entry, kf_phaseProjector_apply, kf_phaseProjector_apply, ← kf_ray_cov s t i,
    ← kf_ray_cov s t j, star_mul']
  ring

theorem kf_coord_cov (t : Fin 3) :
    kfG * coordinateProjector t * kfG.conjTranspose = coordinateProjector t := by
  ext i j
  rw [kf_G_entry, coordinateProjector, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, mul_comm, ← mul_assoc]
    have : star (kfgv i) * kfgv i = 1 := by
      fin_cases i
      · simp [kfgv]
      · exact kf_omega_sq_star_mul
      · exact kf_omega_star_mul
    rw [this, one_mul]
  · rw [ite_eq_right hij, mul_zero, zero_mul]

theorem kf_quartet_cov (k : Fin 4) (t : Fin 3) :
    kfG * (stdQuartet k (t + if k = 0 then 0 else 1)).val * kfG.conjTranspose = (stdQuartet k t).val := by
  rcases (by decide : ∀ k : Fin 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) k with rfl | rfl | rfl | rfl
  · rw [ite_eq_left rfl, add_zero]
    exact kf_coord_cov t
  · rw [ite_eq_right (by decide)]
    exact kf_phase_cov ((0 : ℕ) : PhaseIndex) t
  · rw [ite_eq_right (by decide)]
    exact kf_phase_cov ((1 : ℕ) : PhaseIndex) t
  · rw [ite_eq_right (by decide)]
    exact kf_phase_cov ((2 : ℕ) : PhaseIndex) t

end CKM.NativeFirstOrder

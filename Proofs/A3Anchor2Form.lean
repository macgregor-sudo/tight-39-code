module

public import A3Anchor2Gauge
public import A3Family
public import A3Quartet
public import A3Action

@[expose] public section

/-!
# Anchor H2: relabelling, quartet and the all-phase standard form of `T₂⁻¹ ∘ P(ξ)`

* `fperm2`: standard frame ↦ literal frame `[0,7,9,8,1,10,4,3,12,5,2,11,6]`; `τ2`: negation on the
  standard frames 5, 8, 11 (literal frames 10–12), identity elsewhere.
* `q2 ξ k t = g · stdQuartet k t · gᴴ`, `g = diag(1, A, B⁻¹)`.
* `anchor2_form`: `T₂⁻¹ (P(ξ) (λ i)) = stdAnchored (q2 ξ) (anchor2W ξ hξ) i` for all 39 labels.
-/

noncomputable section

namespace CKM.NativeFirstOrder

namespace Anchor2

open UnitaryErrorBases NativePolynomial NativePolynomial.ConfigurationResiduals
open CompactAlbert UnitaryErrorBases.ComplexQuartet

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega
local notation "χ" => UnitaryErrorBases.ThreeCycleFourier.character

/-! ## Relabelling and shift compatibility -/

/-- Standard frame ↦ literal frame. -/
def fperm2 : Equiv.Perm (Fin 13) where
  toFun := ![0, 7, 9, 8, 1, 10, 4, 3, 12, 5, 2, 11, 6]
  invFun := ![0, 4, 10, 7, 6, 9, 12, 1, 3, 2, 5, 11, 8]
  left_inv := by decide
  right_inv := by decide

/-- Outcome relabelling: negation on standard frames 5, 8, 11 (literal frames 10–12). -/
def τ2 (f : Fin 13) : Equiv.Perm (Fin 3) :=
  if f.val = 5 ∨ f.val = 8 ∨ f.val = 11 then Equiv.neg (Fin 3) else Equiv.refl _

theorem anchor2_shift_compat (i : Fin 39) :
    outcomeShift (anchorShift 2) (pointRelabel fperm2 τ2 i) = pointRelabel fperm2 τ2 (stdShift i) := by
  revert i
  decide

/-! ## The quartet -/

/-- The phase-dependent diagonal unitary `g = diag(1, A, B⁻¹)`. -/
def g2 (ξ : Fin 4 → ℂ) : TitsComplexMatrix := Matrix.diagonal ![1, ξ 0, (ξ 1)⁻¹]

theorem g2_unitary (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : g2 ξ * (g2 ξ).conjTranspose = 1 := by
  have hstar : ∀ k, (starRingEnd ℂ) (ξ k) = (ξ k)⁻¹ := fun k => Anchor0.star_eq_inv_of_unit _ (hξ k)
  have h0 := Anchor0.ne_zero_of_unit _ (hξ 0)
  have h1 := Anchor0.ne_zero_of_unit _ (hξ 1)
  rw [g2, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [hstar, h0, h1]

theorem g2_unitary' (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : (g2 ξ).conjTranspose * g2 ξ = 1 :=
  mul_eq_one_comm.mp (g2_unitary ξ hξ)

/-- The anchored quartet `g · stdQuartet · gᴴ`. -/
def q2 (ξ : Fin 4 → ℂ) (k : Fin 4) (t : Fin 3) : {a : TitsComplexMatrix // a.IsHermitian} :=
  ⟨g2 ξ * (stdQuartet k t).val * (g2 ξ).conjTranspose,
    Matrix.isHermitian_mul_mul_conjTranspose _ (stdQuartet k t).property⟩

theorem q2_idem (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (k : Fin 4) (t : Fin 3) :
    (q2 ξ k t).val * (q2 ξ k t).val = (q2 ξ k t).val := by
  change g2 ξ * (stdQuartet k t).val * (g2 ξ).conjTranspose *
      (g2 ξ * (stdQuartet k t).val * (g2 ξ).conjTranspose) =
    g2 ξ * (stdQuartet k t).val * (g2 ξ).conjTranspose
  rw [show g2 ξ * (stdQuartet k t).val * (g2 ξ).conjTranspose *
      (g2 ξ * (stdQuartet k t).val * (g2 ξ).conjTranspose) =
      g2 ξ * ((stdQuartet k t).val * ((g2 ξ).conjTranspose * g2 ξ) * (stdQuartet k t).val) *
        (g2 ξ).conjTranspose by simp only [Matrix.mul_assoc],
    g2_unitary' ξ hξ, Matrix.mul_one, stdQuartet_idem]

theorem q2_finrank (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ (quartetFirstOrder fun k t => (q2 ξ k t).val) = 8 :=
  (finrank_quartetFirstOrder_conj (fun k t => (stdQuartet k t).val) (g2 ξ) (g2_unitary ξ hξ)
    (Equiv.refl _) (fun _ => Equiv.refl _)).trans finrank_quartetFirstOrder_std

/-- Conjugating a rank-one matrix by a diagonal matrix. -/
theorem diagonal_conj_rankOne (v u : Fin 3 → ℂ) :
    Matrix.diagonal v * ((1 / 3 : ℂ) • Matrix.vecMulVec u (star u)) * (Matrix.diagonal v).conjTranspose =
      (1 / 3 : ℂ) • Matrix.vecMulVec (fun i => v i * u i) (star fun i => v i * u i) := by
  ext i j
  simp only [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, Pi.star_apply, star_mul']
  ring

/-- The anchored quartet in frames 1–3 is the rank-one projector of `(1, A χ t, conj (B χ(−s' + t)))`. -/
theorem g2_phaseProjector (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (s' t : PhaseIndex) :
    g2 ξ * phaseProjector s' t * (g2 ξ).conjTranspose =
      (1 / 3 : ℂ) • Matrix.vecMulVec ![1, ξ 0 * χ t, star (ξ 1 * χ (-s' + t))]
        (star ![1, ξ 0 * χ t, star (ξ 1 * χ (-s' + t))]) := by
  rw [g2, phaseProjector, diagonal_conj_rankOne]
  congr 3 <;>
  · funext i
    fin_cases i <;>
      simp [phaseRay, star_mul', Anchor0.star_chi, Anchor0.star_eq_inv_of_unit _ (hξ 1), sub_eq_add_neg,
        add_comm]

/-! ## The standard anchored form at frame/outcome labels -/

theorem stdA_visible (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : UnitaryErrorBases.Family) (k : Fin 4) (a : Fin 3) :
    stdAnchored q W (framePointIndex (Fin.castLE (by omega) k) a) = includeHermitianMatrix (q k a) := by
  have h12 : (framePointIndex (Fin.castLE (by omega) k) a).val < 12 := by
    simp [framePointIndex]; omega
  rw [stdAnchored]
  simp only [h12, ↓reduceDIte]
  congr 2 <;> ext <;> simp only [framePointIndex, Fin.val_castLE] <;> omega

theorem stdA_hidden (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : UnitaryErrorBases.Family) (l : Label) (a : Fin 3) :
    stdAnchored q W (framePointIndex (hiddenFrame l) a) =
      nativeComplementaryPoint ((UnitaryErrorBases.ThreeCycleFourier.omega ^ a.val) • W l) := by
  have hl : (hiddenFrame l).val = 4 + (Fin.val (n := 3) l.2 + 3 * Fin.val (n := 3) l.1) := rfl
  have h12 : ¬ (framePointIndex (hiddenFrame l) a).val < 12 := by
    rw [framePointIndex_val, hl]; omega
  have hmod : (framePointIndex (hiddenFrame l) a).val % 3 = a.val := by
    rw [framePointIndex_val, hl]; omega
  have hlab : hiddenFrameEquiv.symm
      ⟨(framePointIndex (hiddenFrame l) a).val / 3 - 4, by
        have := (framePointIndex (hiddenFrame l) a).isLt; omega⟩ = l := by
    rw [Equiv.symm_apply_eq]
    ext
    have hfe : (hiddenFrameEquiv l).val = Fin.val (n := 3) l.2 + 3 * Fin.val (n := 3) l.1 := rfl
    show (framePointIndex (hiddenFrame l) a).val / 3 - 4 = (hiddenFrameEquiv l).val
    rw [framePointIndex_val, hl, hfe]; omega
  rw [stdAnchored]
  simp only [h12, ↓reduceDIte]
  rw [hmod, hlab]

/-! ## The images of the 39 literal points -/

/-- Literal frame 0 (coordinate idempotents) is fixed. -/
theorem pt0 (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (a : Fin 3) :
    transportTinv 1 (literalPoint ξ (framePointIndex (Fin.castLE (by omega) (0 : Fin 4)) a)) =
      includeHermitianMatrix (q2 ξ 0 a) := by
  have hstar : ∀ k, (starRingEnd ℂ) (ξ k) = (ξ k)⁻¹ := fun k => Anchor0.star_eq_inv_of_unit _ (hξ k)
  have h0 := Anchor0.ne_zero_of_unit _ (hξ 0)
  have h1 := Anchor0.ne_zero_of_unit _ (hξ 1)
  rw [literalPoint_quartet, transportTinv_one_diagonal]
  · congr 1
    apply Subtype.ext
    change coordinateProjector a = g2 ξ * coordinateProjector a * (g2 ξ).conjTranspose
    rw [g2, coordinateProjector, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> fin_cases a <;> simp [hstar, h0, h1]
  all_goals change coordinateProjector a _ _ = 0; simp [coordinateProjector]

/-- Literal frames `7 + s` (A/B group) become the anchored quartet. -/
theorem ptQ (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (s' : PhaseIndex) (a : Fin 3)
    (P : {m : TitsComplexMatrix // m.IsHermitian})
    (hP : P.val = g2 ξ * phaseProjector s' a * (g2 ξ).conjTranspose) :
    transportTinv 1 (literalPoint ξ (framePointIndex ⟨4 + 3 * (1 : Fin 3).val + (-s').val, by
        have := ZMod.val_lt (-s'); omega⟩ a)) = includeHermitianMatrix P := by
  rw [literalPoint_hidden ξ hξ 1 (-s') a]
  have hu : ∀ k r, Complex.normSq (ξ k * χ r) = 1 := fun k r =>
    Anchor0.normSq_mul_unit _ _ (hξ k) (Anchor0.normSq_chi r)
  exact transportTinv_one_ell P _ _ (hu 0 a) (hu 1 _) (hP.trans (g2_phaseProjector ξ hξ s' a))

/-- Literal frames `1 + s` (phase projectors) become hidden points with label `(a, 0)`, `s = −a`. -/
theorem ptA (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (a : Index) (t : Fin 3) :
    transportTinv 1 (literalPoint ξ (framePointIndex (Fin.castLE (by omega)
        (⟨(-a).val + 1, by have := ZMod.val_lt (-a); omega⟩ : Fin 4)) t)) =
      nativeComplementaryPoint ((UnitaryErrorBases.ThreeCycleFourier.omega ^ t.val) •
        anchor2W ξ hξ (a, 0)) := by
  rw [literalPoint_quartet]
  rw [transportTinv_one_rankOne _ (χ t) (χ (-a - (show ZMod 3 from t))) (Anchor0.normSq_chi _) (Anchor0.normSq_chi _)]
  · congr 1
    ext i j
    have h := famA ξ hξ (-a) t i j
    rw [neg_neg] at h
    exact h
  · change phaseProjector (((-a).val : ℕ) : PhaseIndex) t = _
    rw [ZMod.natCast_zmod_val]
    rfl

/-- Literal frames `4 + s` (group-0 hidden matrices): label `(s, 2)`. -/
theorem ptB (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (a : Index) (t : Fin 3) :
    transportTinv 1 (literalPoint ξ (framePointIndex ⟨4 + 3 * (0 : Fin 3).val + a.val, by
        have := ZMod.val_lt a; omega⟩ t)) =
      nativeComplementaryPoint ((UnitaryErrorBases.ThreeCycleFourier.omega ^ t.val) •
        anchor2W ξ hξ (a, 2)) := by
  rw [literalPoint_hidden ξ hξ 0 a t]
  refine (transportTinv_one_two _ _).trans ?_
  congr 1
  ext i j
  exact famB ξ hξ a t i j

/-- Literal frames `10 + s` (C/D group) at outcome `−t`: label `(a, 1)`, `s = −a`. -/
theorem ptC (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (a : Index) (t : Fin 3) :
    transportTinv 1 (literalPoint ξ (framePointIndex ⟨4 + 3 * (2 : Fin 3).val + (-a).val, by
        have := ZMod.val_lt (-a); omega⟩ (-t))) =
      nativeComplementaryPoint ((UnitaryErrorBases.ThreeCycleFourier.omega ^ t.val) •
        anchor2W ξ hξ (a, 1)) := by
  rw [literalPoint_hidden ξ hξ 2 (-a) (-t)]
  refine (transportTinv_one_nj _ _).trans ?_
  congr 1
  ext i j
  have h := famC ξ hξ (-a) t i j
  rw [neg_neg] at h
  exact h

/-! ## The all-phase standard form -/

theorem anchor2_form (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 39) :
    transportTinv 1 (literalPoint ξ (pointRelabel fperm2 τ2 i)) =
      stdAnchored (q2 ξ) (anchor2W ξ hξ) i := by
  obtain ⟨f, a, rfl⟩ : ∃ f a, i = framePointIndex f a :=
    ⟨⟨i.val / 3, by omega⟩, ⟨i.val % 3, by omega⟩,
      Fin.ext (by rw [framePointIndex_val]; show i.val = 3 * (i.val / 3) + i.val % 3; omega)⟩
  rw [pointRelabel_framePointIndex]
  by_cases hf : f.val < 4
  · obtain ⟨k, rfl⟩ : ∃ k : Fin 4, f = Fin.castLE (by decide : 4 ≤ 13) k := ⟨⟨f.val, hf⟩, Fin.ext rfl⟩
    rw [stdA_visible]
    fin_cases k
    · have hidx : framePointIndex (fperm2 (Fin.castLE (by omega) (0 : Fin 4)))
          (τ2 (Fin.castLE (by omega) (0 : Fin 4)) a) =
          framePointIndex (Fin.castLE (by omega) (0 : Fin 4)) a := by
        revert a; decide
      exact (congrArg (fun j => transportTinv 1 (literalPoint ξ j)) hidx).trans (pt0 ξ hξ a)
    · have hidx : framePointIndex (fperm2 (Fin.castLE (by omega) (1 : Fin 4)))
          (τ2 (Fin.castLE (by omega) (1 : Fin 4)) a) =
          framePointIndex ⟨4 + 3 * (1 : Fin 3).val + (-(((0 : ℕ) : PhaseIndex))).val, by
            have := ZMod.val_lt (-(((0 : ℕ) : PhaseIndex))); omega⟩ a := by
        revert a; decide
      exact (congrArg (fun j => transportTinv 1 (literalPoint ξ j)) hidx).trans
        (ptQ ξ hξ ((0 : ℕ) : PhaseIndex) a _ rfl)
    · have hidx : framePointIndex (fperm2 (Fin.castLE (by omega) (2 : Fin 4)))
          (τ2 (Fin.castLE (by omega) (2 : Fin 4)) a) =
          framePointIndex ⟨4 + 3 * (1 : Fin 3).val + (-(((1 : ℕ) : PhaseIndex))).val, by
            have := ZMod.val_lt (-(((1 : ℕ) : PhaseIndex))); omega⟩ a := by
        revert a; decide
      exact (congrArg (fun j => transportTinv 1 (literalPoint ξ j)) hidx).trans
        (ptQ ξ hξ ((1 : ℕ) : PhaseIndex) a _ rfl)
    · have hidx : framePointIndex (fperm2 (Fin.castLE (by omega) (3 : Fin 4)))
          (τ2 (Fin.castLE (by omega) (3 : Fin 4)) a) =
          framePointIndex ⟨4 + 3 * (1 : Fin 3).val + (-(((2 : ℕ) : PhaseIndex))).val, by
            have := ZMod.val_lt (-(((2 : ℕ) : PhaseIndex))); omega⟩ a := by
        revert a; decide
      exact (congrArg (fun j => transportTinv 1 (literalPoint ξ j)) hidx).trans
        (ptQ ξ hξ ((2 : ℕ) : PhaseIndex) a _ rfl)
  · obtain ⟨l, rfl⟩ : ∃ l, hiddenFrame l = f := by
      refine ⟨hiddenFrameEquiv.symm ⟨f.val - 4, by omega⟩, ?_⟩
      ext; simp only [hiddenFrame, Equiv.apply_symm_apply]; omega
    rw [stdA_hidden]
    obtain ⟨a', b⟩ := l
    rcases Anchor0.indexCases b with rfl | rfl | rfl
    · have hidx : framePointIndex (fperm2 (hiddenFrame (a', 0))) (τ2 (hiddenFrame (a', 0)) a) =
          framePointIndex (Fin.castLE (by omega)
            (⟨(-a').val + 1, by have := ZMod.val_lt (-a'); omega⟩ : Fin 4)) a := by
        revert a' a; decide
      exact (congrArg (fun j => transportTinv 1 (literalPoint ξ j)) hidx).trans (ptA ξ hξ a' a)
    · have hidx : framePointIndex (fperm2 (hiddenFrame (a', 1))) (τ2 (hiddenFrame (a', 1)) a) =
          framePointIndex ⟨4 + 3 * (2 : Fin 3).val + (-a').val, by
            have := ZMod.val_lt (-a'); omega⟩ (-a) := by
        revert a' a; decide
      exact (congrArg (fun j => transportTinv 1 (literalPoint ξ j)) hidx).trans (ptC ξ hξ a' a)
    · have hidx : framePointIndex (fperm2 (hiddenFrame (a', 2))) (τ2 (hiddenFrame (a', 2)) a) =
          framePointIndex ⟨4 + 3 * (0 : Fin 3).val + a'.val, by
            have := ZMod.val_lt a'; omega⟩ a := by
        revert a' a; decide
      exact (congrArg (fun j => transportTinv 1 (literalPoint ξ j)) hidx).trans (ptB ξ hξ a' a)

end Anchor2

end CKM.NativeFirstOrder

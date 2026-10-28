module

public import KfixSix

@[expose] public section

/-!
# KFIX helper: the hidden `R1`-fixed first-order space has dimension six at every unit phase
-/

noncomputable section

namespace CKM.NativeFirstOrder

open CompactAlbert UnitaryErrorBases.ComplexQuartet

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega
local notation "χ" => UnitaryErrorBases.ThreeCycleFourier.character

/-- The hidden common-fixed space. -/
def kfS6 (ξ : Fin 4 → ℂ) : Submodule ℝ UnitaryErrorBases.Family :=
  UnitaryErrorBases.firstOrderSpace (kfW ξ) ⊓ kfFixH

theorem kfM_add (ξ : Fin 4 → ℂ) (V W : UnitaryErrorBases.Family) (l : UnitaryErrorBases.Label) :
    kfM ξ (V + W) l = kfM ξ V l + kfM ξ W l :=
  Matrix.mul_add _ (kfT (V l)) (kfT (W l))

theorem kfM_smul (ξ : Fin 4 → ℂ) (c : ℝ) (V : UnitaryErrorBases.Family) (l : UnitaryErrorBases.Label) :
    kfM ξ (c • V) l = c • kfM ξ V l :=
  Matrix.mul_smul _ c (kfT (V l))

/-- Six real coordinates: imaginary parts of the first two diagonal entries of `M_{(b,0)}`. -/
def kfPhi (ξ : Fin 4 → ℂ) : kfS6 ξ →ₗ[ℝ] (UnitaryErrorBases.Index → Fin 2 → ℝ) where
  toFun V b j := (kfM ξ V.1 (b, 0) (Fin.castSucc j) (Fin.castSucc j)).im
  map_add' V W := by
    funext b j
    simp only [Submodule.coe_add, kfM_add, Matrix.add_apply, Complex.add_im, Pi.add_apply]
  map_smul' c V := by
    funext b j
    simp only [SetLike.val_smul, kfM_smul, Matrix.smul_apply, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]

theorem kfPhi_injective (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Function.Injective (kfPhi ξ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨V, hV, hfix⟩ hker
  have hz : ∀ b j, (kfM ξ V (b, 0) (Fin.castSucc j) (Fin.castSucc j)).im = 0 := fun b j =>
    congrFun (congrFun (LinearMap.mem_ker.mp hker) b) j
  -- the base matrices vanish
  have hbase : ∀ b : UnitaryErrorBases.Index, ∀ k : Fin 3, kfM ξ V (b, 0) k k = 0 := by
    intro b
    have e0 : kfM ξ V (b, 0) 0 0 = 0 := Complex.ext (kf_M_diag_re ξ hξ hV _ _) (hz b 0)
    have e1 : kfM ξ V (b, 0) 1 1 = 0 := Complex.ext (kf_M_diag_re ξ hξ hV _ _) (hz b 1)
    have e2 : kfM ξ V (b, 0) 2 2 = 0 := by
      have h := kf_M_trace3 ξ hξ hV (b, 0)
      rw [e0, e1, zero_add, zero_add] at h
      exact h
    intro k
    fin_cases k
    · exact e0
    · exact e1
    · exact e2
  have hall : ∀ l : UnitaryErrorBases.Label, kfM ξ V l = 0 := by
    intro l
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hl : l = (l.1, 0)
      · rw [hl]; exact hbase l.1 i
      · rw [kf_group_const ξ hξ hV hfix (l.1, 0) l (Ne.symm hl) rfl i]
        exact hbase l.1 i
    · exact kf_M_offdiag ξ hfix l i j hij
  apply Subtype.ext
  funext l
  change kfT (V l) = 0
  rw [kf_V_eq ξ hξ V l, hall l, Matrix.mul_zero]


/-! ## Surjectivity -/

/-- The diagonal traceless anti-Hermitian matrix with imaginary parts `(y₀, y₁, -y₀-y₁)`. -/
def kfDiagM (y : Fin 2 → ℝ) : TitsComplexMatrix :=
  Matrix.diagonal ![(y 0 : ℂ) * Complex.I, (y 1 : ℂ) * Complex.I, -(((y 0 + y 1 : ℝ) : ℂ) * Complex.I)]

theorem kfDiagM_skew (y : Fin 2 → ℝ) : (kfDiagM y).conjTranspose = -kfDiagM y := by
  rw [kfDiagM, Matrix.diagonal_conjTranspose]
  ext i j
  by_cases h : i = j
  · subst h
    fin_cases i <;> simp
  · simp [Matrix.diagonal_apply_ne _ h]

theorem kfDiagM_trace (y : Fin 2 → ℝ) : Matrix.trace (kfDiagM y) = 0 := by
  rw [kfDiagM, Matrix.trace_diagonal, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, Complex.ofReal_add]
  ring

theorem kfDiagM_offdiag (y : Fin 2 → ℝ) (i j : Fin 3) (hij : i ≠ j) : kfDiagM y i j = 0 := by
  rw [kfDiagM, Matrix.diagonal_apply_ne _ hij]

theorem kfH_left_unitary : kfH.conjTranspose * kfH = 1 := by
  rw [kfH, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · exact kf_omega_star_mul
  · exact kf_omega_sq_star_mul
  · simp

theorem kfDiagM_h (y : Fin 2 → ℝ) : kfH * kfDiagM y * kfH.conjTranspose = kfDiagM y := by
  rw [kf_H_conj]
  ext i j
  rw [Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    have : kfHH i i = 1 := by fin_cases i <;> rfl
    rw [this, one_mul]
  · rw [kfDiagM_offdiag y i j hij, mul_zero]

/-- The preimage family. -/
def kfVy (ξ : Fin 4 → ℂ) (y : UnitaryErrorBases.Index → Fin 2 → ℝ) : UnitaryErrorBases.Family :=
  fun l => kfWt ξ l * kfDiagM (y l.1)

theorem kfVy_M (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (y : UnitaryErrorBases.Index → Fin 2 → ℝ)
    (l : UnitaryErrorBases.Label) : kfM ξ (kfVy ξ y) l = kfDiagM (y l.1) := by
  change (kfWt ξ l).conjTranspose * (kfWt ξ l * kfDiagM (y l.1)) = _
  rw [← Matrix.mul_assoc, kfW_unitary ξ hξ l, Matrix.one_mul]

theorem kfVy_fo (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (y : UnitaryErrorBases.Index → Fin 2 → ℝ) :
    kfVy ξ y ∈ UnitaryErrorBases.firstOrderSpace (kfW ξ) := by
  rw [ArchitectureUEBDerivative.first_order_mem_iff _ _ (kfW_ueb ξ hξ)]
  refine ⟨fun p => ?_, fun p => ?_, fun p q hpq => ?_⟩
  · show (kfWt ξ p).conjTranspose * (kfWt ξ p * kfDiagM (y p.1)) +
      (kfWt ξ p * kfDiagM (y p.1)).conjTranspose * kfWt ξ p = 0
    rw [← Matrix.mul_assoc, kfW_unitary ξ hξ p, Matrix.one_mul, Matrix.conjTranspose_mul,
      Matrix.mul_assoc, kfW_unitary ξ hξ p, Matrix.mul_one, kfDiagM_skew, add_neg_cancel]
  · show Matrix.trace ((kfWt ξ p).conjTranspose * (kfWt ξ p * kfDiagM (y p.1))) = 0
    rw [← Matrix.mul_assoc, kfW_unitary ξ hξ p, Matrix.one_mul, kfDiagM_trace]
  · show Matrix.trace ((kfWt ξ p * kfDiagM (y p.1)).conjTranspose * kfWt ξ q +
      (kfWt ξ p).conjTranspose * (kfWt ξ q * kfDiagM (y q.1))) = 0
    have e : (kfWt ξ p * kfDiagM (y p.1)).conjTranspose * kfWt ξ q +
        (kfWt ξ p).conjTranspose * (kfWt ξ q * kfDiagM (y q.1)) =
        (kfWt ξ p).conjTranspose * kfWt ξ q * kfDiagM (y q.1) -
          kfDiagM (y p.1) * ((kfWt ξ p).conjTranspose * kfWt ξ q) := by
      rw [Matrix.conjTranspose_mul, kfDiagM_skew]
      simp only [Matrix.neg_mul, Matrix.mul_assoc]
      abel
    rw [e, Matrix.trace_sub, Matrix.trace_mul_comm (kfDiagM (y p.1)), ← Matrix.trace_sub,
      ← Matrix.mul_sub, kf_trace_mul_diag]
    · refine Finset.sum_eq_zero fun k _ => ?_
      rw [kfW_gram_diag ξ hξ p q k]
      by_cases hg : p.1 = q.1
      · rw [hg, Matrix.sub_apply, sub_self, mul_zero]
      · rw [ite_eq_right hg, zero_mul]
    · intro i j hij
      rw [Matrix.sub_apply, kfDiagM_offdiag _ i j hij, kfDiagM_offdiag _ i j hij, sub_zero]

theorem kfVy_fix (ξ : Fin 4 → ℂ) (y : UnitaryErrorBases.Index → Fin 2 → ℝ) :
    kfVy ξ y ∈ kfFixH := by
  intro l
  change kfWt ξ l * kfDiagM (y l.1) =
    ω ^ (l.1).val • (kfG * (kfWt ξ l * kfDiagM (y l.1)) * kfH.conjTranspose)
  have e : kfG * (kfWt ξ l * kfDiagM (y l.1)) * kfH.conjTranspose =
      (kfG * kfWt ξ l * kfH.conjTranspose) * (kfH * kfDiagM (y l.1) * kfH.conjTranspose) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc kfH.conjTranspose kfH, kfH_left_unitary, Matrix.one_mul]
  rw [e, kfDiagM_h, ← Matrix.smul_mul, ← kfW_cov]

theorem kfPhi_surjective (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Function.Surjective (kfPhi ξ) := by
  intro y
  refine ⟨⟨kfVy ξ y, kfVy_fo ξ hξ y, kfVy_fix ξ y⟩, ?_⟩
  funext b j
  change (kfM ξ (kfVy ξ y) (b, 0) (Fin.castSucc j) (Fin.castSucc j)).im = y b j
  rw [kfVy_M ξ hξ y (b, 0)]
  fin_cases j <;> simp [kfDiagM]

/-- The hidden common-fixed space has dimension six, at every unit phase. -/
theorem kf_finrank_S6 (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Module.finrank ℝ (kfS6 ξ) = 6 := by
  rw [(LinearEquiv.ofBijective (kfPhi ξ) ⟨kfPhi_injective ξ hξ, kfPhi_surjective ξ hξ⟩).finrank_eq,
    Module.finrank_pi_fintype]
  simp [ZMod.card]

end CKM.NativeFirstOrder

module

public import A3ElimRows

@[expose] public section

/-!
# Elimination helpers V: the two directions of the elimination

The two elimination directions are assembled in `A3Elimination`.
-/

noncomputable section

namespace CKM.NativeFirstOrder.Elim

open NativePolynomial NativePolynomial.ConfigurationResiduals ConfigurationResidualIndices
open CompactAlbert

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega
local notation "πp" => CompactAlbert.nativeTitsMatrixPair

variable (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian}) (W : UnitaryErrorBases.Family)

theorem qFrame_lt {k k' : Fin 4} (h : k < k') : qFrame k < qFrame k' := by
  rw [Fin.lt_def, qFrame_val, qFrame_val]; exact h

theorem cross_re_iff (w X : ℂ) : 2 * (((1 / 9 : ℂ) * w) * X).re = 0 ↔ (w * X).re = 0 := by
  rw [mul_assoc, show (1 / 9 : ℂ) = ((1 / 9 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

theorem R0_stdAnchored' (i : Fin 39) : R0 (stdAnchored q W (stdShift i)) = stdAnchored q W i := by
  obtain ⟨f, a, rfl⟩ := point_cases i
  rcases frame_cases f with ⟨k, rfl⟩ | ⟨l, rfl⟩
  · rw [stdShift_quartet, ← pair_inj, R0_pair, stdAnchored_quartet, smul_zero]
  · rw [stdShift_hidden, ← pair_inj, R0_pair, stdAnchored_hidden, stdAnchored_hidden, omega_shift]

theorem elimForward_mem' (_hq : ∀ k t, (q k t).val * (q k t).val = (q k t).val)
    (hW : UnitaryErrorBases.IsUnitaryErrorBasis W) {δ : Fin 39 → Glennie.Albert}
    (hfix : δ ∈ fixedSpace (compensated R0 stdShift)) (hδ : δ ∈ firstOrderSystem (stdAnchored q W)) :
    (elimForward δ).1 ∈ quartetFirstOrder (fun k t => (q k t).val) ∧
      (elimForward δ).2 ∈ UnitaryErrorBases.firstOrderSpace W := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_firstOrderSystem.mp hδ
  have hQ := fun k a => fixed_quartet_pair hfix k a
  have hH := fun l a => fixed_hidden_pair hfix h3 l a
  have hPq := stdAnchored_quartet q W
  have hPh := stdAnchored_hidden q W
  refine ⟨⟨fun k t => pair_fst_isHermitian _, fun k t => ?_, fun k s => ?_, fun k => ?_,
    fun k k' t t' hkk' => ?_⟩, ?_⟩
  · exact (quartet_idem_iff (hPq k t) (hQ k t)).mp (h1 _)
  · exact (quartet_within_iff (hPq k _) (hPq k _) (hQ k _) (hQ k _)).mp (h2 (qFrame k) s)
  · have h := congrArg (fun x => (πp x).1) (h3 (qFrame k))
    simp only [map_sum, Prod.fst_sum, map_zero, Prod.fst_zero, hQ] at h
    exact h
  · rcases lt_or_gt_of_ne hkk' with hlt | hlt
    · have e := h4 ⟨(qFrame k, qFrame k'), qFrame_lt hlt⟩ t t'
      dsimp only at e
      rw [quartet_cross_eq (hPq k t) (hQ k t) (hPq k' t') (hQ k' t')] at e
      exact e
    · have e := h4 ⟨(qFrame k', qFrame k), qFrame_lt hlt⟩ t' t
      dsimp only at e
      rw [quartet_cross_eq (hPq k' t') (hQ k' t') (hPq k t) (hQ k t), Matrix.trace_add,
        Complex.add_re] at e
      rw [Matrix.trace_add, Complex.add_re, Matrix.trace_mul_comm (q k t).val,
        Matrix.trace_mul_comm ((elimForward δ).1 k t)]
      linarith
  · rw [ArchitectureUEBDerivative.first_order_mem_iff _ _ hW]
    have hidem := fun l => (hidden_idem_iff (hW.1 l).1 (hW.1 l).2 (omega_pow_mul_star _)
      (omega_pow_cube _) (hPh l 0) (hH l 0)).mp (h1 _)
    have hX : ∀ m m', hiddenFrame m < hiddenFrame m' →
        (tm (W m) * (tm ((elimForward δ).2 m')).conjTranspose +
          tm ((elimForward δ).2 m) * (tm (W m')).conjTranspose).trace = 0 := by
      intro m m' hlt
      have e0 := h4 ⟨(hiddenFrame m, hiddenFrame m'), hlt⟩ 0 0
      have e1 := h4 ⟨(hiddenFrame m, hiddenFrame m'), hlt⟩ 1 0
      dsimp only at e0 e1
      rw [hidden_cross_eq (hPh m 0) (hH m 0) (hPh m' 0) (hH m' 0), cross_re_iff] at e0
      rw [hidden_cross_eq (hPh m 1) (hH m 1) (hPh m' 0) (hH m' 0), cross_re_iff] at e1
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, star_one, mul_one, one_mul] at e0 e1
      exact eq_zero_of_re_of_re_omega e0 e1
    refine ⟨fun l => (hidem l).1, fun l => (hidem l).2, fun l l' hll' => ?_⟩
    rcases lt_or_gt_of_ne (hiddenFrame_injective.ne hll') with hlt | hlt
    · have e := pair_row_eq_star (tm (W l)) (tm ((elimForward δ).2 l)) (tm (W l'))
        (tm ((elimForward δ).2 l'))
      rw [hX l l' hlt, star_zero] at e
      exact e
    · have e := pair_row_eq_swap (tm (W l)) (tm ((elimForward δ).2 l)) (tm (W l'))
        (tm ((elimForward δ).2 l'))
      rw [hX l' l hlt] at e
      exact e

theorem elimForward_injOn' {δ δ' : Fin 39 → Glennie.Albert}
    (hfix : δ ∈ fixedSpace (compensated R0 stdShift)) (hδ : δ ∈ firstOrderSystem (stdAnchored q W))
    (hfix' : δ' ∈ fixedSpace (compensated R0 stdShift))
    (hδ' : δ' ∈ firstOrderSystem (stdAnchored q W)) (h : elimForward δ = elimForward δ') :
    δ = δ' := by
  have hfixε : δ - δ' ∈ fixedSpace (compensated R0 stdShift) := Submodule.sub_mem _ hfix hfix'
  have hfoε : δ - δ' ∈ firstOrderSystem (stdAnchored q W) := Submodule.sub_mem _ hδ hδ'
  have h0 : elimForward (δ - δ') = 0 := by rw [map_sub, h, sub_self]
  have hsum := (mem_firstOrderSystem.mp hfoε).2.2.1
  rw [← sub_eq_zero]
  funext i
  obtain ⟨f, a, rfl⟩ := point_cases i
  rcases frame_cases f with ⟨k, rfl⟩ | ⟨l, rfl⟩
  · rw [Pi.zero_apply, ← pair_eq_zero, fixed_quartet_pair hfixε, h0]
    rfl
  · rw [Pi.zero_apply, ← pair_eq_zero, fixed_hidden_pair hfixε hsum, h0]
    change ((0 : TitsComplexMatrix), (1 / 3 : ℂ) • ((ω ^ a.val) • (0 : TitsComplexMatrix))) = 0
    rw [smul_zero, smul_zero]
    rfl

theorem elimForward_surjOn' (hq : ∀ k t, (q k t).val * (q k t).val = (q k t).val)
    (hW : UnitaryErrorBases.IsUnitaryErrorBasis W)
    (x : (Fin 4 → Fin 3 → TitsComplexMatrix) × UnitaryErrorBases.Family)
    (hx₁ : x.1 ∈ quartetFirstOrder (fun k t => (q k t).val))
    (hx₂ : x.2 ∈ UnitaryErrorBases.firstOrderSpace W) :
    ∃ δ, δ ∈ fixedSpace (compensated R0 stdShift) ∧ δ ∈ firstOrderSystem (stdAnchored q W) ∧
      elimForward δ = x := by
  obtain ⟨hHe, hI, hWi, hS, hC⟩ := hx₁
  obtain ⟨hVa, hVb, hVc⟩ := (ArchitectureUEBDerivative.first_order_mem_iff _ _ hW).mp hx₂
  let δ : Fin 39 → Glennie.Albert :=
    assemble (fun k t => mkPoint (x.1 k t) (hHe k t) 0)
      (fun l t => mkPoint 0 Matrix.isHermitian_zero ((1 / 3 : ℂ) • ((ω ^ t.val) • tm (x.2 l))))
  have hDq : ∀ k a, πp (δ (framePointIndex (qFrame k) a)) = (x.1 k a, 0) := fun k a => by
    simp only [δ]; rw [assemble_quartet, mkPoint_pair]
  have hDh : ∀ l a, πp (δ (framePointIndex (hiddenFrame l) a)) =
      (0, (1 / 3 : ℂ) • ((ω ^ a.val) • tm (x.2 l))) := fun l a => by
    simp only [δ]; rw [assemble_hidden, mkPoint_pair]
  have hPq := stdAnchored_quartet q W
  have hPh := stdAnchored_hidden q W
  have hidem : ∀ l a, (2 : ℝ) • Glennie.jordan (stdAnchored q W (framePointIndex (hiddenFrame l) a))
      (δ (framePointIndex (hiddenFrame l) a)) = δ (framePointIndex (hiddenFrame l) a) :=
    fun l a => (hidden_idem_iff (hW.1 l).1 (hW.1 l).2 (omega_pow_mul_star _) (omega_pow_cube _)
      (hPh l a) (hDh l a)).mpr ⟨hVa l, hVb l⟩
  have hroot : ∀ M : TitsComplexMatrix, (1 / 3 : ℂ) • ((ω ^ (0 : Fin 3).val) • M) +
      (1 / 3 : ℂ) • ((ω ^ (1 : Fin 3).val) • M) + (1 / 3 : ℂ) • ((ω ^ (2 : Fin 3).val) • M) = 0 := by
    intro M
    rw [← smul_add, ← smul_add, ← add_smul, ← add_smul]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
    rw [one_add_omega_add_sq, zero_smul, smul_zero]
  have hsum : ∀ f : Fin 13, (∑ a : Fin 3, δ (framePointIndex f a)) = 0 := by
    intro f
    rcases frame_cases f with ⟨k, rfl⟩ | ⟨l, rfl⟩
    · rw [← pair_eq_zero, map_sum, Fin.sum_univ_three, hDq, hDq, hDq]
      have hk := hS k
      rw [Fin.sum_univ_three] at hk
      rw [Prod.mk_add_mk, Prod.mk_add_mk, hk, add_zero, add_zero]
      rfl
    · rw [← pair_eq_zero, map_sum, Fin.sum_univ_three, hDh, hDh, hDh, Prod.mk_add_mk,
        Prod.mk_add_mk, hroot, add_zero, add_zero]
      rfl
  have hPsum : ∀ l, (∑ a : Fin 3, stdAnchored q W (framePointIndex (hiddenFrame l) a)) = 1 := by
    intro l
    rw [← pair_inj, map_sum, Fin.sum_univ_three, hPh, hPh, hPh, unit_pair, Prod.mk_add_mk,
      Prod.mk_add_mk, hroot, ← add_smul, ← add_smul]
    norm_num
  refine ⟨δ, mem_fixed_of_apply ?_, mem_firstOrderSystem.mpr ⟨?_, ?_, hsum, ?_⟩, ?_⟩
  · intro i
    obtain ⟨f, a, rfl⟩ := point_cases i
    rcases frame_cases f with ⟨k, rfl⟩ | ⟨l, rfl⟩
    · rw [stdShift_quartet, ← pair_inj, R0_pair, hDq, smul_zero]
    · rw [stdShift_hidden, ← pair_inj, R0_pair, hDh, hDh, omega_shift]
  · intro i
    obtain ⟨f, a, rfl⟩ := point_cases i
    rcases frame_cases f with ⟨k, rfl⟩ | ⟨l, rfl⟩
    · exact (quartet_idem_iff (hPq k a) (hDq k a)).mpr (hI k a)
    · exact hidem l a
  · intro f s
    rcases frame_cases f with ⟨k, rfl⟩ | ⟨l, rfl⟩
    · exact (quartet_within_iff (hPq k _) (hPq k _) (hDq k _) (hDq k _)).mpr (hWi k s)
    · exact within_of_idem (fun a => stdAnchored q W (framePointIndex (hiddenFrame l) a))
        (fun a => δ (framePointIndex (hiddenFrame l) a)) (hPsum l) (hsum _) (hidem l) _ _
        (ne_of_lt (withinPair s).property)
  · rintro ⟨⟨f, g⟩, hfg⟩ a b
    dsimp only at hfg ⊢
    rcases frame_cases f with ⟨k, rfl⟩ | ⟨l, rfl⟩ <;>
      rcases frame_cases g with ⟨k', rfl⟩ | ⟨l', rfl⟩
    · rw [quartet_cross_eq (hPq k a) (hDq k a) (hPq k' b) (hDq k' b)]
      exact hC k k' a b (fun h => by subst h; exact lt_irrefl _ hfg)
    · exact quartet_hidden_cross_eq_zero (hPq k a) (hDq k a) (hPh l' b) (hDh l' b)
        (trace_eq_zero_of_tangent (hq k a) (hI k a))
    · exact absurd hfg (not_lt.mpr (le_of_lt (qFrame_lt_hiddenFrame k' l)))
    · rw [hidden_cross_eq (hPh l a) (hDh l a) (hPh l' b) (hDh l' b)]
      have hne : l ≠ l' := fun h => by subst h; exact lt_irrefl _ hfg
      have e := pair_row_eq_star (tm (W l)) (tm (x.2 l)) (tm (W l')) (tm (x.2 l'))
      have hc : star (tm (W l) * (tm (x.2 l')).conjTranspose +
          tm (x.2 l) * (tm (W l')).conjTranspose).trace = 0 := e.symm.trans (hVc l l' hne)
      rw [star_eq_zero] at hc
      rw [hc, mul_zero, Complex.zero_re, mul_zero]
  · apply Prod.ext
    · funext k t
      rw [elimForward_fst_apply, hDq]
    · funext l
      rw [elimForward_snd_apply, hDh]
      change (3 : ℝ) • ((1 / 3 : ℂ) • ((ω ^ (0 : Fin 3).val) • tm (x.2 l))) = tm (x.2 l)
      rw [Fin.val_zero, pow_zero, one_smul, ← Complex.coe_smul, smul_smul]
      norm_num

end CKM.NativeFirstOrder.Elim

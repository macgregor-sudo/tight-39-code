module

public import KfixHidden

@[expose] public section

/-!
# KFIX helper: the `R1`-fixed part of the unrestricted first-order space of the hidden family

`kfFixH ξ` is the subspace of `firstOrderSpace (kfW ξ)` fixed by `V ↦ ω^{l.1} • g V hᴴ`. Writing
`V_l = W_l M_l`, fixedness forces `M_l = h M_l hᴴ`, hence `M_l` diagonal; the pair equations then make
`M_l` depend only on the group `l.1`, leaving `3 × 2 = 6` real parameters at every unit phase.
-/

noncomputable section

namespace CKM.NativeFirstOrder

open CompactAlbert UnitaryErrorBases.ComplexQuartet

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega
local notation "χ" => UnitaryErrorBases.ThreeCycleFourier.character

/-- Reinterpret a `UnitaryErrorBases.Mat` as a Tits matrix (identity). -/
def kfT (M : UnitaryErrorBases.Mat) : TitsComplexMatrix := M

/-! ## Scalar facts -/

theorem kf_zeta_cases (s s' : UnitaryErrorBases.Index) (h : s ≠ s') :
    χ s * star (χ s') = ω ∨ χ s * star (χ s') = ω ^ 2 := by
  have h1 := kf_char_one
  have h2 := kf_char_two
  have h0 := kf_char_zero
  have hs := kf_star_omega
  have hs2 : star (ω ^ 2) = ω := by
    rw [star_pow, hs, ← pow_mul, show (2 * 2 : ℕ) = 4 by rfl, kf_omega_four]
  rcases kf_idx_cases s with rfl | rfl | rfl <;> rcases kf_idx_cases s' with rfl | rfl | rfl
  · exact absurd rfl h
  · right; rw [h0, h1, hs, one_mul]
  · left; rw [h0, h2, hs2, one_mul]
  · left; rw [h1, h0, star_one, mul_one]
  · exact absurd rfl h
  · right; rw [h1, h2, hs2, pow_two]
  · right; rw [h2, h0, star_one, mul_one]
  · left; rw [h2, h1, hs, ← pow_add, show (2 + 2 : ℕ) = 4 by rfl, kf_omega_four]
  · exact absurd rfl h

theorem kf_zeta_re (s s' : UnitaryErrorBases.Index) (h : s ≠ s') :
    (χ s * star (χ s')).re = -1 / 2 := by
  rcases kf_zeta_cases s s' h with e | e <;> rw [e]
  · exact kf_omega_re
  · exact kf_omega_sq_re

theorem kf_zeta_im (s s' : UnitaryErrorBases.Index) (h : s ≠ s') :
    (χ s * star (χ s')).im ≠ 0 := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rcases kf_zeta_cases s s' h with e | e <;> rw [e]
  · rw [kf_omega_im]; positivity
  · rw [kf_omega_sq_im]; intro hc; linarith

/-- Three purely imaginary numbers summing to zero and killed by `(1, ζ, ζ̄)` vanish. -/
theorem kf_kill_three (ζ a b c : ℂ) (hre : ζ.re = -1 / 2) (him : ζ.im ≠ 0)
    (ha : a.re = 0) (hb : b.re = 0) (hc : c.re = 0) (hsum : a + b + c = 0)
    (h : a + ζ * b + star ζ * c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hs1 := congrArg Complex.im hsum
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.zero_re, Complex.zero_im, ha, hb, hc, hre] at hs1 h1 h2
  have hbc : b.im = c.im := by
    have : ζ.im * (c.im - b.im) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 him
    · linarith
  have hb0 : b.im = 0 := by linarith
  have hc0 : c.im = 0 := by linarith
  have ha0 : a.im = 0 := by linarith
  exact ⟨Complex.ext ha ha0, Complex.ext hb hb0, Complex.ext hc hc0⟩

theorem kf_sum_rot (f : Fin 3 → ℂ) (g : Fin 3) : ∑ k : Fin 3, f (k - g) = f 0 + f 1 + f 2 := by
  rw [Fin.sum_univ_three]
  fin_cases g
  · rfl
  · show f 2 + f 0 + f 1 = _
    ring
  · show f 1 + f 2 + f 0 = _
    ring

theorem kfPat_0 (s s' : UnitaryErrorBases.Index) : kfPat s s' 0 = 1 := rfl
theorem kfPat_1 (s s' : UnitaryErrorBases.Index) : kfPat s s' 1 = χ s * star (χ s') := rfl
theorem kfPat_2 (s s' : UnitaryErrorBases.Index) : kfPat s s' 2 = star (χ s) * χ s' := rfl

theorem kf_pat_sum (s s' : UnitaryErrorBases.Index) (h : s ≠ s') (g : Fin 3) :
    ∑ k : Fin 3, kfPat s s' (k - g) = 0 := by
  rw [kf_sum_rot]
  rw [kfPat_0, kfPat_1, kfPat_2]
  have hst : star (χ s) * χ s' = star (χ s * star (χ s')) := by
    rw [star_mul', star_star, mul_comm]
  rw [hst]
  have hre := kf_zeta_re s s' h
  generalize χ s * star (χ s') = ζ at hre ⊢
  apply Complex.ext
  · simp only [Complex.add_re, Complex.one_re, Complex.star_def, Complex.conj_re, hre,
      Complex.zero_re]
    linarith
  · simp only [Complex.add_im, Complex.one_im, Complex.star_def, Complex.conj_im, Complex.zero_im]
    ring


/-! ## The hidden family is a unitary error basis -/

theorem kfW_trace_orth (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (p q : UnitaryErrorBases.Label)
    (hpq : p ≠ q) : Matrix.trace ((kfWt ξ p).conjTranspose * kfWt ξ q) = 0 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Finset.sum_congr rfl (fun k _ => kfW_gram_diag ξ hξ p q k)]
  by_cases h : p.1 = q.1
  · have hs : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h h2)
    simp only [h, ite_true]
    exact kf_pat_sum _ _ hs _
  · simp [h]

theorem kfW_ueb (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : UnitaryErrorBases.IsUnitaryErrorBasis (kfW ξ) :=
  ⟨fun p => ⟨kfW_unitary ξ hξ p, kfW_det ξ hξ p⟩, fun p q hpq => kfW_trace_orth ξ hξ p q hpq⟩

theorem kfW_right_unitary (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (l : UnitaryErrorBases.Label) :
    kfWt ξ l * (kfWt ξ l).conjTranspose = 1 :=
  mul_eq_one_comm.mp (kfW_unitary ξ hξ l)

/-! ## The fixed subspace -/

/-- Hidden `R1`-fixedness in the anchor-0 elimination coordinates. -/
def kfFixH : Submodule ℝ UnitaryErrorBases.Family where
  carrier := {V | ∀ l, kfT (V l) = ω ^ (l.1).val • (kfG * kfT (V l) * kfH.conjTranspose)}
  add_mem' := by
    intro x y hx hy l
    change kfT (x l) + kfT (y l) =
      ω ^ (l.1).val • (kfG * (kfT (x l) + kfT (y l)) * kfH.conjTranspose)
    rw [Matrix.mul_add, Matrix.add_mul, smul_add, ← hx l, ← hy l]
  zero_mem' := by
    intro l
    show (0 : TitsComplexMatrix) = ω ^ (l.1).val • (kfG * (0 : TitsComplexMatrix) * kfH.conjTranspose)
    simp
  smul_mem' := by
    intro c x hx l
    change c • kfT (x l) = ω ^ (l.1).val • (kfG * (c • kfT (x l)) * kfH.conjTranspose)
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm, ← hx l]


/-! ## Right trivialization -/

/-- `M_l = W_lᴴ V_l`. -/
def kfM (ξ : Fin 4 → ℂ) (V : UnitaryErrorBases.Family) (l : UnitaryErrorBases.Label) :
    TitsComplexMatrix :=
  (kfWt ξ l).conjTranspose * kfT (V l)

theorem kf_V_eq (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (V : UnitaryErrorBases.Family)
    (l : UnitaryErrorBases.Label) : kfT (V l) = kfWt ξ l * kfM ξ V l := by
  rw [kfM, ← Matrix.mul_assoc, kfW_right_unitary ξ hξ l, Matrix.one_mul]

theorem kf_fo (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {V : UnitaryErrorBases.Family}
    (hV : V ∈ UnitaryErrorBases.firstOrderSpace (kfW ξ)) :
    UnitaryErrorBases.SatisfiesFirstOrder (kfW ξ) V :=
  (ArchitectureUEBDerivative.first_order_mem_iff _ _ (kfW_ueb ξ hξ)).mp hV

theorem kf_M_skew (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {V : UnitaryErrorBases.Family}
    (hV : V ∈ UnitaryErrorBases.firstOrderSpace (kfW ξ)) (l : UnitaryErrorBases.Label) :
    (kfM ξ V l).conjTranspose = -kfM ξ V l := by
  have h' : (kfWt ξ l).conjTranspose * kfT (V l) + (kfT (V l)).conjTranspose * kfWt ξ l = 0 :=
    (kf_fo ξ hξ hV).1 l
  rw [kfM, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h')

theorem kf_M_trace (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {V : UnitaryErrorBases.Family}
    (hV : V ∈ UnitaryErrorBases.firstOrderSpace (kfW ξ)) (l : UnitaryErrorBases.Label) :
    Matrix.trace (kfM ξ V l) = 0 :=
  (kf_fo ξ hξ hV).2.1 l

theorem kfG_left_unitary : kfG.conjTranspose * kfG = 1 := by
  rw [kfG, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · simp
  · exact kf_omega_sq_star_mul
  · exact kf_omega_star_mul

theorem kf_omega_pow_unit (n : ℕ) : star (ω ^ n) * ω ^ n = 1 := by
  rw [star_pow, ← mul_pow, kf_omega_star_mul, one_pow]

theorem kf_conj_pair (A B G H : TitsComplexMatrix) (c : ℂ) (hc : star c * c = 1)
    (hG : G.conjTranspose * G = 1) :
    (c • (G * A * H.conjTranspose)).conjTranspose * (c • (G * B * H.conjTranspose)) =
      H * (A.conjTranspose * B) * H.conjTranspose := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc, one_smul]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc G.conjTranspose G, hG, Matrix.one_mul]

theorem kf_M_h (ξ : Fin 4 → ℂ) {V : UnitaryErrorBases.Family} (hfix : V ∈ kfFixH)
    (l : UnitaryErrorBases.Label) : kfM ξ V l = kfH * kfM ξ V l * kfH.conjTranspose := by
  have hc := kf_omega_pow_unit (l.1).val
  have hV := hfix l
  have hW := kfW_cov ξ l
  calc kfM ξ V l = (kfWt ξ l).conjTranspose * kfT (V l) := rfl
    _ = (ω ^ (l.1).val • (kfG * kfWt ξ l * kfH.conjTranspose)).conjTranspose *
        (ω ^ (l.1).val • (kfG * kfT (V l) * kfH.conjTranspose)) := by
      conv_lhs => rw [hW, hV]
    _ = _ := kf_conj_pair _ _ _ _ _ hc kfG_left_unitary

/-- `h M hᴴ` is entrywise multiplication by `h_i h̄_j`. -/
def kfHH : Fin 3 → Fin 3 → ℂ := ![![1, ω ^ 2, ω], ![ω, 1, ω ^ 2], ![ω ^ 2, ω, 1]]

theorem kf_H_conj (a : TitsComplexMatrix) :
    kfH * a * kfH.conjTranspose = Matrix.of fun i j => kfHH i j * a i j := by
  ext i j
  rw [kfH, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;>
    simp [kfHH, kf_star_omega, star_pow] <;> ring_nf <;>
    (try simp only [kf_omega_cube, kf_omega_four, kf_omega_five, kf_omega_six, one_mul])

theorem kf_omega_ne_one : ω ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [kf_omega_re, Complex.one_re] at this
  norm_num at this

theorem kf_omega_sq_ne_one : ω ^ 2 ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [kf_omega_sq_re, Complex.one_re] at this
  norm_num at this

theorem kfHH_ne_one (i j : Fin 3) (hij : i ≠ j) : kfHH i j ≠ 1 := by
  fin_cases i <;> fin_cases j <;>
    first | exact absurd rfl hij | exact kf_omega_ne_one | exact kf_omega_sq_ne_one

theorem kf_M_offdiag (ξ : Fin 4 → ℂ) {V : UnitaryErrorBases.Family} (hfix : V ∈ kfFixH)
    (l : UnitaryErrorBases.Label) (i j : Fin 3) (hij : i ≠ j) : kfM ξ V l i j = 0 := by
  have h := congrFun (congrFun (kf_M_h ξ hfix l) i) j
  rw [kf_H_conj, Matrix.of_apply] at h
  have h2 : (1 - kfHH i j) * kfM ξ V l i j = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3).symm (kfHH_ne_one i j hij)
  · exact h3

theorem kf_trace_mul_diag (G D : TitsComplexMatrix) (hD : ∀ i j, i ≠ j → D i j = 0) :
    Matrix.trace (G * D) = ∑ k, G k k * D k k := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single k]
  · intro j _ hj
    rw [hD j k hj, mul_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

theorem kf_M_pair (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {V : UnitaryErrorBases.Family}
    (hV : V ∈ UnitaryErrorBases.firstOrderSpace (kfW ξ)) (hfix : V ∈ kfFixH)
    (p q : UnitaryErrorBases.Label) (hpq : p ≠ q) :
    ∑ k, ((kfWt ξ p).conjTranspose * kfWt ξ q) k k * (kfM ξ V q k k - kfM ξ V p k k) = 0 := by
  have h' : Matrix.trace ((kfT (V p)).conjTranspose * kfWt ξ q +
      (kfWt ξ p).conjTranspose * kfT (V q)) = 0 := (kf_fo ξ hξ hV).2.2 p q hpq
  rw [kf_V_eq ξ hξ V p, kf_V_eq ξ hξ V q] at h'
  have e : (kfWt ξ p * kfM ξ V p).conjTranspose * kfWt ξ q +
      (kfWt ξ p).conjTranspose * (kfWt ξ q * kfM ξ V q) =
      (kfWt ξ p).conjTranspose * kfWt ξ q * kfM ξ V q -
        kfM ξ V p * ((kfWt ξ p).conjTranspose * kfWt ξ q) := by
    rw [Matrix.conjTranspose_mul, kf_M_skew ξ hξ hV p]
    simp only [Matrix.neg_mul, Matrix.mul_assoc]
    abel
  rw [e, Matrix.trace_sub, Matrix.trace_mul_comm (kfM ξ V p), ← Matrix.trace_sub, ← Matrix.mul_sub,
    kf_trace_mul_diag] at h'
  · simpa only [Matrix.sub_apply] using h'
  · intro i j hij
    rw [Matrix.sub_apply, kf_M_offdiag ξ hfix q i j hij, kf_M_offdiag ξ hfix p i j hij, sub_zero]


theorem kf_sum_rot2 (f D : Fin 3 → ℂ) (g : Fin 3) :
    ∑ k : Fin 3, f (k - g) * D k = f 0 * D g + f 1 * D (g + 1) + f 2 * D (g + 2) := by
  rw [Fin.sum_univ_three]
  fin_cases g
  · rfl
  · show f 2 * D 0 + f 0 * D 1 + f 1 * D 2 = f 0 * D 1 + f 1 * D 2 + f 2 * D 0
    ring
  · show f 1 * D 0 + f 2 * D 1 + f 0 * D 2 = f 0 * D 2 + f 1 * D 0 + f 2 * D 1
    ring

theorem kf_M_diag_re (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {V : UnitaryErrorBases.Family}
    (hV : V ∈ UnitaryErrorBases.firstOrderSpace (kfW ξ)) (l : UnitaryErrorBases.Label) (k : Fin 3) :
    (kfM ξ V l k k).re = 0 := by
  have h := congrFun (congrFun (kf_M_skew ξ hξ hV l) k) k
  rw [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
  have h2 := congrArg Complex.re h
  rw [Complex.star_def, Complex.conj_re, Complex.neg_re] at h2
  linarith

theorem kf_M_trace3 (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {V : UnitaryErrorBases.Family}
    (hV : V ∈ UnitaryErrorBases.firstOrderSpace (kfW ξ)) (l : UnitaryErrorBases.Label) :
    kfM ξ V l 0 0 + kfM ξ V l 1 1 + kfM ξ V l 2 2 = 0 := by
  have h := kf_M_trace ξ hξ hV l
  rw [Matrix.trace, Fin.sum_univ_three] at h
  exact h

theorem kf_rot_sum (D : Fin 3 → ℂ) (g : Fin 3) (h : D 0 + D 1 + D 2 = 0) :
    D g + D (g + 1) + D (g + 2) = 0 := by
  fin_cases g
  · exact h
  · show D 1 + D 2 + D 0 = 0
    linear_combination h
  · show D 2 + D 0 + D 1 = 0
    linear_combination h

theorem kf_rot_cover (g k : Fin 3) : k = g ∨ k = g + 1 ∨ k = g + 2 := by
  revert g k; decide

/-- Within one hidden group the diagonal of `M` is constant. -/
theorem kf_group_const (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {V : UnitaryErrorBases.Family}
    (hV : V ∈ UnitaryErrorBases.firstOrderSpace (kfW ξ)) (hfix : V ∈ kfFixH)
    (p q : UnitaryErrorBases.Label) (hpq : p ≠ q) (hg : p.1 = q.1) (k : Fin 3) :
    kfM ξ V q k k = kfM ξ V p k k := by
  have hs : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext hg h2)
  have hpair := kf_M_pair ξ hξ hV hfix p q hpq
  simp only [kfW_gram_diag ξ hξ p q, hg, ite_true] at hpair
  set D : Fin 3 → ℂ := fun k => kfM ξ V q k k - kfM ξ V p k k with hD
  have hpair' : ∑ k : Fin 3, kfPat p.2 q.2 (k - kfToFin q.1) * D k = 0 := hpair
  rw [kf_sum_rot2, kfPat_0, kfPat_1, kfPat_2] at hpair'
  have hre : ∀ k, (D k).re = 0 := fun k => by
    simp only [hD, Complex.sub_re, kf_M_diag_re ξ hξ hV, sub_zero]
  have hsum : D 0 + D 1 + D 2 = 0 := by
    have h1 := kf_M_trace3 ξ hξ hV q
    have h2 := kf_M_trace3 ξ hξ hV p
    simp only [hD]
    linear_combination h1 - h2
  have hst : star (χ p.2) * χ q.2 = star (χ p.2 * star (χ q.2)) := by
    rw [star_mul', star_star, mul_comm]
  rw [hst, one_mul] at hpair'
  obtain ⟨h0, h1, h2⟩ := kf_kill_three _ _ _ _ (kf_zeta_re _ _ hs) (kf_zeta_im _ _ hs) (hre _) (hre _)
    (hre _) (kf_rot_sum D _ hsum) hpair'
  have hk : D k = 0 := by
    rcases kf_rot_cover (kfToFin q.1) k with e | e | e <;> rw [e]
    · exact h0
    · exact h1
    · exact h2
  exact sub_eq_zero.mp hk

end CKM.NativeFirstOrder

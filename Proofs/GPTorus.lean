module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Algebra.MvPolynomial

@[expose] public section

/-!
# Nonvanishing of a nonzero complex polynomial on the unit torus

`UnitTorus n` is the unit torus `{ξ ∈ ℂⁿ : |ξ a| = 1 for all a}` with the subspace topology. A nonzero
ordinary polynomial `p ∈ ℂ[X₀, …, X_{n-1}]` cannot vanish on a nonempty open subset of the torus: such
a set contains a product of infinite circle arcs, and a polynomial vanishing on a product of infinite
sets is zero (`MvPolynomial.funext_set`). Hence the nonvanishing locus is open and dense, and it
accumulates at every point of the torus through points different from that point.

This is standard mathematics, not a new result: the vanishing statement is N. Alon, *Combinatorial
Nullstellensatz*, Combin. Probab. Comput. 8 (1999), Lemma 2.1 (sets of size `> deg_{x_i} P`), here in
mathlib's form `MvPolynomial.funext_set` (Mathlib/Algebra/MvPolynomial/Funext.lean, J. Commelin).
-/

noncomputable section

open MvPolynomial Filter Topology

namespace CKM.NativeGoodPhase

/-- The unit torus in `ℂⁿ`, with the subspace topology of the product topology. -/
abbrev UnitTorus (n : ℕ) := {ξ : Fin n → ℂ // ∀ a, Complex.normSq (ξ a) = 1}

/-- The nonvanishing locus of a polynomial on the unit torus. -/
def evalNeZeroSet {n : ℕ} (p : MvPolynomial (Fin n) ℂ) : Set (UnitTorus n) :=
  {u | eval u.1 p ≠ 0}

theorem isOpen_evalNeZeroSet {n : ℕ} (p : MvPolynomial (Fin n) ℂ) : IsOpen (evalNeZeroSet p) := by
  -- `u ↦ eval u.1 p` is continuous, and `{· ≠ 0}` is open.
  exact isOpen_ne_fun ((MvPolynomial.continuous_eval p).comp continuous_subtype_val) continuous_const

/-- A nonzero polynomial does not vanish identically on a nonempty open subset of the torus. -/
theorem exists_eval_ne_zero_of_isOpen {n : ℕ} {p : MvPolynomial (Fin n) ℂ} (hp : p ≠ 0)
    {U : Set (UnitTorus n)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ u ∈ U, eval u.1 p ≠ 0 := by
  by_contra hzero
  simp only [not_exists, not_and, not_not] at hzero
  obtain ⟨u, hu⟩ := hne
  -- Rotate `u` coordinatewise by real angles: a continuous map into the torus, sending `0` to `u`.
  let f : (Fin n → ℝ) → UnitTorus n := fun θ =>
    ⟨fun a => u.1 a * Complex.exp (θ a * Complex.I), fun a => by
      rw [Complex.normSq_mul, u.2 a, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
      norm_num⟩
  have hf : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_pi fun a => continuous_const.mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_apply a)).mul continuous_const))
  have hf0 : f 0 = u := by ext a; simp [f]
  -- The preimage of `U` is an open neighbourhood of `0`, so it contains a sup-norm ball.
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, Metric.ball (0 : Fin n → ℝ) δ ⊆ f ⁻¹' U :=
    Metric.isOpen_iff.1 (hU.preimage hf) 0 (by simpa [hf0] using hu)
  set δ' := min δ 1 with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ one_pos
  have hδ'π : δ' < Real.pi := lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.two_le_pi])
  -- Coordinate arcs `u a · exp(t i)`, `t ∈ (0, δ')`: infinite since `cos` is injective on `[0, π]`.
  let s : Fin n → Set ℂ := fun a => (fun t : ℝ => u.1 a * Complex.exp (t * Complex.I)) '' Set.Ioo 0 δ'
  have hs : ∀ a, (s a).Infinite := by
    intro a
    refine (Set.Ioo_infinite hδ'pos).image ?_
    intro x hx y hy hxy
    have hua : u.1 a ≠ 0 := by
      intro h0; have := u.2 a; rw [h0, map_zero] at this; exact zero_ne_one this
    have he : Complex.exp (x * Complex.I) = Complex.exp (y * Complex.I) :=
      mul_left_cancel₀ hua hxy
    have hc : Real.cos x = Real.cos y := by
      have := congrArg Complex.re he
      rwa [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re] at this
    exact Real.injOn_cos ⟨hx.1.le, (hx.2.trans hδ'π).le⟩ ⟨hy.1.le, (hy.2.trans hδ'π).le⟩ hc
  -- Every point of the product of arcs is a point of `U`, so `p` vanishes there; hence `p = 0`.
  refine hp (MvPolynomial.funext_set s hs fun x hx => ?_)
  have hx' : ∀ a, ∃ t ∈ Set.Ioo 0 δ', u.1 a * Complex.exp (t * Complex.I) = x a :=
    fun a => hx a (Set.mem_univ a)
  choose θ hθ hθx using hx'
  have hθball : θ ∈ Metric.ball (0 : Fin n → ℝ) δ := by
    rw [mem_ball_zero_iff, pi_norm_lt_iff hδ]
    intro a
    rw [Real.norm_eq_abs, abs_lt]
    exact ⟨by linarith [(hθ a).1], lt_of_lt_of_le (hθ a).2 (min_le_left _ _)⟩
  have hxf : (f θ).1 = x := funext hθx
  rw [map_zero, ← hxf]
  exact hzero _ (hball hθball)

theorem dense_evalNeZeroSet {n : ℕ} {p : MvPolynomial (Fin n) ℂ} (hp : p ≠ 0) :
    Dense (evalNeZeroSet p) := by
  -- Every nonempty open set meets the nonvanishing locus.
  refine dense_iff_inter_open.2 fun U hU hne => ?_
  obtain ⟨u, hu, hpu⟩ := exists_eval_ne_zero_of_isOpen hp hU hne
  exact ⟨u, hu, hpu⟩

/-- Punctured accumulation: for `n ≥ 1`, every point of the torus is the limit of a sequence of
nonvanishing points of `p`, all different from it. -/
theorem exists_seq_evalNeZero_tendsto {n : ℕ} (hn : 0 < n) {p : MvPolynomial (Fin n) ℂ}
    (hp : p ≠ 0) (u₀ : UnitTorus n) :
    ∃ u : ℕ → UnitTorus n, (∀ k, eval (u k).1 p ≠ 0) ∧ (∀ k, u k ≠ u₀) ∧
      Tendsto u atTop (𝓝 u₀) := by
  -- Multiply `p` by `X a₀ - u₀ a₀`: nonvanishing of the product also forces `u ≠ u₀`.
  set a₀ : Fin n := ⟨0, hn⟩
  set r : MvPolynomial (Fin n) ℂ := p * (X a₀ - C (u₀.1 a₀))
  have hlin : (X a₀ - C (u₀.1 a₀) : MvPolynomial (Fin n) ℂ) ≠ 0 := by
    intro h0
    have := congrArg (eval (fun _ => u₀.1 a₀ + 1)) h0
    simp at this
  have hr : r ≠ 0 := mul_ne_zero hp hlin
  have hevr : ∀ v : UnitTorus n, eval v.1 r = eval v.1 p * (v.1 a₀ - u₀.1 a₀) := by
    intro v; simp [r]
  -- In each ball of radius `1/(k+1)` around `u₀`, pick a point where `r` does not vanish.
  have hk : ∀ k : ℕ, ∃ v ∈ Metric.ball u₀ (1 / ((k : ℝ) + 1)), eval v.1 r ≠ 0 := fun k =>
    exists_eval_ne_zero_of_isOpen hr Metric.isOpen_ball
      ⟨u₀, Metric.mem_ball_self (by positivity)⟩
  choose u hu hru using hk
  refine ⟨u, fun k => ?_, fun k hk0 => ?_, ?_⟩
  · have := hru k; rw [hevr] at this; exact left_ne_zero_of_mul this
  · have := hru k; rw [hevr, hk0, sub_self, mul_zero] at this; exact this rfl
  · rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun k => (hu k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat


end CKM.NativeGoodPhase

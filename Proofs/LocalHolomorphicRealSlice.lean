module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Tactic

@[expose] public section

/-! Local holomorphic uniqueness from a real coordinate slice, for the A7
multiplier. All line evaluations stay in one explicit analytic ball; no
entire extension is assumed. Standard one-variable identity theorem is the
mathlib dependency. This is a first-party proof, not copied source.
 -/

noncomputable section
namespace Option2.NativeStress.LocalRealSliceA7
open Set Filter
open scoped Topology

private theorem norm_real_cast {n : ℕ} (x : Fin n → ℝ) :
    ‖fun j => (x j : ℂ)‖ = ‖x‖ := by
  simp [Pi.norm_def]

/-- A local holomorphic scalar germ vanishing on a real neighborhood is zero.
The proof uses one complex disk for each vector, with uniform radius control. -/
theorem eventually_zero_of_real_slice {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticAt ℂ f 0)
    (hr : (fun x : Fin n → ℝ => f (fun j => (x j : ℂ))) =ᶠ[𝓝 0] 0) :
    f =ᶠ[𝓝 0] 0 := by
  obtain ⟨r,hrpos,hfr⟩ := hf.exists_ball_analyticOnNhd
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.1 hr
  let b := min r ε
  have hb : 0 < b := lt_min hrpos hε
  have hbr : b ≤ r := min_le_left _ _
  have hbε : b ≤ ε := min_le_right _ _
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : Fin n → ℂ) (by positivity : 0 < b/4))
  intro z hz
  change f z = 0
  have hz' : ‖z‖ < b/4 := by simpa using hz
  let line : ℂ → (Fin n → ℂ) := fun t j => ((z j).re : ℂ) + t * ((z j).im : ℂ)
  have hline : Differentiable ℂ line := by
    apply differentiable_pi.mpr
    intro j
    dsimp [line]
    fun_prop
  have hbound : ∀ t : ℂ, ‖t‖ < 2 → ‖line t‖ < b := by
    intro t ht
    have hle : ‖line t‖ ≤ ‖z‖ + ‖t‖ * ‖z‖ := by
      apply (pi_norm_le_iff_of_nonneg (by positivity)).2
      intro j
      calc
        ‖line t j‖ ≤ ‖((z j).re : ℂ)‖ + ‖t * ((z j).im : ℂ)‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ‖t‖ * ‖z‖ := by
          rw [norm_mul]
          apply add_le_add
          · simpa only [Complex.norm_real,Real.norm_eq_abs] using
              (Complex.abs_re_le_norm (z j)).trans (norm_le_pi_norm z j)
          · apply mul_le_mul_of_nonneg_left _ (norm_nonneg t)
            simpa only [Complex.norm_real,Real.norm_eq_abs] using
              (Complex.abs_im_le_norm (z j)).trans (norm_le_pi_norm z j)
    have hn := norm_nonneg z
    nlinarith
  have han : AnalyticOnNhd ℂ (f ∘ line) (Metric.ball 0 2) := by
    intro t ht
    apply (hfr (line t) ?_).comp (hline.analyticAt t)
    simpa using (hbound t (by simpa using ht)).trans_le hbr
  have hreal : ∀ t : ℝ, |t| < 2 → (f ∘ line) t = 0 := by
    intro t ht
    let x : Fin n → ℝ := fun j => (z j).re + t * (z j).im
    have hx : (fun j => (x j : ℂ)) = line t := by
      ext j
      simp [x,line]
    have hxn : ‖x‖ < ε := by
      rw [← norm_real_cast x,hx]
      apply (hbound (t : ℂ) ?_).trans_le hbε
      simpa using ht
    have hv := hεsub (show x ∈ Metric.ball 0 ε by simpa using hxn)
    change f (fun j => (x j : ℂ)) = 0 at hv
    simpa only [hx,Function.comp_apply,Pi.zero_apply] using hv
  have hacc : (0 : ℂ) ∈ closure ({t | (f ∘ line) t = 0} \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    let t := min (δ/2) 1
    have ht : 0 < t := lt_min (half_pos hδ) zero_lt_one
    have ht1 : t ≤ 1 := min_le_right _ _
    have htδ : t < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
    refine ⟨(t : ℂ),⟨hreal t (by rw [abs_of_pos ht]; linarith),?_⟩,?_⟩
    · simpa using (ne_of_gt ht)
    · simpa [dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht] using htδ
  have hz0 := han.eqOn_zero_of_preconnected_of_mem_closure
    (convex_ball (0 : ℂ) 2).isPreconnected
    (by simp : (0 : ℂ) ∈ Metric.ball 0 2) hacc
    (by simp : Complex.I ∈ Metric.ball 0 2)
  have hi : line Complex.I = z := by
    funext j
    dsimp [line]
    rw [mul_comm Complex.I,Complex.re_add_im]
  simpa only [Function.comp_apply,hi,Pi.zero_apply] using hz0

#print axioms eventually_zero_of_real_slice
end Option2.NativeStress.LocalRealSliceA7

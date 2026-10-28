module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Tactic

@[expose] public section

/-! Uniqueness for entire functions on a finite complex coordinate space from
their actual real slice. The proof uses one complex line, not coordinate expansion. -/

noncomputable section
namespace Option2.NativeStress.EntireRealSliceA6
open Set

theorem entire_scalar_zero_of_real (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hr : ∀ t : ℝ, f t = 0) (z : ℂ) : f z = 0 := by
  have hc : (0 : ℂ) ∈ closure ({w | f w = 0} \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨((ε / 2 : ℝ) : ℂ), ⟨hr _, ?_⟩, ?_⟩
    · simpa only [Set.mem_singleton_iff, Complex.ofReal_eq_zero] using
        (ne_of_gt (half_pos hε))
    · simpa [dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hε] using half_lt_self hε
  have ha : AnalyticOnNhd ℂ f Set.univ := fun w _ => hf.analyticAt w
  exact ha.eqOn_zero_of_preconnected_of_mem_closure isPreconnected_univ
      (mem_univ (0 : ℂ)) hc (mem_univ z)

/-- Every complex vector lies on a complex line whose real points are real
vectors. Thus global real-slice vanishing determines an entire scalar function. -/
theorem entire_zero_of_real_slice {σ : Type*} [Fintype σ] (f : (σ → ℂ) → ℂ)
    (hf : Differentiable ℂ f)
    (hr : ∀ x : σ → ℝ, f (fun i => (x i : ℂ)) = 0)
    (z : σ → ℂ) : f z = 0 := by
  let line : ℂ → (σ → ℂ) := fun t i => ((z i).re : ℂ) + t * ((z i).im : ℂ)
  have hl : Differentiable ℂ line := by
    apply differentiable_pi.mpr
    intro i
    dsimp [line]
    fun_prop
  have hg : Differentiable ℂ (f ∘ line) := hf.comp hl
  have hreal : ∀ t : ℝ, (f ∘ line) t = 0 := by
    intro t
    simpa only [Function.comp_apply, line, Complex.ofReal_add, Complex.ofReal_mul]
      using hr (fun i => (z i).re + t * (z i).im)
  have hi : line Complex.I = z := by
    funext i
    dsimp [line]
    rw [mul_comm Complex.I, Complex.re_add_im]
  have h := entire_scalar_zero_of_real (f ∘ line) hg hreal Complex.I
  simpa only [Function.comp_apply, hi] using h

#print axioms Option2.NativeStress.EntireRealSliceA6.entire_zero_of_real_slice
end Option2.NativeStress.EntireRealSliceA6

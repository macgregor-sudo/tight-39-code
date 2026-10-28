module

public import LocalHolomorphicRealSlice

@[expose] public section

/-! Local real nonvanishing density for a nonzero holomorphic germ.
Real analytic continuation is used only on one connected real ball, and the
local real-slice uniqueness theorem supplies the passage back to complex
germs. There is no entire-extension premise. Legacy development source. -/

noncomputable section
namespace Option2.NativeStress.LocalRealSliceA7
open Set Filter
open scoped Topology

theorem exists_real_ball_open_dense_nonzero {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticAt ℂ f 0) (hnz : ¬ f =ᶠ[𝓝 0] 0) :
    ∃ r : ℝ, 0 < r ∧
      IsOpen {x : Fin n → ℝ | x ∈ Metric.ball 0 r ∧ f (fun j => (x j : ℂ)) ≠ 0} ∧
      Metric.ball (0 : Fin n → ℝ) r ⊆
        closure {x : Fin n → ℝ | x ∈ Metric.ball 0 r ∧ f (fun j => (x j : ℂ)) ≠ 0} := by
  obtain ⟨r,hr,hfr⟩ := hf.exists_ball_analyticOnNhd
  let g : (Fin n → ℝ) → ℂ := fun x => f (fun j => (x j : ℂ))
  have hga : AnalyticOnNhd ℝ g (Metric.ball 0 r) := by
    intro x hx
    have hc : AnalyticAt ℝ (fun x : Fin n → ℝ => fun j => (x j : ℂ)) x := by
      apply AnalyticAt.pi
      intro j
      exact (Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)).analyticAt x
    have hx' : (fun j => (x j : ℂ)) ∈ Metric.ball (0 : Fin n → ℂ) r := by
      simpa [Metric.mem_ball,dist_zero_right,Pi.norm_def] using hx
    exact ((hfr _ hx').restrictScalars (𝕜 := ℝ)).comp hc
  refine ⟨r,hr,?_,?_⟩
  · apply isOpen_iff_mem_nhds.2
    intro x hx
    exact inter_mem (Metric.isOpen_ball.mem_nhds hx.1)
      ((hga x hx.1).continuousAt.preimage_mem_nhds
        (isOpen_compl_singleton.mem_nhds hx.2))
  · intro x hx
    apply mem_closure_iff_nhds.2
    intro V hV
    by_contra hnone
    have hgzero : g =ᶠ[𝓝 x] 0 := by
      filter_upwards [hV,Metric.isOpen_ball.mem_nhds hx] with y hyV hyB
      change g y = 0
      by_contra hy
      exact hnone ⟨y,hyV,hyB,hy⟩
    have hgon := hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : Fin n → ℝ) r).isPreconnected hx hgzero
    have hgz : g =ᶠ[𝓝 0] 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : Fin n → ℝ) hr] with y hy
      exact hgon hy
    exact hnz (eventually_zero_of_real_slice f hf hgz)

#print axioms exists_real_ball_open_dense_nonzero
end Option2.NativeStress.LocalRealSliceA7

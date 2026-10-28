module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Nearest orthogonal block and normal rescaling

Lean 4.35.0-rc2 / Mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55. No analytic prototype dependency.
All projections and distances below are the actual Mathlib constructions.
-/

open Filter
open scoped Topology

namespace SupportedStress

theorem eventually_nearest_block_and_normal_rescaling
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (W : ι → Submodule ℝ E)
    (horth : Pairwise (fun i j => (W i).IsOrtho (W j)))
    (i : ι) (w : E) (hw : w ∈ W i) (hwunit : ‖w‖ = 1)
    (u : ℕ → E) (hne : ∀ n : ℕ, u n ≠ 0)
    (hlimit : Tendsto (fun n : ℕ => (‖u n‖⁻¹ : ℝ) • u n) atTop (𝓝 w)) :
    (∀ᶠ n in atTop,
      (∀ j : ι, j ≠ i →
        Metric.infDist (u n) (W i : Set E) < Metric.infDist (u n) (W j : Set E)) ∧
      Metric.infDist (u n) (⋃ j, (W j : Set E)) =
        ‖u n - (W i).starProjection (u n)‖) ∧
    Tendsto (fun n : ℕ => ‖u n - (W i).starProjection (u n)‖ / ‖u n‖)
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (‖u n‖⁻¹ : ℝ) • (W i).starProjection (u n))
      atTop (𝓝 w) ∧
    (∀ n : ℕ, u n - (W i).starProjection (u n) ∈ (W i).orthogonal) := by
  let v : ℕ → E := fun n => (‖u n‖⁻¹ : ℝ) • u n
  let P : E →L[ℝ] E := (W i).starProjection
  let S : Set E := ⋃ j, (W j : Set E)
  have hv : Tendsto v atTop (𝓝 w) := hlimit
  have hPw : P w = w :=
    (Submodule.starProjection_eq_self_iff (K := W i)).mpr hw
  have hscale : ∀ (j : ι) (n : ℕ),
      Metric.infDist (v n) (W j : Set E) = Metric.infDist (u n) (W j : Set E) / ‖u n‖ := by
    intro j n
    rw [← (W j).dist_starProjection_eq_infDist (v n),
      ← (W j).dist_starProjection_eq_infDist (u n)]
    simp only [dist_eq_norm, v, map_smul, ← smul_sub, norm_smul, norm_inv,
      norm_norm, div_eq_mul_inv, mul_comm]
  have hclose : ∀ᶠ n in atTop, dist (v n) w < (1 / 3 : ℝ) := by
    exact hv.eventually (Metric.ball_mem_nhds w (by norm_num))
  have hnormalizedStrict : ∀ᶠ n in atTop, ∀ j : ι, j ≠ i →
      Metric.infDist (v n) (W i : Set E) < Metric.infDist (v n) (W j : Set E) := by
    filter_upwards [hclose] with n hn
    intro j hji
    have horthij : (W i).IsOrtho (W j) := horth hji.symm
    have hPjw : (W j).starProjection w = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff (K := W j)).mpr (horthij hw)
    have hdistw : Metric.infDist w (W j : Set E) = 1 := by
      rw [← (W j).dist_starProjection_eq_infDist w, hPjw, dist_zero_right, hwunit]
    have hdi : Metric.infDist (v n) (W i : Set E) ≤ dist (v n) w :=
      Metric.infDist_le_dist_of_mem hw
    have htriangle := Metric.infDist_le_infDist_add_dist
      (x := w) (y := v n) (s := (W j : Set E))
    rw [hdistw, dist_comm w (v n)] at htriangle
    linarith
  have hstrict : ∀ᶠ n in atTop, ∀ j : ι, j ≠ i →
      Metric.infDist (u n) (W i : Set E) < Metric.infDist (u n) (W j : Set E) := by
    filter_upwards [hnormalizedStrict] with n hn
    intro j hji
    have h := hn j hji
    rw [hscale i n, hscale j n] at h
    exact (div_lt_div_iff_of_pos_right (norm_pos_iff.mpr (hne n))).mp h
  have hSnonempty : S.Nonempty :=
    ⟨0, Set.mem_iUnion.mpr ⟨i, (W i).zero_mem⟩⟩
  have hsub : (W i : Set E) ⊆ S := fun x hx => Set.mem_iUnion.mpr ⟨i, hx⟩
  have hnearest : ∀ᶠ n in atTop,
      (∀ j : ι, j ≠ i →
        Metric.infDist (u n) (W i : Set E) < Metric.infDist (u n) (W j : Set E)) ∧
      Metric.infDist (u n) S = ‖u n - P (u n)‖ := by
    filter_upwards [hstrict] with n hn
    refine ⟨hn, ?_⟩
    have hupper : Metric.infDist (u n) S ≤ Metric.infDist (u n) (W i : Set E) :=
      Metric.infDist_le_infDist_of_subset hsub ⟨0, (W i).zero_mem⟩
    have hlower : Metric.infDist (u n) (W i : Set E) ≤ Metric.infDist (u n) S := by
      apply (Metric.le_infDist hSnonempty).2
      intro y hy
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
      have hmin : Metric.infDist (u n) (W i : Set E) ≤ Metric.infDist (u n) (W j : Set E) := by
        by_cases hji : j = i
        · subst j
          exact le_rfl
        · exact (hn j hji).le
      exact hmin.trans (Metric.infDist_le_dist_of_mem hj)
    calc
      Metric.infDist (u n) S = Metric.infDist (u n) (W i : Set E) :=
        le_antisymm hupper hlower
      _ = ‖u n - P (u n)‖ := by
        rw [← (W i).dist_starProjection_eq_infDist (u n), dist_eq_norm]
  have hPlimit : Tendsto (fun n : ℕ => (‖u n‖⁻¹ : ℝ) • P (u n)) atTop (𝓝 w) := by
    have h := (P.continuous.tendsto w).comp hv
    simpa only [Function.comp_def, v, map_smul, hPw] using h
  have hnormal : Tendsto (fun n : ℕ => (‖u n‖⁻¹ : ℝ) • (u n - P (u n)))
      atTop (𝓝 (0 : E)) := by
    simpa only [v, smul_sub, sub_self] using hv.sub hPlimit
  have hnormalNorm : Tendsto (fun n : ℕ => ‖u n - P (u n)‖ / ‖u n‖)
      atTop (𝓝 0) := by
    simpa only [norm_smul, norm_inv, norm_norm, norm_zero, div_eq_mul_inv, mul_comm]
      using hnormal.norm
  refine ⟨hnearest, hnormalNorm, hPlimit, ?_⟩
  intro n
  exact Submodule.sub_starProjection_mem_orthogonal (K := W i) (u n)

end SupportedStress

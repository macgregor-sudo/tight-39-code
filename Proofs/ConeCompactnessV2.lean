module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Sequences

@[expose] public section

/-!
# Compact unit directions and a quadratic zero cone

Dependency pin: Lean 4.35.0-rc2 / Mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55.

In the intended criterion S is the union of the actual orthogonal blocks.
These two compactness facts only need the explicit zero-set identity. They do
not prove the native identity, connect nonlinear residuals to Q, or perform
the second normal-direction limit.
-/

open Filter
open scoped Topology

namespace SupportedStress

theorem positive_gap_on_unit_directions_away_from_zero_set
    {E Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z]
    (Q : E → Z) (S : Set E) (hQ : Continuous Q)
    (hzero : ∀ x : E, Q x = 0 ↔ x ∈ S)
    (η : ℝ) (hη : 0 < η) :
    ∃ m : ℝ, 0 < m ∧ ∀ x : E,
      ‖x‖ = 1 → η ≤ Metric.infDist x S → m ≤ ‖Q x‖ := by
  let K : Set E := Metric.sphere (0 : E) 1 ∩ {x | η ≤ Metric.infDist x S}
  have hK : IsCompact K :=
    (isCompact_sphere (0 : E) 1).inter_right
      (isClosed_le continuous_const (Metric.continuous_infDist_pt S))
  have hpositive : ∀ x ∈ K, (0 : ℝ) < ‖Q x‖ := by
    intro x hx
    apply norm_pos_iff.mpr
    intro hxzero
    have hdist : Metric.infDist x S = 0 :=
      Metric.infDist_zero_of_mem ((hzero x).mp hxzero)
    have hsep : η ≤ Metric.infDist x S := hx.2
    rw [hdist] at hsep
    exact (not_le_of_gt hη) hsep
  obtain ⟨m, hm, hmin⟩ := hK.exists_forall_le' hQ.norm.continuousOn hpositive
  refine ⟨m, hm, ?_⟩
  intro x hx hdist
  apply hmin x
  exact ⟨by simpa only [Metric.mem_sphere, dist_zero_right] using hx, hdist⟩

theorem normalized_quadratic_residual_subsequence
    {E Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : E → Z) (S : Set E) (hQ : Continuous Q)
    (hzero : ∀ x : E, Q x = 0 ↔ x ∈ S)
    (hhom : ∀ (t : ℝ) (x : E), Q (t • x) = t ^ 2 • Q x)
    (u : ℕ → E) (hne : ∀ n : ℕ, u n ≠ 0)
    (hsmall : Tendsto (fun n : ℕ => ‖Q (u n)‖ / ‖u n‖ ^ 2) atTop (𝓝 0)) :
    ∃ w ∈ S, ‖w‖ = 1 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n : ℕ => (‖u (φ n)‖⁻¹ : ℝ) • u (φ n)) atTop (𝓝 w) := by
  let v : ℕ → E := fun n => (‖u n‖⁻¹ : ℝ) • u n
  have hunit : ∀ n : ℕ, v n ∈ Metric.sphere (0 : E) 1 := by
    intro n
    rw [Metric.mem_sphere, dist_zero_right]
    exact norm_smul_inv_norm (hne n)
  have hnormQ : ∀ n : ℕ, ‖Q (v n)‖ = ‖Q (u n)‖ / ‖u n‖ ^ 2 := by
    intro n
    dsimp [v]
    rw [hhom, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [inv_pow, div_eq_mul_inv, mul_comm]
  have hvsmall : Tendsto (fun n : ℕ => ‖Q (v n)‖) atTop (𝓝 0) := by
    simpa only [hnormQ] using hsmall
  obtain ⟨w, hw, φ, hφ, hlim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq hunit
  have hQlim : Tendsto (fun n : ℕ => ‖Q (v (φ n))‖) atTop (𝓝 ‖Q w‖) :=
    (hQ.norm.tendsto w).comp hlim
  have hQzero : Tendsto (fun n : ℕ => ‖Q (v (φ n))‖) atTop (𝓝 0) :=
    hvsmall.comp hφ.tendsto_atTop
  have hwzero : Q w = 0 := norm_eq_zero.mp (tendsto_nhds_unique hQlim hQzero)
  refine ⟨w, (hzero w).mp hwzero, ?_, φ, hφ, ?_⟩
  · simpa only [Metric.mem_sphere, dist_zero_right] using hw
  · exact hlim

end SupportedStress

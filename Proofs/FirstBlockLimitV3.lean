module

public import LocalC2RemainderV3
public import ConeCompactnessV2
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# First block limit from an actual nonlinear residual sequence

No desired quadratic little-o conclusion is assumed.

The common-locus identities are still inputs here. The intended full criterion
derives them from exact sheet vanishing and spanning; that derivation, eventual
nearest-block selection, and the second normal-direction limit are not established in this module.
-/

open Filter
open scoped Topology

namespace SupportedStress

noncomputable def transverseQuadraticPart
    {C E Z : Type*}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : C × E → Z) (a : E) : Z :=
  (1 / 2 : ℝ) •
    (fderiv ℝ (fderiv ℝ F) (0 : C × E)) (0, a) (0, a)

def blockUnion {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (W : ι → Submodule ℝ E) : Set E := ⋃ i, (W i : Set E)

theorem nonlinear_residual_first_block_limit
    {ι C E Z : Type*}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (W : ι → Submodule ℝ E)
    (F : C × E → Z) (U : Set (C × E))
    (hU : IsOpen U) (hOrigin : (0 : C × E) ∈ U)
    (hF : ContDiffOn ℝ 2 F U)
    (hzero : ∀ c : C, (c, (0 : E)) ∈ U → F (c, 0) = 0)
    (hpartial : ∀ c : C, (c, (0 : E)) ∈ U →
      ∀ v : E, (fderiv ℝ F (c, 0)) (0, v) = 0)
    (hcone : ∀ a : E, transverseQuadraticPart F a = 0 ↔ a ∈ blockUnion W)
    (c : ℕ → C) (u : ℕ → E)
    (hc : Tendsto c atTop (𝓝 0)) (hu : Tendsto u atTop (𝓝 0))
    (haway : ∀ n : ℕ, u n ∉ blockUnion W)
    (hresidual : Tendsto (fun n : ℕ =>
      ‖F (c n, u n)‖ / Metric.infDist (u n) (blockUnion W) ^ 2) atTop (𝓝 0)) :
    ∃ (i : ι) (w : E), w ∈ W i ∧ ‖w‖ = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n : ℕ => (‖u (φ n)‖⁻¹ : ℝ) • u (φ n)) atTop (𝓝 w) := by
  let Q : E → Z := transverseQuadraticPart F
  let S : Set E := blockUnion W
  let H : (C × E) →L[ℝ] (C × E) →L[ℝ] Z :=
    fderiv ℝ (fderiv ℝ F) (0 : C × E)
  have hI : Continuous (fun a : E => ((0 : C), a)) := continuous_const.prodMk continuous_id
  have hQ : Continuous Q := by
    change Continuous (fun a : E => (1 / 2 : ℝ) • H (0, a) (0, a))
    exact continuous_const.smul ((H.continuous.comp hI).clm_apply hI)
  have hhom : ∀ (t : ℝ) (a : E), Q (t • a) = t ^ 2 • Q a := by
    intro t a
    change (1 / 2 : ℝ) • H (0, t • a) (0, t • a) =
      t ^ 2 • ((1 / 2 : ℝ) • H (0, a) (0, a))
    have hpair : ((0 : C), t • a) = t • ((0 : C), a) := by simp
    simp only [hpair, map_smul, ContinuousLinearMap.smul_apply, smul_smul]
    congr 1
    ring
  have hSrepr : S = Q ⁻¹' ({0} : Set Z) := by
    ext a
    change a ∈ S ↔ Q a = 0
    exact (hcone a).symm
  have hSclosed : IsClosed S := by
    rw [hSrepr]
    exact isClosed_singleton.preimage hQ
  have hSzero : (0 : E) ∈ S := by
    apply (hcone 0).mp
    change (1 / 2 : ℝ) • H (0 : C × E) (0 : C × E) = 0
    simp only [map_zero, zero_apply, smul_zero]
  have hSnonempty : S.Nonempty := ⟨0, hSzero⟩
  have hne : ∀ n : ℕ, u n ≠ 0 := by
    intro n hn
    apply haway n
    simpa only [hn] using hSzero
  have hdistPos : ∀ n : ℕ, 0 < Metric.infDist (u n) S := by
    intro n
    exact (hSclosed.notMem_iff_infDist_pos hSnonempty).mp (haway n)
  have hdistLe : ∀ n : ℕ, Metric.infDist (u n) S ≤ ‖u n‖ := by
    intro n
    simpa only [dist_zero_right] using
      (Metric.infDist_le_dist_of_mem (x := u n) hSzero)
  have hFnorm : Tendsto (fun n : ℕ => ‖F (c n, u n)‖ / ‖u n‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => div_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun n => ?_) hresidual
    apply div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos (hdistPos n) 2)
    nlinarith [hdistLe n, hdistPos n, norm_nonneg (u n)]
  have hQsmall : Tendsto (fun n : ℕ => ‖Q (u n)‖ / ‖u n‖ ^ 2) atTop (𝓝 0) := by
    apply tendsto_order.2
    constructor
    · intro b hb
      exact Filter.Eventually.of_forall (fun n =>
        hb.trans_le (div_nonneg (norm_nonneg _) (sq_nonneg _)))
    · intro ε hε
      obtain ⟨r, hr, hrem⟩ := local_c2_parameterized_quadratic_remainder
        F U hU hOrigin hF hzero hpartial (ε / 2) (half_pos hε)
      have hcevent : ∀ᶠ n in atTop, c n ∈ Metric.ball (0 : C) r :=
        hc.eventually (Metric.ball_mem_nhds (0 : C) hr)
      have huevent : ∀ᶠ n in atTop, u n ∈ Metric.ball (0 : E) r :=
        hu.eventually (Metric.ball_mem_nhds (0 : E) hr)
      have hFevent : ∀ᶠ n in atTop, ‖F (c n, u n)‖ / ‖u n‖ ^ 2 < ε / 2 :=
        (tendsto_order.1 hFnorm).2 (ε / 2) (half_pos hε)
      filter_upwards [hcevent, huevent, hFevent] with n hcn hun hFn
      have hcnorm : ‖c n‖ < r := by
        simpa only [Metric.mem_ball, dist_zero_right] using hcn
      have hunorm : ‖u n‖ < r := by
        simpa only [Metric.mem_ball, dist_zero_right] using hun
      have hsq : 0 < ‖u n‖ ^ 2 := pow_pos (norm_pos_iff.mpr (hne n)) 2
      have herr : ‖F (c n, u n) - Q (u n)‖ ≤ (ε / 2) * ‖u n‖ ^ 2 :=
        hrem (c n) (u n) hcnorm hunorm
      have herrRatio : ‖F (c n, u n) - Q (u n)‖ / ‖u n‖ ^ 2 ≤ ε / 2 :=
        (div_le_iff₀ hsq).2 herr
      have htriangle : ‖Q (u n)‖ ≤ ‖F (c n, u n)‖ + ‖F (c n, u n) - Q (u n)‖ := by
        have h := norm_sub_norm_le (Q (u n)) (F (c n, u n))
        rw [norm_sub_rev] at h
        linarith
      have hratio : ‖Q (u n)‖ / ‖u n‖ ^ 2 ≤
          ‖F (c n, u n)‖ / ‖u n‖ ^ 2 + ‖F (c n, u n) - Q (u n)‖ / ‖u n‖ ^ 2 := by
        simpa only [add_div] using
          (div_le_div_of_nonneg_right htriangle (sq_nonneg ‖u n‖))
      linarith
  obtain ⟨w, hwS, hwnorm, φ, hφ, hlim⟩ :=
    normalized_quadratic_residual_subsequence Q S hQ hcone hhom u hne hQsmall
  change w ∈ ⋃ i, (W i : Set E) at hwS
  obtain ⟨i, hwi⟩ := Set.mem_iUnion.mp hwS
  exact ⟨i, w, hwi, hwnorm, φ, hφ, hlim⟩

end SupportedStress

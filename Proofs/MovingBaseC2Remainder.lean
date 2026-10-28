module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Uniform quadratic remainder at a moving base

Dependency pin: Lean 4.35.0-rc2 and Mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55. Mathlib-only dependencies.

The moving-base linear term is retained. The fixed Hessian at zero, its
symmetry, and its uniform two-point derivative estimate all come from the
actual local C² map. No common-locus vanishing, completeness or ratio
assumption is used. This is one ingredient of the second normal limit,
not the full supported-stress criterion or native robustness.
-/

namespace SupportedStress

theorem local_c2_uniform_moving_base_remainder
    {E Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : E → Z) (U : Set E)
    (hU : IsOpen U) (hOrigin : (0 : E) ∈ U)
    (hF : ContDiffOn ℝ 2 F U) :
    ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧
      ∀ b v : E, ‖b‖ < r → ‖v‖ < r →
        ‖F (b + v) - F b - (fderiv ℝ F b) v - (1 / 2 : ℝ) •
          (fderiv ℝ (fderiv ℝ F) (0 : E)) v v‖ ≤ ε * ‖v‖ ^ 2 := by
  intro ε hε
  let H : E →L[ℝ] E →L[ℝ] Z := fderiv ℝ (fderiv ℝ F) (0 : E)
  have hFd : ContDiffOn ℝ 1 (fderiv ℝ F) U :=
    hF.fderiv_of_isOpen hU (by norm_num)
  have hstrict : HasStrictFDerivAt (fderiv ℝ F) H (0 : E) :=
    (hFd.contDiffAt (hU.mem_nhds hOrigin)).hasStrictFDerivAt one_ne_zero
  have hsym : ∀ v w : E, H v w = H w v :=
    (hF.contDiffAt (hU.mem_nhds hOrigin)).isSymmSndFDerivAt (by simp)
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hOrigin)
  obtain ⟨δ, hδ, hδH⟩ := Metric.mem_nhds_iff.mp (hstrict.isLittleO.def hε)
  have hbound : ∀ p b : E, ‖p‖ < δ → ‖b‖ < δ →
      ‖fderiv ℝ F p - fderiv ℝ F b - H (p - b)‖ ≤ ε * ‖p - b‖ := by
    intro p b hp hb
    have hpair : (p, b) ∈ Metric.ball ((0 : E), (0 : E)) δ := by
      change dist (p, b) (0 : E × E) < δ
      rw [dist_zero_right, Prod.norm_mk]
      exact max_lt hp hb
    exact @hδH (p, b) hpair
  let r : ℝ := min ρ δ / 2
  have hr : 0 < r := half_pos (lt_min hρ hδ)
  have hrρ : 2 * r ≤ ρ := by
    dsimp [r]
    linarith [min_le_left ρ δ]
  have hrδ : 2 * r ≤ δ := by
    dsimp [r]
    linarith [min_le_right ρ δ]
  refine ⟨r, hr, ?_⟩
  intro b v hb hv
  have hbδ : ‖b‖ < δ := by linarith
  have hnear : ∀ p ∈ Metric.closedBall b ‖v‖, ‖p‖ < ρ ∧ ‖p‖ < δ := by
    intro p hp
    have hpb : ‖p - b‖ ≤ ‖v‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hp
    have hnorm : ‖p‖ ≤ ‖v‖ + ‖b‖ := by
      calc
        ‖p‖ = ‖(p - b) + b‖ := by rw [sub_add_cancel]
        _ ≤ ‖p - b‖ + ‖b‖ := norm_add_le _ _
        _ ≤ ‖v‖ + ‖b‖ := add_le_add hpb le_rfl
    constructor <;> linarith
  let R : E → Z := fun p =>
    F p - F b - (fderiv ℝ F b) (p - b) - (1 / 2 : ℝ) • H (p - b) (p - b)
  let R' : E → E →L[ℝ] Z := fun p =>
    fderiv ℝ F p - fderiv ℝ F b - H (p - b)
  have hquad : ∀ p : E,
      HasFDerivAt (fun z : E => (1 / 2 : ℝ) • H (z - b) (z - b))
        (H (p - b)) p := by
    intro p
    have ht : HasFDerivAt (fun z : E => z - b)
        (ContinuousLinearMap.id ℝ E) p := (hasFDerivAt_id p).sub_const b
    have hq := (H.hasFDerivAt_of_bilinear ht ht).const_smul (1 / 2 : ℝ)
    apply hq.congr_fderiv
    refine ContinuousLinearMap.ext (fun (w : E) => ?_)
    change (1 / 2 : ℝ) • (H (p - b) w + H w (p - b)) = H (p - b) w
    rw [hsym w (p - b), ← two_smul ℝ, smul_smul]
    norm_num
  have hderiv : ∀ p ∈ Metric.closedBall b ‖v‖,
      HasFDerivWithinAt R (R' p) (Metric.closedBall b ‖v‖) p := by
    intro p hp
    have hpU : p ∈ U :=
      hρU (by simpa only [Metric.mem_ball, dist_zero_right] using (hnear p hp).1)
    have hdF : HasFDerivAt F (fderiv ℝ F p) p :=
      ((hF.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hpU)).hasFDerivAt
    have ht : HasFDerivAt (fun z : E => z - b)
        (ContinuousLinearMap.id ℝ E) p := (hasFDerivAt_id p).sub_const b
    have hlin : HasFDerivAt (fun z : E => (fderiv ℝ F b) (z - b))
        (fderiv ℝ F b) p := by
      simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
        ((fderiv ℝ F b).hasFDerivAt.comp p ht)
    exact (((hdF.sub_const (F b)).sub hlin).sub (hquad p)).hasFDerivWithinAt
  have hRbound : ∀ p ∈ Metric.closedBall b ‖v‖, ‖R' p‖ ≤ ε * ‖v‖ := by
    intro p hp
    have hpb : ‖p - b‖ ≤ ‖v‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hp
    exact (hbound p b (hnear p hp).2 hbδ).trans
      (mul_le_mul_of_nonneg_left hpb hε.le)
  have hbBall : b ∈ Metric.closedBall b ‖v‖ := by
    simp only [Metric.mem_closedBall, dist_self, norm_nonneg]
  have hbvdiff : b + v - b = v := add_sub_cancel_left b v
  have hbvBall : b + v ∈ Metric.closedBall b ‖v‖ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, hbvdiff] using
      (le_rfl : ‖v‖ ≤ ‖v‖)
  have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    hderiv hRbound (convex_closedBall b ‖v‖) hbBall hbvBall
  have hRzero : R b = 0 := by simp [R]
  have hRend : R (b + v) =
      F (b + v) - F b - (fderiv ℝ F b) v - (1 / 2 : ℝ) • H v v := by
    change F (b + v) - F b - (fderiv ℝ F b) (b + v - b) -
      (1 / 2 : ℝ) • H (b + v - b) (b + v - b) =
        F (b + v) - F b - (fderiv ℝ F b) v - (1 / 2 : ℝ) • H v v
    rw [hbvdiff]
  rw [hRzero, hRend, sub_zero, hbvdiff] at hmv
  simpa only [H, pow_two, mul_assoc] using hmv

end SupportedStress

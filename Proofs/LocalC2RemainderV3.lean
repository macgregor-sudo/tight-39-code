module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Relative quadratic Taylor remainder with a common parameter

Dependency pin: Lean 4.35.0-rc2 and Mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55. No LocalC1 prototype dependency.

The Hessian, its symmetry, and the uniform two-point derivative estimate are
derived from the actual C² map. Common-locus value and transverse-derivative
vanishing remain explicit inputs. This is an analytic ingredient, not native
CKM closure or the full supported-stress criterion.
-/

namespace SupportedStress

theorem local_c2_parameterized_quadratic_remainder
    {C E Z : Type*}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : C × E → Z) (U : Set (C × E))
    (hU : IsOpen U) (hOrigin : (0 : C × E) ∈ U)
    (hF : ContDiffOn ℝ 2 F U)
    (hzero : ∀ c : C, (c, (0 : E)) ∈ U → F (c, 0) = 0)
    (hpartial : ∀ c : C, (c, (0 : E)) ∈ U →
      ∀ v : E, (fderiv ℝ F (c, 0)) (0, v) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧
      ∀ (c : C) (a : E), ‖c‖ < r → ‖a‖ < r →
        ‖F (c, a) - (1 / 2 : ℝ) •
          (fderiv ℝ (fderiv ℝ F) (0 : C × E)) (0, a) (0, a)‖
          ≤ ε * ‖a‖ ^ 2 := by
  intro ε hε
  let H : (C × E) →L[ℝ] (C × E) →L[ℝ] Z :=
    fderiv ℝ (fderiv ℝ F) (0 : C × E)
  have hFd : ContDiffOn ℝ 1 (fderiv ℝ F) U :=
    hF.fderiv_of_isOpen hU (by norm_num)
  have hstrict : HasStrictFDerivAt (fderiv ℝ F) H (0 : C × E) :=
    (hFd.contDiffAt (hU.mem_nhds hOrigin)).hasStrictFDerivAt one_ne_zero
  have hsym : ∀ v w : C × E, H v w = H w v :=
    (hF.contDiffAt (hU.mem_nhds hOrigin)).isSymmSndFDerivAt (by simp)
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hOrigin)
  obtain ⟨δ, hδ, hδH⟩ := Metric.mem_nhds_iff.mp (hstrict.isLittleO.def hε)
  have hbound : ∀ p b : C × E, ‖p‖ < δ → ‖b‖ < δ →
      ‖fderiv ℝ F p - fderiv ℝ F b - H (p - b)‖ ≤ ε * ‖p - b‖ := by
    intro p b hp hb
    have hpair : (p, b) ∈ Metric.ball ((0 : C × E), (0 : C × E)) δ := by
      change dist (p, b) (0 : (C × E) × (C × E)) < δ
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
  intro c a hc ha
  let b : C × E := (c, 0)
  let v : C × E := (0, a)
  have hbNorm : ‖b‖ = ‖c‖ := by simp [b, Prod.norm_mk]
  have hvNorm : ‖v‖ = ‖a‖ := by simp [v, Prod.norm_mk]
  have hbρ : ‖b‖ < ρ := by rw [hbNorm]; linarith
  have hbδ : ‖b‖ < δ := by rw [hbNorm]; linarith
  have hbU : b ∈ U := hρU (by simpa only [Metric.mem_ball, dist_zero_right] using hbρ)
  have hnear : ∀ p ∈ Metric.closedBall b ‖a‖, ‖p‖ < ρ ∧ ‖p‖ < δ := by
    intro p hp
    have hpb : ‖p - b‖ ≤ ‖a‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hp
    have hnorm : ‖p‖ ≤ ‖a‖ + ‖c‖ := by
      calc
        ‖p‖ = ‖(p - b) + b‖ := by rw [sub_add_cancel]
        _ ≤ ‖p - b‖ + ‖b‖ := norm_add_le _ _
        _ ≤ ‖a‖ + ‖c‖ := by rw [hbNorm]; exact add_le_add hpb le_rfl
    constructor <;> linarith
  let R : C × E → Z := fun p =>
    F p - F b - (fderiv ℝ F b) (p - b) - (1 / 2 : ℝ) • H (p - b) (p - b)
  let R' : C × E → (C × E) →L[ℝ] Z := fun p =>
    fderiv ℝ F p - fderiv ℝ F b - H (p - b)
  have hquad : ∀ p : C × E,
      HasFDerivAt (fun z : C × E => (1 / 2 : ℝ) • H (z - b) (z - b))
        (H (p - b)) p := by
    intro p
    have ht : HasFDerivAt (fun z : C × E => z - b)
        (ContinuousLinearMap.id ℝ (C × E)) p := (hasFDerivAt_id p).sub_const b
    have hq := (H.hasFDerivAt_of_bilinear ht ht).const_smul (1 / 2 : ℝ)
    apply hq.congr_fderiv
    refine ContinuousLinearMap.ext (fun (w : C × E) => ?_)
    change (1 / 2 : ℝ) • (H (p - b) w + H w (p - b)) = H (p - b) w
    rw [hsym w (p - b), ← two_smul ℝ, smul_smul]
    norm_num
  have hderiv : ∀ p ∈ Metric.closedBall b ‖a‖,
      HasFDerivWithinAt R (R' p) (Metric.closedBall b ‖a‖) p := by
    intro p hp
    have hpU : p ∈ U :=
      hρU (by simpa only [Metric.mem_ball, dist_zero_right] using (hnear p hp).1)
    have hdF : HasFDerivAt F (fderiv ℝ F p) p :=
      ((hF.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hpU)).hasFDerivAt
    have ht : HasFDerivAt (fun z : C × E => z - b)
        (ContinuousLinearMap.id ℝ (C × E)) p := (hasFDerivAt_id p).sub_const b
    have hlin : HasFDerivAt (fun z : C × E => (fderiv ℝ F b) (z - b))
        (fderiv ℝ F b) p := by
      simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
        ((fderiv ℝ F b).hasFDerivAt.comp p ht)
    exact (((hdF.sub_const (F b)).sub hlin).sub (hquad p)).hasFDerivWithinAt
  have hRbound : ∀ p ∈ Metric.closedBall b ‖a‖, ‖R' p‖ ≤ ε * ‖a‖ := by
    intro p hp
    have hpb : ‖p - b‖ ≤ ‖a‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hp
    exact (hbound p b (hnear p hp).2 hbδ).trans
      (mul_le_mul_of_nonneg_left hpb hε.le)
  have hbBall : b ∈ Metric.closedBall b ‖a‖ := by
    simp only [Metric.mem_closedBall, dist_self, norm_nonneg]
  have hbvdiff : b + v - b = v := add_sub_cancel_left b v
  have hbv : b + v = (c, a) := by
    simp only [b, v, Prod.mk_add_mk, add_zero, zero_add]
  have hbvBall : b + v ∈ Metric.closedBall b ‖a‖ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, hbvdiff, hvNorm] using
      (le_rfl : ‖a‖ ≤ ‖a‖)
  have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    hderiv hRbound (convex_closedBall b ‖a‖) hbBall hbvBall
  have hFb : F b = 0 := hzero c hbU
  have hDb : (fderiv ℝ F b) v = 0 := hpartial c hbU a
  have hRzero : R b = 0 := by simp [R]
  have hRend : R (b + v) = F (c, a) - (1 / 2 : ℝ) • H (0, a) (0, a) := by
    change F (b + v) - F b - (fderiv ℝ F b) (b + v - b) -
      (1 / 2 : ℝ) • H (b + v - b) (b + v - b) =
        F (c, a) - (1 / 2 : ℝ) • H (0, a) (0, a)
    rw [hbvdiff, hFb, hDb, sub_zero, sub_zero, hbv]
  rw [hRzero, hRend, sub_zero, hbvdiff, hvNorm] at hmv
  simpa only [H, pow_two, mul_assoc] using hmv

end SupportedStress

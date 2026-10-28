module

public import BookHTQuartic
public import Mathlib.Analysis.Calculus.LineDeriv.QuadraticMap
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Mathlib.Analysis.InnerProductSpace.LinearMap

@[expose] public section

/-!
Differential interface for the unchanged literal Book quadratic maps.
The outer Blocks space retains its existing Pi norm. Its block norms are
complex Euclidean norms. No original-F or native stress identification follows.
The derivative formula reuses Mathlib's quadratic-map line derivative and its
comparison with the Frechet derivative after finite-dimensional smoothness.
-/

noncomputable section

namespace Option2.NativeStress.BookHT

open scoped InnerProductSpace ContDiff

private theorem smooth_quadratic {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : QuadraticMap ℝ E F) : ContDiff ℝ ∞ Q := by
  let B := Q.associated.toContinuousBilinearMap
  have h : (fun x => B x x) = Q := by
    funext x
    exact Q.associated_eq_self_apply ℝ x
  rw [← h]
  exact B.contDiff.clm_apply contDiff_id

/-- C-infinity regularity of the actual H, without a supplied regularity premise. -/
theorem contDiff_H : ContDiff ℝ ∞ H := smooth_quadratic H

/-- C-infinity regularity of the actual T. -/
theorem contDiff_T : ContDiff ℝ ∞ T := smooth_quadratic T

theorem contDiff_sigma : ContDiff ℝ ∞ sigma := smooth_quadratic sigma

/-- The derivative is the full polar cross term, with no factor of one-half. -/
theorem fderiv_H_apply (w n : Blocks) :
    (fderiv ℝ H w) n = QuadraticMap.polar H w n := by
  rw [← (contDiff_H.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv,
    QuadraticMap.lineDeriv]

theorem fderiv_T_apply (w n : Blocks) :
    (fderiv ℝ T w) n = QuadraticMap.polar T w n := by
  rw [← (contDiff_T.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv,
    QuadraticMap.lineDeriv]

/-- The real stress, as an actual continuous linear functional on H's target. -/
def stressFunctional (i : Fin 4) (w : Blocks) : Blocks →L[ℝ] ℝ :=
  (3 : ℝ) • (innerSL ℝ (sigma (w i))).comp (ContinuousLinearMap.proj i)

@[simp] theorem stressFunctional_apply (i : Fin 4) (w q : Blocks) :
    stressFunctional i w q = 3 * ⟪sigma (w i), q i⟫_ℝ := rfl

/-- Continuity into the continuous dual, in its operator norm topology. -/
theorem continuous_stressFunctional (i : Fin 4) : Continuous (stressFunctional i) := by
  have hs : Continuous (fun w : Blocks => sigma (w i)) :=
    contDiff_sigma.continuous.comp (continuous_apply i)
  have hi : Continuous (fun w : Blocks => innerSL ℝ (sigma (w i))) :=
    (innerSL ℝ (E := Triple)).continuous.comp hs
  change Continuous (fun w : Blocks => (3 : ℝ) •
    (innerSL ℝ (sigma (w i))).comp (ContinuousLinearMap.proj i : Blocks →L[ℝ] Triple))
  have hc : Continuous (fun _ : Blocks =>
      (ContinuousLinearMap.proj i : Blocks →L[ℝ] Triple)) := continuous_const
  exact (hi.clm_comp hc).const_smul (3 : ℝ)

theorem derivative_kernel_stress_identity (i : Fin 4) (w n : Blocks)
    (hw : FourBlock.OnAxis i w) (hn : n i = 0)
    (hH : (fderiv ℝ H w) n = 0) (hT : (fderiv ℝ T w) n = 0) :
    stressFunctional i w (H n) = ‖w i‖ ^ 2 * FourBlock.totalSquaredLength n := by
  exact kernel_stress_identity i w n hw hn
    ((fderiv_H_apply w n).symm.trans hH) ((fderiv_T_apply w n).symm.trans hT)

theorem derivative_kernel_stress_pos (i : Fin 4) (w n : Blocks)
    (hw : FourBlock.OnAxis i w) (hn : n i = 0) (hw0 : w ≠ 0) (hn0 : n ≠ 0)
    (hH : (fderiv ℝ H w) n = 0) (hT : (fderiv ℝ T w) n = 0) :
    0 < stressFunctional i w (H n) := by
  exact kernel_stress_pos i w n hw hn hw0 hn0
    ((fderiv_H_apply w n).symm.trans hH) ((fderiv_T_apply w n).symm.trans hT)

theorem derivative_kernel_eq_zero_of_sigma_eq_zero (i : Fin 4) (w n : Blocks)
    (hw : FourBlock.OnAxis i w) (hn : n i = 0) (hw0 : w ≠ 0)
    (hsigma : sigma (w i) = 0)
    (hH : (fderiv ℝ H w) n = 0) (hT : (fderiv ℝ T w) n = 0) : n = 0 :=
  kernel_eq_zero_of_sigma_eq_zero i w n hw hn hw0 hsigma
    ((fderiv_H_apply w n).symm.trans hH) ((fderiv_T_apply w n).symm.trans hT)

end Option2.NativeStress.BookHT

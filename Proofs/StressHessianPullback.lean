module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
Second-order pullback under an annihilating continuous real-linear stress.
The Hessian is exactly `fderiv ℝ (fderiv ℝ f)`. The nonlinear chart's
acceleration term is derived first and removed only by the explicit stress
annihilation hypothesis. No chart affinity or second-chain formula is assumed.
-/

namespace SupportedStress.HessianPullback

open Filter
open scoped Topology

variable {E F Z W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The actual second chain rule, obtained by differentiating the first chain
rule on a neighborhood. The first summand records nonlinear chart acceleration. -/
theorem second_chain_rule_zero (f : F → Z) (g : E → F)
    (hf : ContDiffAt ℝ 2 f (g 0)) (hg : ContDiffAt ℝ 2 g 0) (u v : E) :
    (fderiv ℝ (fderiv ℝ (f ∘ g)) 0) u v =
      (fderiv ℝ f (g 0)) ((fderiv ℝ (fderiv ℝ g) 0) u v) +
      (fderiv ℝ (fderiv ℝ f) (g 0))
        ((fderiv ℝ g 0) u) ((fderiv ℝ g 0) v) := by
  have hgd : DifferentiableAt ℝ g 0 := hg.differentiableAt (by norm_num)
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) (g 0) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hgdd : DifferentiableAt ℝ (fderiv ℝ g) 0 :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hnear : fderiv ℝ (f ∘ g) =ᶠ[𝓝 (0 : E)]
      (fun x => (fderiv ℝ f (g x)).comp (fderiv ℝ g x)) := by
    have hfn := hg.continuousAt.eventually (hf.eventually (by norm_num))
    filter_upwards [hfn, hg.eventually (by norm_num)] with x hfx hgx
    exact fderiv_comp x (hfx.differentiableAt (by norm_num))
      (hgx.differentiableAt (by norm_num))
  have hcomposition := hfd.hasFDerivAt.comp 0 hgd.hasFDerivAt
  have hproduct := hcomposition.clm_comp hgdd.hasFDerivAt
  have hproduct_eq := hproduct.fderiv
  dsimp only [Function.comp_def] at hproduct_eq
  rw [hnear.fderiv_eq, hproduct_eq]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]

/-- A stress that kills the full first derivative removes the chart acceleration
term. The chart may be nonlinear; the stress may take values in any real normed space. -/
theorem stress_hessian_pullback_zero (f : F → Z) (g : E → F)
    (ell : Z →L[ℝ] W)
    (hf : ContDiffAt ℝ 2 f (g 0)) (hg : ContDiffAt ℝ 2 g 0)
    (hann : ell.comp (fderiv ℝ f (g 0)) = 0) (u v : E) :
    ell ((fderiv ℝ (fderiv ℝ (f ∘ g)) 0) u v) =
      ell ((fderiv ℝ (fderiv ℝ f) (g 0))
        ((fderiv ℝ g 0) u) ((fderiv ℝ g 0) v)) := by
  rw [second_chain_rule_zero f g hf hg, map_add]
  have hz : ell ((fderiv ℝ f (g 0))
      ((fderiv ℝ (fderiv ℝ g) 0) u v)) = 0 := by
    change (ell.comp (fderiv ℝ f (g 0))) _ = 0
    rw [hann]
    rfl
  rw [hz, zero_add]

/-- Open-neighborhood form: the source neighborhood is at zero and the target
neighborhood is at `g 0`; no global image-containment hypothesis is needed. -/
theorem stress_hessian_pullback_on (f : F → Z) (g : E → F)
    (ell : Z →L[ℝ] W) (U : Set F) (V : Set E)
    (hU : IsOpen U) (hV : IsOpen V) (hbase : g 0 ∈ U) (hzero : (0 : E) ∈ V)
    (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g V)
    (hann : ell.comp (fderiv ℝ f (g 0)) = 0) (u v : E) :
    ell ((fderiv ℝ (fderiv ℝ (f ∘ g)) 0) u v) =
      ell ((fderiv ℝ (fderiv ℝ f) (g 0))
        ((fderiv ℝ g 0) u) ((fderiv ℝ g 0) v)) :=
  stress_hessian_pullback_zero f g ell (hf.contDiffAt (hU.mem_nhds hbase))
    (hg.contDiffAt (hV.mem_nhds hzero)) hann u v

/-- Diagonal half-quadratic coefficient, using the same actual Hessian. -/
theorem stress_half_quadratic_pullback_zero (f : F → Z) (g : E → F)
    (ell : Z →L[ℝ] W)
    (hf : ContDiffAt ℝ 2 f (g 0)) (hg : ContDiffAt ℝ 2 g 0)
    (hann : ell.comp (fderiv ℝ f (g 0)) = 0) (u : E) :
    ell ((1 / 2 : ℝ) • (fderiv ℝ (fderiv ℝ (f ∘ g)) 0) u u) =
      (1 / 2 : ℝ) • ell ((fderiv ℝ (fderiv ℝ f) (g 0))
        ((fderiv ℝ g 0) u) ((fderiv ℝ g 0) u)) := by
  rw [map_smul, stress_hessian_pullback_zero f g ell hf hg hann u u]

end SupportedStress.HessianPullback

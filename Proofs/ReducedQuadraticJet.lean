module

public import StressHessianPullback
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

@[expose] public section

/-! Light coefficient and germ interfaces; the second chain rule is imported unchanged. -/
noncomputable section
namespace SupportedStress.ReducedQuadratic
open scoped Topology
variable {E F Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem second_comp_linear (f : F → Z) (L : E →L[ℝ] F)
    (hf : ContDiffAt ℝ 2 f 0) (u v : E) :
    fderiv ℝ (fderiv ℝ (f ∘ L)) 0 u v =
      fderiv ℝ (fderiv ℝ f) 0 (L u) (L v) := by
  have h := HessianPullback.second_chain_rule_zero f L
    (by simpa only [map_zero] using hf) L.contDiff.contDiffAt u v
  have hL : fderiv ℝ L = (fun _ => L) := funext fun x => L.fderiv
  rw [hL] at h
  simpa using h

theorem second_zero_of_linear_germ (f : F → Z) (L : E →L[ℝ] F)
    (hf : ContDiffAt ℝ 2 f 0)
    (hz : (f ∘ L) =ᶠ[𝓝 0] (fun _ => 0)) (u v : E) :
    fderiv ℝ (fderiv ℝ f) 0 (L u) (L v) = 0 := by
  rw [← second_comp_linear f L hf u v, hz.fderiv.fderiv_eq]
  simp

theorem second_post_linear (f : E → F) (L : F →L[ℝ] Z)
    (hf : ContDiffAt ℝ 2 f 0) (u v : E) :
    fderiv ℝ (fderiv ℝ (L ∘ f)) 0 u v =
      L (fderiv ℝ (fderiv ℝ f) 0 u v) := by
  have h := HessianPullback.second_chain_rule_zero L f L.contDiff.contDiffAt hf u v
  have hL : fderiv ℝ L = (fun _ => L) := funext fun x => L.fderiv
  rw [hL] at h
  simpa using h

theorem half_hessian_quadratic [FiniteDimensional ℝ E]
    (Q : QuadraticMap ℝ E Z) (z : E) :
    (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ Q) 0 z z = Q z := by
  letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  let B : E →L[ℝ] E →L[ℝ] Z := Q.associated.toContinuousBilinearMap
  have hQ : (fun x => B x x) = Q := by
    funext x
    exact Q.associated_eq_self_apply ℝ x
  have hd (x : E) : HasFDerivAt Q (B x + B.flip x) x := by
    rw [← hQ]
    convert B.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x) using 1 <;>
      ext y <;> simp
  have he : fderiv ℝ Q = (fun x => (B + B.flip) x) := by
    funext x
    exact (hd x).fderiv
  rw [he, ContinuousLinearMap.fderiv]
  change (1 / 2 : ℝ) • (B z z + B z z) = Q z
  rw [← two_smul ℝ, smul_smul]
  norm_num
  exact congrFun hQ z

end SupportedStress.ReducedQuadratic

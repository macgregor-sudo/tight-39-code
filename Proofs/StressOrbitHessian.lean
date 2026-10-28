module

public import StressHessianPullback
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section

namespace SupportedStress.OrbitHessian

variable {E Z W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Differentiating an infinitesimal covariance identity gives the mixed
Hessian identity. No Hessian equality is supplied as a hypothesis. -/
theorem mixed_stress_zero (f : E → Z) (B : E →L[ℝ] E) (R : Z →L[ℝ] Z)
    (hf : ContDiff ℝ 2 f)
    (hcov : ∀ y, (fderiv ℝ f y) (B y) = R (f y))
    (x v : E) (ell : Z →L[ℝ] W)
    (hv : (fderiv ℝ f x) v = 0)
    (hann : ell.comp (fderiv ℝ f x) = 0) :
    ell ((fderiv ℝ (fderiv ℝ f) x) v (B x)) = 0 := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hleft := hdf.hasFDerivAt.clm_apply B.hasFDerivAt
  have hright := R.hasFDerivAt.comp x
    ((hf.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt)
  have heq : (fun y => (fderiv ℝ f y) (B y)) = fun y => R (f y) := funext hcov
  rw [heq] at hleft
  have hd := congrArg (fun L : E →L[ℝ] Z => L v) (hleft.unique hright)
  have hid : (fderiv ℝ f x) (B v) +
      (fderiv ℝ (fderiv ℝ f) x) v (B x) = R ((fderiv ℝ f x) v) := by
    simpa only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply] using hd
  have hkill : ell ((fderiv ℝ f x) (B v)) = 0 := by
    change (ell.comp (fderiv ℝ f x)) (B v) = 0
    rw [hann]
    rfl
  have hzero := congrArg ell hid
  simpa only [map_add, hkill, zero_add, hv, map_zero] using hzero

/-- A stationary stress Hessian on the derivative kernel is unchanged when
an infinitesimal symmetry direction is subtracted. -/
theorem sub_orbit_invariant (f : E → Z) (B : E →L[ℝ] E) (R : Z →L[ℝ] Z)
    (hf : ContDiff ℝ 2 f)
    (hcov : ∀ y, (fderiv ℝ f y) (B y) = R (f y))
    (x v : E) (ell : Z →L[ℝ] W) (hx : f x = 0)
    (hv : (fderiv ℝ f x) v = 0)
    (hann : ell.comp (fderiv ℝ f x) = 0) :
    ell ((fderiv ℝ (fderiv ℝ f) x) (v - B x) (v - B x)) =
      ell ((fderiv ℝ (fderiv ℝ f) x) v v) := by
  have ho : (fderiv ℝ f x) (B x) = 0 := by rw [hcov x, hx, map_zero]
  have hvo := mixed_stress_zero f B R hf hcov x v ell hv hann
  have hoo := mixed_stress_zero f B R hf hcov x (B x) ell ho hann
  have hsym : IsSymmSndFDerivAt ℝ f x :=
    hf.contDiffAt.isSymmSndFDerivAt (by norm_num)
  have hov : ell ((fderiv ℝ (fderiv ℝ f) x) (B x) v) = 0 := by
    rw [hsym (B x) v]
    exact hvo
  simp only [map_sub, sub_apply, hvo, hov, hoo, sub_zero]

end SupportedStress.OrbitHessian

#print axioms SupportedStress.OrbitHessian.mixed_stress_zero
#print axioms SupportedStress.OrbitHessian.sub_orbit_invariant

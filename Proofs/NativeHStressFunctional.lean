module

public import NativeHAnchorSupport
public import OriginalFAnalyticDerivativeV2
public import BookHTDifferential

@[expose] public section

/-!
The twelve literal original-row covectors, packaged in the Book target with
its existing complex Euclidean block norms and outer Pi norm. Each component
reuses the accepted continuous REAL-linear stressCovector. This does not
identify its quadratic reproduction with Book H or assert native equilibrium.
The derivative transfer retains the exact remaining equilibrium and anchor
matching premises and uses the actual originalF on all 39 by 27 coordinates.
-/

noncomputable section

namespace Option2.NativeStress.NativeH

open scoped BigOperators InnerProductSpace
open AnalyticDerivative AnchorSupport NativePolynomial.PartialAction PolynomialJets

/-- All twelve H covectors, with no truncation of the 2184 original rows. -/
def residualContraction : RealResiduals →L[ℝ] BookHT.Blocks :=
  ContinuousLinearMap.pi fun i =>
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun a => stressCovector (weightC i a))

theorem residualContraction_apply (q : RealResiduals) (i : Fin 4) (a : Fin 3) :
    residualContraction q i a = ∑ r : Fin 2184, weightC i a r * (q r : ℂ) :=
  stressCovector_apply (weightC i a) q

/-- The accepted sparse-list formula retains its exact signs and conjugations. -/
theorem residualContraction_apply_sparse (q : RealResiduals) (i : Fin 4) (a : Fin 3) :
    residualContraction q i a =
      ((hEntries i a).map fun e => e.2 * (q e.1 : ℂ)).sum := by
  rw [residualContraction_apply, weightC_dense_sparse]

/-- An actual real continuous functional on the original residual space. -/
def realStressFunctional (i : Fin 4) (w : BookHT.Blocks) : RealResiduals →L[ℝ] ℝ :=
  (BookHT.stressFunctional i w).comp residualContraction

theorem realStressFunctional_apply (i : Fin 4) (w : BookHT.Blocks) (q : RealResiduals) :
    realStressFunctional i w q =
      3 * ⟪BookHT.sigma (w i), residualContraction q i⟫_ℝ := rfl

/-- Hermitian pairing, with conjugation on sigma and the full factor three. -/
theorem realStressFunctional_apply_hermitian
    (i : Fin 4) (w : BookHT.Blocks) (q : RealResiduals) :
    realStressFunctional i w q = 3 *
      (∑ a : Fin 3, star (BookHT.sigma (w i) a) *
        ∑ r : Fin 2184, weightC i a r * (q r : ℂ)).re := by
  rw [realStressFunctional_apply]
  congr 1
  have h (u v : BookHT.Triple) :
      ⟪u, v⟫_ℝ = (∑ a : Fin 3, star (u a) * v a).re := by
    simp [PiLp.inner_apply, real_inner_eq_re_inner, RCLike.inner_apply,
      Fin.sum_univ_succ, mul_comm]
  simpa only [residualContraction_apply] using h (BookHT.sigma (w i))
    (residualContraction q i)

/-- Continuity in the continuous-dual operator norm, rather than pointwise only. -/
theorem continuous_realStressFunctional (i : Fin 4) :
    Continuous (realStressFunctional i) :=
  (BookHT.continuous_stressFunctional i).clm_comp continuous_const

/-- Componentwise complex annihilation transfers to the actual real derivative.
This is a transfer, not a proof of the component annihilation premise. -/
theorem realStress_comp_fderiv_eq_zero_of_components
    (i : Fin 4) (w : BookHT.Blocks) (C : RealConfiguration)
    (h : ∀ a : Fin 3,
      (stressCovector (weightC i a)).comp (fderiv ℝ originalF C) = 0) :
    (realStressFunctional i w).comp (fderiv ℝ originalF C) = 0 := by
  ext W
  change realStressFunctional i w (fderiv ℝ originalF C W) = 0
  have hz : residualContraction (fderiv ℝ originalF C W) i = 0 := by
    ext a
    exact congrArg (fun L : RealConfiguration →L[ℝ] ℂ => L W) (h a)
  rw [realStressFunctional_apply, hz, inner_zero_right, mul_zero]

/-- Native support is already proved. Only the exact base solution, selected
three component equilibrium identities, and anchor agreement are premises.
No equation at C and no restriction on tested ambient directions is assumed. -/
theorem realStress_comp_fderiv_originalF_eq_zero
    (P C : RealConfiguration) (i : Fin 4) (w : BookHT.Blocks)
    (hP : ∀ r : Fin 2184, originalF P r = 0)
    (hL : ∀ (a : Fin 3) (c : Fin 1053),
      ∑ r : Fin 2184, weightC i a r *
        equationLinearMatrix (translatedRow (complexPack P)) r c = 0)
    (hanchor : ∀ v, AnchorCoordinate i v → pack C v = pack P v) :
    (realStressFunctional i w).comp (fderiv ℝ originalF C) = 0 := by
  apply realStress_comp_fderiv_eq_zero_of_components i w C
  intro a
  exact stress_comp_fderiv_originalF_eq_zero P C (weightC i a) i
    hP (hL a) (hasAnchorSupport (complexPack P) i a) hanchor

/-- The scalar Hermitian sum vanishes on every actual original-F derivative output. -/
theorem realStress_all_real_directions_annihilated
    (P C W : RealConfiguration) (i : Fin 4) (w : BookHT.Blocks)
    (hP : ∀ r : Fin 2184, originalF P r = 0)
    (hL : ∀ (a : Fin 3) (c : Fin 1053),
      ∑ r : Fin 2184, weightC i a r *
        equationLinearMatrix (translatedRow (complexPack P)) r c = 0)
    (hanchor : ∀ v, AnchorCoordinate i v → pack C v = pack P v) :
    3 * (∑ a : Fin 3, star (BookHT.sigma (w i) a) *
      ∑ r : Fin 2184, weightC i a r * (fderiv ℝ originalF C W r : ℂ)).re = 0 := by
  rw [← realStressFunctional_apply_hermitian]
  exact congrArg (fun L : RealConfiguration →L[ℝ] ℝ => L W)
    (realStress_comp_fderiv_originalF_eq_zero P C i w hP hL hanchor)

end Option2.NativeStress.NativeH

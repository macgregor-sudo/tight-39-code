module

public import BookNativeReducedQuadratic
public import NativeOrbitStressJetConsumer

@[expose] public section

/-! Exact native nonlinear-to-affine transfer. Reproduction inputs remain explicit until their heavy closure qualifies. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.BookHT.ReducedQuadratic
open SheetReduction NativeNormalKernelBridge TangentCoordinates
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeSliceImplicitReduction
open NativePolynomial QuadraticCertificate.ExactCKMConfiguration
open SupportedStress.ReducedQuadratic SupportedStress.HessianPullback

def affineBook (z : Blocks) : Cfg := literalCfg exactPhases + bookDirection z
def affineResidual (z : Blocks) : Residual :=
  Option2.NativeStress.originalF (Option2.BookNativeBase.bookBase + realV z)

@[simp] theorem affineBook_zero : affineBook 0 = literalCfg exactPhases := by
  rw [affineBook, map_zero, add_zero]

theorem affineBook_derivative (z : Blocks) : HasFDerivAt affineBook bookDirection z := by
  exact bookDirection.hasFDerivAt.const_add (literalCfg exactPhases)

theorem affineBook_C2 : ContDiff ℝ 2 affineBook :=
  contDiff_const.add bookDirection.contDiff

theorem pack_affineBook (z : Blocks) :
    PartialAction.pack (affineBook z) = Option2.BookNativeBase.bookBase + realV z := by
  change PartialAction.pack (literalCfg exactPhases) + PartialAction.pack (bookDirection z) = _
  rw [TangentCoordinates.pack_literalCfg_exactPhases, pack_bookDirection]

/-- Both native coordinate presentations retain all 2184 literal original rows. -/
theorem affineResidual_native : affineResidual = AnalyticDerivative.originalF ∘ affineBook := by
  funext z
  change Option2.NativeStress.originalF (Option2.BookNativeBase.bookBase + realV z) =
    Option2.NativeStress.originalF (PartialAction.pack (affineBook z))
  rw [pack_affineBook]

theorem affineResidual_C2 : ContDiffAt ℝ 2 affineResidual 0 := by
  rw [affineResidual_native]
  exact (AnalyticDerivative.originalF_contDiff 2).contDiffAt.comp 0 affineBook_C2.contDiffAt

theorem stress_reducedQuadratic_eq_affine {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] (ell : Residual →L[ℝ] W)
    (hann : ell.comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases)) = 0)
    (z : Blocks) :
    ell (reducedQuadratic z) = ell ((1/2 : ℝ) •
      fderiv ℝ (fderiv ℝ affineResidual) 0 z z) := by
  rw [stress_reducedQuadratic ell hann,
    NativeOrbitStressJet.bookDirection_normalProjection_hessian z ell hann]
  have h := stress_half_quadratic_pullback_zero AnalyticDerivative.originalF affineBook ell
    (AnalyticDerivative.originalF_contDiff 2).contDiffAt affineBook_C2.contDiffAt
    (by simpa only [affineBook_zero] using hann) z
  simpa only [← affineResidual_native, affineBook_zero, (affineBook_derivative 0).fderiv] using h.symm

/-- Exact reproduction is an input here, not an assumed cone or rank statement. -/
theorem stress_reducedQuadratic_of_reproduction {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] (ell : Residual →L[ℝ] W)
    (Q : QuadraticMap ℝ Blocks W)
    (hann : ell.comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases)) = 0)
    (hrepro : ∀ z, ell (Option2.NativeStress.originalF
      (Option2.BookNativeBase.bookBase + realV z)) = Q z) (z : Blocks) :
    ell (reducedQuadratic z) = Q z := by
  rw [stress_reducedQuadratic_eq_affine ell hann, map_smul,
    ← second_post_linear affineResidual ell affineResidual_C2]
  have he : ell ∘ affineResidual = Q := funext hrepro
  rw [he]
  exact half_hessian_quadratic Q z

/-- The full reduced quadratic cone follows from two exact reproductions and actual sheet vanishing.
This theorem is conditional on the displayed native input identities; it is not the assembled H/T endpoint. -/
theorem reducedQuadratic_zero_cone_of_reproduction
    (ellH ellT : Residual →L[ℝ] Blocks)
    (hannH : ellH.comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases)) = 0)
    (hannT : ellT.comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases)) = 0)
    (hreproH : ∀ z, ellH (Option2.NativeStress.originalF
      (Option2.BookNativeBase.bookBase + realV z)) = H z)
    (hreproT : ∀ z, ellT (Option2.NativeStress.originalF
      (Option2.BookNativeBase.bookBase + realV z)) = T z) (z : Blocks) :
    reducedQuadratic z = 0 ↔ ∃ i, FourBlock.OnAxis i z := by
  constructor
  · intro hz
    apply (zero_cone z).1
    constructor
    · rw [← stress_reducedQuadratic_of_reproduction ellH H hannH hreproH z, hz, map_zero]
    · rw [← stress_reducedQuadratic_of_reproduction ellT T hannT hreproT z, hz, map_zero]
  · rintro ⟨i, hi⟩
    exact reducedQuadratic_axis i z hi

end Option2.NativeStress.BookHT.ReducedQuadratic

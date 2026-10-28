module

public import BookNativeSheetReduction
public import ReducedQuadraticJet

@[expose] public section

/-! The actual reduced half-Hessian and its native embedding. No H/T reproduction is assumed here. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.BookHT.ReducedQuadratic
open SheetReduction NativeNormalKernelBridge TangentCoordinates
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeSliceImplicitReduction
open NativePolynomial QuadraticCertificate.ExactCKMConfiguration
open SupportedStress.ReducedQuadratic SupportedStress.HessianPullback
open scoped Topology

def nativeEmbedding (x : KernelModel) : Cfg :=
  literalCfg exactPhases + (reducedEmbedding x : Cfg)

@[simp] theorem nativeEmbedding_zero : nativeEmbedding 0 = literalCfg exactPhases := by
  simp [nativeEmbedding]

theorem nativeEmbedding_C2 : ContDiffAt ℝ 2 nativeEmbedding 0 :=
  contDiffAt_const.add ((normalC exactPhases).subtypeL.contDiff.contDiffAt.comp 0 reducedEmbedding_C2)

def nativeEmbeddingDerivative : KernelModel →L[ℝ] Cfg :=
  (normalC exactPhases).subtypeL.comp embeddingDerivative

theorem nativeEmbedding_derivative : HasFDerivAt nativeEmbedding nativeEmbeddingDerivative 0 := by
  change HasFDerivAt (fun x : KernelModel => literalCfg exactPhases +
    (normalC exactPhases).subtypeL (reducedEmbedding x))
    ((normalC exactPhases).subtypeL.comp embeddingDerivative) 0
  exact ((normalC exactPhases).subtypeL.hasFDerivAt.comp 0
    reducedEmbedding_derivative).const_add (literalCfg exactPhases)

theorem nativeEmbedding_Book_derivative (z : Blocks) :
    fderiv ℝ nativeEmbedding 0 (0,z) = (normalProjection (bookDirection z) : Cfg) := by
  rw [nativeEmbedding_derivative.fderiv]
  simp [nativeEmbeddingDerivative, embeddingDerivative, bookNormal]

theorem sheetResidual_native : sheetResidual = AnalyticDerivative.originalF ∘ nativeEmbedding := rfl

/-- The actual full 2184-row reduced quadratic on the 24 real Book coordinates. -/
def reducedQuadratic (z : Blocks) : Residual :=
  (1/2 : ℝ) • fderiv ℝ (fderiv ℝ sheetResidual) 0 (0,z) (0,z)

def sheetAxis (i : Fin 4) : (Common × Triple) →L[ℝ] KernelModel :=
  (ContinuousLinearMap.fst ℝ Common Triple).prod
    ((ContinuousLinearMap.single ℝ (fun _ : Fin 4 => Triple) i).comp
      (ContinuousLinearMap.snd ℝ Common Triple))

theorem reducedQuadratic_single (i : Fin 4) (z : Triple) :
    reducedQuadratic (Pi.single i z) = 0 := by
  have h := second_zero_of_linear_germ sheetResidual (sheetAxis i) sheetResidual_C2
    (sheetResidual_family_zero i) (0,z) (0,z)
  change fderiv ℝ (fderiv ℝ sheetResidual) 0 (0,Pi.single i z) (0,Pi.single i z) = 0 at h
  simp only [reducedQuadratic, h, smul_zero]

theorem reducedQuadratic_axis (i : Fin 4) (z : Blocks) (hz : FourBlock.OnAxis i z) :
    reducedQuadratic z = 0 := by
  have he : Pi.single i (z i) = z := by
    ext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Pi.single_apply, hj, hz j hj]
  rw [← he]
  exact reducedQuadratic_single i (z i)

/-- Only full native derivative annihilation removes the nonlinear acceleration. -/
theorem stress_reducedQuadratic {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (ell : Residual →L[ℝ] W)
    (hann : ell.comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases)) = 0)
    (z : Blocks) :
    ell (reducedQuadratic z) = (1/2 : ℝ) • ell
      (fderiv ℝ (fderiv ℝ AnalyticDerivative.originalF) (literalCfg exactPhases)
        (normalProjection (bookDirection z) : Cfg) (normalProjection (bookDirection z) : Cfg)) := by
  have h := stress_half_quadratic_pullback_zero AnalyticDerivative.originalF nativeEmbedding ell
    ((AnalyticDerivative.originalF_contDiff 2).contDiffAt) nativeEmbedding_C2
    (by simpa only [nativeEmbedding_zero] using hann) (0,z)
  simpa only [← sheetResidual_native, nativeEmbedding_zero, nativeEmbedding_Book_derivative,
    reducedQuadratic] using h

end Option2.NativeStress.BookHT.ReducedQuadratic

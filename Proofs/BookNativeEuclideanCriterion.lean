module

public import BookNativeEuclideanSheetDistance
public import BookNativeReducedQuadratic

@[expose] public section

noncomputable section
namespace Option2.NativeStress.BookHT.EuclideanCriterion
open SheetReduction BookOrthogonal
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeSliceNormalSplitting CKM.NativeSliceImplicitReduction
open QuadraticCertificate.ExactCKMConfiguration Filter Topology

abbrev EuclideanModel := Common × BookOrthogonal.E

/-- The actual real-linear coordinate change; no isometry is assumed. -/
def euclideanCoordinates : EuclideanModel →L[ℝ] KernelModel :=
  (ContinuousLinearMap.fst ℝ Common BookOrthogonal.E).prod
    ((toBlocks : BookOrthogonal.E →L[ℝ] Blocks).comp
      (ContinuousLinearMap.snd ℝ Common BookOrthogonal.E))

@[simp] theorem euclideanCoordinates_apply (p : EuclideanModel) :
    euclideanCoordinates p = (p.1, toBlocks p.2) := rfl

/-- The unchanged full 2184-row reduced residual, now on the inner-product domain. -/
def fE (p : EuclideanModel) : Residual := sheetResidual (euclideanCoordinates p)

/-- Actual native embedding at the exact seed, retaining the nonlinear chart. -/
def embeddingE (p : EuclideanModel) : Cfg :=
  ReducedQuadratic.nativeEmbedding (euclideanCoordinates p)

theorem embeddingE_native (p : EuclideanModel) :
    embeddingE p = literalCfg exactPhases +
      (reducedEmbedding (p.1, toBlocks p.2) : Cfg) := rfl

theorem fE_originalF : fE = AnalyticDerivative.originalF ∘ embeddingE := rfl

@[simp] theorem embeddingE_zero : embeddingE 0 = literalCfg exactPhases := by
  simp only [embeddingE, map_zero, ReducedQuadratic.nativeEmbedding_zero]

@[simp] theorem fE_zero : fE 0 = 0 := by
  simp only [fE, map_zero, sheetResidual_zero]

theorem fE_C2 : ContDiffAt ℝ 2 fE 0 := by
  have hf : ContDiffAt ℝ 2 sheetResidual (euclideanCoordinates 0) := by
    simpa only [map_zero] using sheetResidual_C2
  exact hf.comp 0 euclideanCoordinates.contDiff.contDiffAt

theorem embeddingE_C2 : ContDiffAt ℝ 2 embeddingE 0 := by
  have hf : ContDiffAt ℝ 2 ReducedQuadratic.nativeEmbedding (euclideanCoordinates 0) := by
    simpa only [map_zero] using ReducedQuadratic.nativeEmbedding_C2
  exact hf.comp 0 euclideanCoordinates.contDiff.contDiffAt

theorem fE_fderiv_zero : fderiv ℝ fE 0 = 0 := by
  have hf : DifferentiableAt ℝ sheetResidual (euclideanCoordinates 0) := by
    simpa only [map_zero] using sheetResidual_derivative_zero.differentiableAt
  change fderiv ℝ (sheetResidual ∘ euclideanCoordinates) 0 = 0
  rw [fderiv_comp 0 hf euclideanCoordinates.differentiableAt]
  simp only [map_zero, sheetResidual_derivative_zero.fderiv, ContinuousLinearMap.zero_comp]

/-- Exact half-Hessian identity using the already-proved second linear chain rule. -/
theorem transverseQuadraticPart_fE (x : BookOrthogonal.E) :
    SupportedStress.transverseQuadraticPart fE x =
      ReducedQuadratic.reducedQuadratic (toBlocks x) := by
  have h := SupportedStress.ReducedQuadratic.second_comp_linear
    sheetResidual euclideanCoordinates sheetResidual_C2
    ((0 : Common), x) ((0 : Common), x)
  change (1/2 : ℝ) • fderiv ℝ (fderiv ℝ (sheetResidual ∘ euclideanCoordinates))
    0 (0,x) (0,x) = _
  rw [h]
  rfl

/-- Pull back the genuine native sheet germ to each actual orthogonal W axis. -/
theorem fE_axis_zero_near (H : Fin 4) :
    ∀ᶠ p : EuclideanModel in 𝓝 0, p.2 ∈ W H → fE p = 0 := by
  have hc : Continuous (fun p : EuclideanModel => (p.1, toBlocks p.2 H)) :=
    continuous_fst.prodMk ((continuous_apply H).comp (toBlocks.continuous.comp continuous_snd))
  have ht : Tendsto (fun p : EuclideanModel => (p.1, toBlocks p.2 H))
      (𝓝 0) (𝓝 (0 : Common × Triple)) := by
    simpa only [Prod.fst_zero, Prod.snd_zero, map_zero, Pi.zero_apply, Prod.mk_zero_zero]
      using hc.continuousAt.tendsto (x := 0)
  filter_upwards [ht.eventually (sheetResidual_family_zero H)] with p hp hx
  have haxis : FourBlock.OnAxis H (toBlocks p.2) :=
    (BookOrthogonal.mem_W_iff_onAxis H p.2).mp hx
  have he : Pi.single H (toBlocks p.2 H) = toBlocks p.2 := by
    ext J
    by_cases hJ : J = H
    · subst J; simp
    · simp [hJ, haxis J hJ]
  change sheetResidual (p.1, toBlocks p.2) = 0
  simpa only [he] using hp

/-- Range elimination remains the actual range projection of the full residual. -/
theorem fE_range_zero (p : EuclideanModel)
    (hp : (euclideanCoordinates p, (0 : normalRange exactPhases)) ∈ reducedPH.source) :
    rangeProjection exactPhases (fE p) = 0 :=
  reducedEmbedding_range_zero (euclideanCoordinates p) hp.1

/-- The concrete open-neighborhood inputs for supported_stress_local_criterion.
No cone or supported-stress positivity premise is supplied here. -/
theorem criterion_input_neighborhood :
    ∃ U : Set EuclideanModel, IsOpen U ∧ (0 : EuclideanModel) ∈ U ∧
      ContDiffOn ℝ 2 fE U ∧
      (∀ (H : Fin 4) (c : Common) (x : BookOrthogonal.E),
        (c,x) ∈ U → x ∈ W H → fE (c,x) = 0) ∧
      (∀ p ∈ U, (euclideanCoordinates p, (0 : normalRange exactPhases)) ∈ reducedPH.source) ∧
      (∀ p ∈ U, rangeProjection exactPhases (fE p) = 0) := by
  have hC2 : ∀ᶠ p in 𝓝 (0 : EuclideanModel), ContDiffAt ℝ 2 fE p :=
    fE_C2.eventually (by norm_num)
  have haxes : ∀ᶠ p : EuclideanModel in 𝓝 0,
      ∀ H : Fin 4, p.2 ∈ W H → fE p = 0 :=
    Filter.eventually_all.mpr fE_axis_zero_near
  have hc : Continuous (fun p : EuclideanModel =>
      (euclideanCoordinates p, (0 : normalRange exactPhases))) :=
    euclideanCoordinates.continuous.prodMk continuous_const
  have hsource : ∀ᶠ p : EuclideanModel in 𝓝 0,
      (euclideanCoordinates p, (0 : normalRange exactPhases)) ∈ reducedPH.source := by
    have ht : Tendsto (fun p : EuclideanModel =>
        (euclideanCoordinates p, (0 : normalRange exactPhases))) (𝓝 0) (𝓝 0) := by
      simpa only [map_zero, Prod.mk_zero_zero] using
        hc.continuousAt.tendsto (x := (0 : EuclideanModel))
    exact ht.eventually (reducedPH.open_source.mem_nhds zero_mem_reducedPH_source)
  obtain ⟨r, hr, hnear⟩ := Metric.mem_nhds_iff.mp (hC2.and (haxes.and hsource))
  refine ⟨Metric.ball 0 r, Metric.isOpen_ball, by simpa using hr, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact (hnear hp).1.contDiffWithinAt
  · intro H c x hp hx
    exact (hnear hp).2.1 H hx
  · intro p hp
    exact (hnear hp).2.2
  · intro p hp
    exact fE_range_zero p (hnear hp).2.2

end Option2.NativeStress.BookHT.EuclideanCriterion

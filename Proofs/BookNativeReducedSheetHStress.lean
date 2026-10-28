module

public import BookNativeSheetHStress

@[expose] public section

/-! Exact annihilation on the reduced sheet, with the neighborhood and fixed stress direction
quantifiers needed by the supported-stress criterion. Positivity remains a separate obligation. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.BookHT.SheetHStress
open CKM.NativeFirstOrder CKM.NativeFourFamily CKM.NativeGroupSlice
open SheetReduction TangentCoordinates NativeNormalKernelBridge ReducedQuadratic
open NativePolynomial QuadraticCertificate.ExactCKMConfiguration
open AnalyticDerivative
open scoped Topology

theorem nativeEmbedding_family_germ (i : Fin 4) :
    (fun p : FamilyCoordinates => nativeEmbedding (p.1, Pi.single i p.2)) =ᶠ[𝓝 0]
      familyCfg i := by
  filter_upwards [eliminated_family_germ i] with p hp
  simp only [nativeEmbedding, familyCfg, hp]

/-- Stronger than transverse annihilation: the transported real H field kills every reduced direction. -/
theorem realField_reduced_annihilates (i : Fin 4) (w : Blocks) :
    ∀ᶠ p in 𝓝 (0 : FamilyCoordinates),
      (realField i w p).comp (fderiv ℝ sheetResidual (p.1, Pi.single i p.2)) = 0 := by
  have ht : Filter.Tendsto (sheetAxis i) (𝓝 (0 : FamilyCoordinates)) (𝓝 0) := by
    simpa only [map_zero] using (sheetAxis i).continuous.continuousAt.tendsto (x := 0)
  filter_upwards [rawFamily_mem_target i, nativeEmbedding_family_germ i,
    ht.eventually (nativeEmbedding_C2.eventually (by norm_num))] with p hp he hd
  have ha := realField_annihilates i w p hp
  rw [← he] at ha
  change ContDiffAt ℝ 2 nativeEmbedding (p.1, Pi.single i p.2) at hd
  rw [sheetResidual_native, fderiv_comp _ originalF_differentiable.differentiableAt
    (hd.differentiableAt (by norm_num)), ← ContinuousLinearMap.comp_assoc, ha]
  rfl

/-- At any prescribed reduced neighborhood, shrink once to an open actual family neighborhood.
The fixed Book weight w is independent of p; no annihilation, reproduction or positivity input occurs. -/
theorem supported_stress_field (i : Fin 4) (w : Blocks) (U : Set KernelModel)
    (hU : IsOpen U) (h0 : (0 : KernelModel) ∈ U) :
    ∃ V : Set FamilyCoordinates, IsOpen V ∧ (0 : FamilyCoordinates) ∈ V ∧
      (∀ p ∈ V, (p.1, Pi.single i p.2) ∈ U) ∧
      ContinuousOn (realField i w) V ∧
      (∀ p ∈ V, ∀ n : Blocks,
        realField i w p (fderiv ℝ sheetResidual (p.1, Pi.single i p.2) (0,n)) = 0) ∧
      realField i w 0 = NativeH.realStressFunctional i w := by
  have hu : ∀ᶠ p in 𝓝 (0 : FamilyCoordinates), sheetAxis i p ∈ U :=
    (sheetAxis i).continuous.continuousAt.preimage_mem_nhds
      (by rw [map_zero]; exact hU.mem_nhds h0)
  have hall : ∀ᶠ p in 𝓝 (0 : FamilyCoordinates),
      sheetAxis i p ∈ U ∧ ContinuousAt (realField i w) p ∧
        (realField i w p).comp (fderiv ℝ sheetResidual (p.1, Pi.single i p.2)) = 0 := by
    filter_upwards [hu, (realField_analytic i w).eventually_analyticAt,
      realField_reduced_annihilates i w] with p hp hc ha
    exact ⟨hp, hc.continuousAt, ha⟩
  obtain ⟨V, hV, hVo, hVz⟩ := mem_nhds_iff.1 hall
  refine ⟨V, hVo, hVz, fun p hp => (hV hp).1,
    fun p hp => (hV hp).2.1.continuousWithinAt, ?_, realField_zero i w⟩
  intro p hp n
  exact congrArg (fun L : KernelModel →L[ℝ] ℝ => L (0,n)) (hV hp).2.2

end Option2.NativeStress.BookHT.SheetHStress

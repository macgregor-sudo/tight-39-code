module

public import NativePhaseAlongSheetH
public import NativePhaseRangeReduction

@[expose] public section

/-! The native all-phase H field on the actual reduced sheet. The fixed Book
direction is independent of the varying sheet point. All residual rows remain. -/
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Option2.NativeStress.PhaseReducedHStress
open CKM.NativeFirstOrder CKM.NativeFourFamily CKM.NativeGroupSlice
open CKM.NativeSliceImplicitReduction
open HTPhaseComplete BookHT PhaseSheetChart PhaseRangeReduction
open scoped Topology BigOperators
variable {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)

def nativeEmbedding (x : KernelModel ξ) : Cfg := literalCfg ξ + (reducedEmbedding hξ x : Cfg)
@[simp] theorem nativeEmbedding_zero : nativeEmbedding hξ 0 = literalCfg ξ := by
  simp [nativeEmbedding]
theorem nativeEmbedding_C2 : ContDiffAt ℝ 2 (nativeEmbedding hξ) 0 :=
  contDiffAt_const.add ((normalC ξ).subtypeL.contDiff.contDiffAt.comp 0 (reducedEmbedding_C2 hξ))
theorem sheetResidual_native : sheetResidual hξ = AnalyticDerivative.originalF ∘ nativeEmbedding hξ := rfl

theorem nativeEmbedding_family_germ (i : Fin 4) :
    (fun p : Common ξ × Triple => nativeEmbedding hξ (p.1,Pi.single i p.2)) =ᶠ[𝓝 0]
      (fun p => literalCfg ξ + (sliceFam ξ hξ.1 i (familyParam hξ i p) : Cfg)) := by
  filter_upwards [eliminated_family_germ hξ i] with p hp
  simp only [nativeEmbedding, hp, familySheet]

def componentField (i : Fin 4) (a : Fin 3) (p : Common ξ × Triple) : Residual →L[ℝ] ℂ :=
  PhaseAlongSheetH.componentField ξ hξ.1 i a (familyParam hξ i p)

@[simp] theorem componentField_zero (i : Fin 4) (a : Fin 3) :
    componentField hξ i a 0 = AnalyticDerivative.stressCovector (ellH ξ hξ.1 i a) := by
  rw [componentField, familyParam_zero, PhaseAlongSheetH.componentField_zero]

theorem componentField_analytic (i : Fin 4) (a : Fin 3) :
    AnalyticAt ℝ (componentField hξ i a) 0 :=
  (PhaseAlongSheetH.componentField_analytic ξ hξ.1 i a).comp_of_eq
    (familyParam_analytic hξ i) (familyParam_zero hξ i)

theorem componentField_reduced_annihilates (i : Fin 4) :
    ∀ᶠ p in 𝓝 (0 : Common ξ × Triple), ∀ a : Fin 3,
      (componentField hξ i a p).comp (fderiv ℝ (sheetResidual hξ) (p.1,Pi.single i p.2)) = 0 := by
  obtain ⟨V,hVo,hV0,hV⟩ := PhaseAlongSheetH.along_sheet_H_fields ξ hξ.1 i
  have hpV : ∀ᶠ p in 𝓝 (0 : Common ξ × Triple), familyParam hξ i p ∈ V :=
    (familyParam_analytic hξ i).continuousAt.preimage_mem_nhds (by
      rw [familyParam_zero]; exact hVo.mem_nhds hV0)
  have ht : Filter.Tendsto (axisInclusion (ξ := ξ) i) (𝓝 (0 : Common ξ × Triple)) (𝓝 0) := by
    simpa only [map_zero] using (axisInclusion (ξ := ξ) i).continuous.continuousAt.tendsto (x := 0)
  filter_upwards [hpV, nativeEmbedding_family_germ hξ i,
    ht.eventually ((nativeEmbedding_C2 hξ).eventually (by norm_num))] with p hp he hd
  intro a
  have ha := (hV a).2.1 (familyParam hξ i p) hp
  rw [← he] at ha
  change ContDiffAt ℝ 2 (nativeEmbedding hξ) (p.1,Pi.single i p.2) at hd
  rw [sheetResidual_native, fderiv_comp _ AnalyticDerivative.originalF_differentiable.differentiableAt
    (hd.differentiableAt (by norm_num)), ← ContinuousLinearMap.comp_assoc]
  change ((componentField hξ i a p).comp
    (fderiv ℝ AnalyticDerivative.originalF (nativeEmbedding hξ (p.1,Pi.single i p.2)))).comp _ = 0
  rw [show (componentField hξ i a p).comp
    (fderiv ℝ AnalyticDerivative.originalF (nativeEmbedding hξ (p.1,Pi.single i p.2))) = 0 from ha]
  rfl

def complexField (i : Fin 4) (w : Blocks) (p : Common ξ × Triple) : Residual →L[ℝ] ℂ :=
  ∑ a : Fin 3, star (sigma (w i) a) • componentField hξ i a p

def realField (i : Fin 4) (w : Blocks) (p : Common ξ × Triple) : Residual →L[ℝ] ℝ :=
  (3 : ℝ) • Complex.reCLM.comp (complexField hξ i w p)

theorem realField_apply (i : Fin 4) (w : Blocks) (p : Common ξ × Triple) (q : Residual) :
    realField hξ i w p q = 3 * (∑ a : Fin 3,
      star (sigma (w i) a) * componentField hξ i a p q).re := by
  simp only [realField, complexField, smul_apply, ContinuousLinearMap.comp_apply,
    sum_apply, Complex.reCLM_apply, smul_eq_mul]

/-- The exact factor three and Hermitian conjugation are retained at the native phase basepoint. -/
theorem realField_zero_apply (i : Fin 4) (w : Blocks) (q : Residual) :
    realField hξ i w 0 q = 3 * (∑ a : Fin 3, star (sigma (w i) a) *
      ∑ r : Fin 2184, ellH ξ hξ.1 i a r * (q r : ℂ)).re := by
  rw [realField_apply]
  simp only [componentField_zero, AnalyticDerivative.stressCovector_apply]

theorem realField_analytic (i : Fin 4) (w : Blocks) : AnalyticAt ℝ (realField hξ i w) 0 := by
  have hc : AnalyticAt ℝ (complexField hξ i w) 0 := by
    apply Finset.analyticAt_fun_sum
    intro a _
    exact (analyticAt_const (𝕜 := ℝ) (v := star (sigma (w i) a))).smul
      (componentField_analytic hξ i a)
  have hr : AnalyticAt ℝ (fun p : Common ξ × Triple => Complex.reCLM.comp (complexField hξ i w p)) 0 :=
    ((ContinuousLinearMap.compL ℝ Residual ℂ ℝ Complex.reCLM).analyticAt _).comp hc
  exact hr.const_smul (c := (3 : ℝ))

theorem realField_reduced_annihilates (i : Fin 4) (w : Blocks) :
    ∀ᶠ p in 𝓝 (0 : Common ξ × Triple),
      (realField hξ i w p).comp (fderiv ℝ (sheetResidual hξ) (p.1,Pi.single i p.2)) = 0 := by
  filter_upwards [componentField_reduced_annihilates hξ i] with p hp
  apply ContinuousLinearMap.ext
  intro v
  change realField hξ i w p (fderiv ℝ (sheetResidual hξ) (p.1,Pi.single i p.2) v) = 0
  rw [realField_apply]
  have he (a : Fin 3) : componentField hξ i a p
      (fderiv ℝ (sheetResidual hξ) (p.1,Pi.single i p.2) v) = 0 :=
    congrArg (fun L : KernelModel ξ →L[ℝ] ℂ => L v) (hp a)
  simp only [he, mul_zero, Finset.sum_const_zero, Complex.zero_re]

/-- Shrink to any prescribed reduced neighborhood. Annihilation holds on every
reduced direction, hence in particular on the transverse directions of the criterion. -/
theorem supported_stress_field (i : Fin 4) (w : Blocks) (U : Set (KernelModel ξ))
    (hU : IsOpen U) (h0 : (0 : KernelModel ξ) ∈ U) :
    ∃ V : Set (Common ξ × Triple), IsOpen V ∧ (0 : Common ξ × Triple) ∈ V ∧
      (∀ p ∈ V, (p.1,Pi.single i p.2) ∈ U) ∧ ContinuousOn (realField hξ i w) V ∧
      (∀ p ∈ V, ∀ v : KernelModel ξ,
        realField hξ i w p (fderiv ℝ (sheetResidual hξ) (p.1,Pi.single i p.2) v) = 0) := by
  have hu : ∀ᶠ p in 𝓝 (0 : Common ξ × Triple), axisInclusion i p ∈ U :=
    (axisInclusion i).continuous.continuousAt.preimage_mem_nhds
      (by rw [map_zero]; exact hU.mem_nhds h0)
  have hall : ∀ᶠ p in 𝓝 (0 : Common ξ × Triple), axisInclusion i p ∈ U ∧
      ContinuousAt (realField hξ i w) p ∧
      (realField hξ i w p).comp (fderiv ℝ (sheetResidual hξ) (p.1,Pi.single i p.2)) = 0 := by
    filter_upwards [hu, (realField_analytic hξ i w).eventually_analyticAt,
      realField_reduced_annihilates hξ i w] with p hp hc ha
    exact ⟨hp,hc.continuousAt,ha⟩
  obtain ⟨V,hV,hVo,hV0⟩ := mem_nhds_iff.mp hall
  refine ⟨V,hVo,hV0,fun p hp => (hV hp).1,fun p hp => (hV hp).2.1.continuousWithinAt,?_⟩
  intro p hp v
  exact congrArg (fun L : KernelModel ξ →L[ℝ] ℝ => L v) (hV hp).2.2

end Option2.NativeStress.PhaseReducedHStress
#print axioms Option2.NativeStress.PhaseReducedHStress.supported_stress_field
#print axioms Option2.NativeStress.PhaseReducedHStress.realField_zero_apply

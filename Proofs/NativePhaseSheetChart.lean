module

public import HTPhaseCompleteGeometry
public import BookNativeSheetChart

@[expose] public section

/-! A nonlinear simultaneous sheet chart at each good phase. The common germ is
inserted through its actual analytic inclusion in every native family. This is a
chart on the full normal space, before elimination of the residual range. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.PhaseSheetChart
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeSliceNormalSplitting CKM.NativeSliceImplicitReduction
open HTPhaseComplete BookHT
open BookHT.NativeNormalKernelBridge (unpackNative)
open BookHT.SheetReduction (strict_comp_zero)
open scoped Topology BigOperators

variable {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)

abbrev Common (ξ : Fin 4 → ℂ) := fixQK ξ
abbrev Normal (ξ : Fin 4 → ℂ) := normalC ξ
abbrev Complement (ξ : Fin 4 → ℂ) := normalComplement ξ
abbrev KernelModel (ξ : Fin 4 → ℂ) := Common ξ × Blocks
abbrev Model (ξ : Fin 4 → ℂ) := KernelModel ξ × Complement ξ

def kernelMap : KernelModel ξ →L[ℝ] Normal ξ :=
  (normalKernel ξ).subtypeL.comp (bookPhaseKernelEquiv hξ).toContinuousLinearMap

theorem kernelMap_apply (c : Common ξ) (z : Blocks) :
    (kernelMap hξ (c,z) : Cfg) = (c : Cfg) +
      (normalProjXi ξ hξ.1 (unpackNative (Vxi ξ hξ.1 z)) : Cfg) := by
  rw [← phaseV_eq_Vxi]
  exact bookPhaseKernelEquiv_apply hξ c z

def commonNormal : Common ξ →L[ℝ] Normal ξ :=
  (kernelMap hξ).comp ((ContinuousLinearMap.id ℝ (Common ξ)).prod 0)

@[simp] theorem commonNormal_coe (c : Common ξ) : (commonNormal hξ c : Cfg) = c := by
  change (kernelMap hξ (c,0) : Cfg) = _
  rw [kernelMap_apply, map_zero]
  have hu : unpackNative 0 = 0 := rfl
  rw [hu, map_zero]
  simp

def commonSheet (c : Common ξ) : Normal ξ :=
  sliceCommon ξ hξ.1 ((commonParamEquiv hξ).symm c)

@[simp] theorem commonSheet_zero : commonSheet hξ 0 = 0 := by
  simp [commonSheet, sliceCommon_zero]

theorem commonSheet_analytic : AnalyticAt ℝ (commonSheet hξ) 0 :=
  (analyticAt_sliceCommon hξ.1).comp_of_eq ((commonParamEquiv hξ).symm.analyticAt 0) (map_zero _)

theorem commonSheet_derivative : HasStrictFDerivAt (commonSheet hξ) (commonNormal hξ) 0 := by
  have hd := strict_comp_zero (hasStrictFDerivAt_sliceCommon hξ.1)
    (commonParamEquiv hξ).symm.hasStrictFDerivAt (map_zero _)
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro c
  apply Subtype.ext
  change (sliceCommonDer ξ hξ.1 ((commonParamEquiv hξ).symm c) : Cfg) = _
  rw [← commonParamEquiv_apply hξ, ContinuousLinearEquiv.apply_symm_apply, commonNormal_coe]

def familyInclusion (i : Fin 4) : (Fin 4 → ℝ) → SliceParam :=
  Classical.choose (exists_slice_inclusion hξ.1 i)

theorem familyInclusion_spec (i : Fin 4) :
    AnalyticAt ℝ (familyInclusion hξ i) 0 ∧ familyInclusion hξ i 0 = 0 ∧
      ∀ᶠ θ in 𝓝 (0 : Fin 4 → ℝ),
        sliceFam ξ hξ.1 i (familyInclusion hξ i θ) = sliceCommon ξ hξ.1 θ :=
  Classical.choose_spec (exists_slice_inclusion hξ.1 i)

def axisParam (i : Fin 4) : Triple →L[ℝ] SliceParam :=
  (axisSliceEquiv hξ i).toContinuousLinearMap.comp
    ((0 : Triple →L[ℝ] Common ξ).prod (ContinuousLinearMap.id ℝ Triple))

def familyParam (i : Fin 4) (p : Common ξ × Triple) : SliceParam :=
  familyInclusion hξ i ((commonParamEquiv hξ).symm p.1) + axisParam hξ i p.2

def familySheet (i : Fin 4) (p : Common ξ × Triple) : Normal ξ :=
  sliceFam ξ hξ.1 i (familyParam hξ i p)

@[simp] theorem familyParam_zero (i : Fin 4) : familyParam hξ i 0 = 0 := by
  simp [familyParam, (familyInclusion_spec hξ i).2.1]

@[simp] theorem familySheet_zero (i : Fin 4) : familySheet hξ i 0 = 0 := by
  simp [familySheet, sliceFam_zero]

theorem familyParam_analytic (i : Fin 4) : AnalyticAt ℝ (familyParam hξ i) 0 :=
  ((familyInclusion_spec hξ i).1.comp_of_eq
    (((commonParamEquiv hξ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℝ (Common ξ) Triple)).analyticAt 0) (map_zero _)).add
    (((axisParam hξ i).comp (ContinuousLinearMap.snd ℝ (Common ξ) Triple)).analyticAt 0)

theorem familySheet_analytic (i : Fin 4) : AnalyticAt ℝ (familySheet hξ i) 0 :=
  (analyticAt_sliceFam hξ.1 i).comp_of_eq (familyParam_analytic hξ i) (familyParam_zero hξ i)

theorem familySheet_common_germ (i : Fin 4) :
    (fun c : Common ξ => familySheet hξ i (c,0)) =ᶠ[𝓝 0] commonSheet hξ := by
  have ht : Filter.Tendsto (commonParamEquiv hξ).symm (𝓝 (0 : Common ξ)) (𝓝 0) := by
    simpa only [map_zero] using (commonParamEquiv hξ).symm.continuous.continuousAt.tendsto (x := 0)
  filter_upwards [ht.eventually (familyInclusion_spec hξ i).2.2] with c hc
  simpa [familySheet, familyParam, commonSheet] using hc

def axisInclusion (i : Fin 4) : (Common ξ × Triple) →L[ℝ] KernelModel ξ :=
  (ContinuousLinearMap.fst ℝ (Common ξ) Triple).prod
    ((ContinuousLinearMap.single ℝ (fun _ : Fin 4 => Triple) i).comp
      (ContinuousLinearMap.snd ℝ (Common ξ) Triple))

theorem familySheet_derivative (i : Fin 4) : HasStrictFDerivAt (familySheet hξ i)
    ((kernelMap hξ).comp (axisInclusion i)) 0 := by
  let J := (fderiv ℝ (familyInclusion hξ i) 0).comp (commonParamEquiv hξ).symm.toContinuousLinearMap
  have hj : HasStrictFDerivAt (fun c : Common ξ => familyInclusion hξ i ((commonParamEquiv hξ).symm c)) J 0 :=
    strict_comp_zero (familyInclusion_spec hξ i).1.hasStrictFDerivAt
      (commonParamEquiv hξ).symm.hasStrictFDerivAt (map_zero _)
  have hfac : (sliceFamDer ξ hξ.1 i).comp J = commonNormal hξ := by
    have hf := strict_comp_zero (hasStrictFDerivAt_sliceFam hξ.1 i) hj
      (by simp [(familyInclusion_spec hξ i).2.1])
    have he : HasFDerivAt (fun c : Common ξ => familySheet hξ i (c,0))
        ((sliceFamDer ξ hξ.1 i).comp J) 0 := by
      simpa [familySheet, familyParam] using hf.hasFDerivAt
    exact (he.congr_of_eventuallyEq (familySheet_common_germ hξ i).symm).unique
      (commonSheet_derivative hξ).hasFDerivAt
  have hp : HasStrictFDerivAt (familyParam hξ i) (J.coprod (axisParam hξ i)) 0 := by
    exact (hj.comp (0 : Common ξ × Triple)
      (hasStrictFDerivAt_fst (𝕜 := ℝ) (E := Common ξ) (F := Triple))).add
      ((axisParam hξ i).hasStrictFDerivAt.comp (0 : Common ξ × Triple)
        (hasStrictFDerivAt_snd (𝕜 := ℝ) (E := Common ξ) (F := Triple)))
  have hs := strict_comp_zero (hasStrictFDerivAt_sliceFam hξ.1 i) hp (familyParam_zero hξ i)
  apply hs.congr_fderiv
  apply ContinuousLinearMap.ext
  intro p
  apply Subtype.ext
  change ((sliceFamDer ξ hξ.1 i) (J p.1 + axisParam hξ i p.2) : Cfg) = _
  rw [map_add]
  have hc := congrArg (fun L : Common ξ →L[ℝ] Normal ξ => L p.1) hfac
  rw [show sliceFamDer ξ hξ.1 i (J p.1) = commonNormal hξ p.1 from hc]
  change (commonNormal hξ p.1 : Cfg) +
    (sliceFamDer ξ hξ.1 i (axisSliceEquiv hξ i (0,p.2)) : Cfg) =
      (kernelMap hξ (p.1, Pi.single i p.2) : Cfg)
  rw [commonNormal_coe, sliceFamDer_axisSliceEquiv, kernelMap_apply, phaseV_eq_Vxi]
  simp

def sheetDerivative : Model ξ ≃L[ℝ] Normal ξ :=
  ((bookPhaseKernelEquiv hξ).prodCongr (complementRangeEquiv ξ)).trans (chartDerivative ξ).symm

theorem sheetDerivative_apply (p : Model ξ) :
    sheetDerivative hξ p = kernelMap hξ p.1 + (p.2 : Normal ξ) := by
  change (bookPhaseKernelEquiv hξ p.1 : Normal ξ) +
    normalRightInverse ξ (complementRangeEquiv ξ p.2) = _
  have he : normalRightInverse ξ (complementRangeEquiv ξ p.2) = (p.2 : Normal ξ) := by
    change (((complementRangeEquiv ξ).symm (complementRangeEquiv ξ p.2) : Complement ξ) : Normal ξ) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [he]
  rfl

def commonPr : Model ξ →L[ℝ] Common ξ :=
  (ContinuousLinearMap.fst ℝ (Common ξ) Blocks).comp (ContinuousLinearMap.fst ℝ (KernelModel ξ) (Complement ξ))
def familyPr (i : Fin 4) : Model ξ →L[ℝ] (Common ξ × Triple) :=
  commonPr.prod ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Triple) i).comp
    ((ContinuousLinearMap.snd ℝ (Common ξ) Blocks).comp (ContinuousLinearMap.fst ℝ (KernelModel ξ) (Complement ξ))))
def complementPr : Model ξ →L[ℝ] Normal ξ :=
  (normalComplement ξ).subtypeL.comp (ContinuousLinearMap.snd ℝ (KernelModel ξ) (Complement ξ))

def sheetMap (p : Model ξ) : Normal ξ :=
  commonSheet hξ (commonPr p) + ∑ i : Fin 4,
    (familySheet hξ i (familyPr i p) - commonSheet hξ (commonPr p)) + complementPr p

@[simp] theorem sheetMap_zero : sheetMap hξ 0 = 0 := by simp [sheetMap]

theorem sheetMap_analytic : AnalyticAt ℝ (sheetMap hξ) 0 := by
  have hc : AnalyticAt ℝ (fun p : Model ξ => commonSheet hξ (commonPr p)) 0 :=
    (commonSheet_analytic hξ).comp_of_eq
      (ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := Model ξ) (F := Common ξ) commonPr 0) (map_zero _)
  have hs : ∀ i ∈ (Finset.univ : Finset (Fin 4)), AnalyticAt ℝ
      (fun p : Model ξ => familySheet hξ i (familyPr i p) - commonSheet hξ (commonPr p)) 0 := by
    intro i _
    have hf : AnalyticAt ℝ (fun p : Model ξ => familySheet hξ i (familyPr i p)) 0 :=
      (familySheet_analytic hξ i).comp_of_eq
      (ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := Model ξ) (F := Common ξ × Triple) (familyPr i) 0)
        (map_zero _)
    exact AnalyticAt.sub (E := Model ξ) (F := Normal ξ) hf hc
  exact (AnalyticAt.add (E := Model ξ) (F := Normal ξ) hc (Finset.analyticAt_fun_sum _ hs)).add
    (ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := Model ξ) (F := Normal ξ) complementPr 0)

theorem sheetMap_derivative : HasStrictFDerivAt (sheetMap hξ)
    (sheetDerivative hξ : Model ξ →L[ℝ] Normal ξ) 0 := by
  have hc := strict_comp_zero (E := Model ξ) (F := Common ξ) (G := Normal ξ)
    (commonSheet_derivative hξ)
    (ContinuousLinearMap.hasStrictFDerivAt (𝕜 := ℝ) (E := Model ξ) (F := Common ξ) commonPr (x := 0)) (map_zero _)
  let B (i : Fin 4) : Model ξ →L[ℝ] Normal ξ := (kernelMap hξ).comp
    ((0 : Model ξ →L[ℝ] Common ξ).prod
      ((ContinuousLinearMap.single ℝ (fun _ : Fin 4 => Triple) i).comp
        ((ContinuousLinearMap.snd ℝ (Common ξ) Triple).comp (familyPr i))))
  have hs : ∀ i ∈ (Finset.univ : Finset (Fin 4)), HasStrictFDerivAt
      (fun p : Model ξ => familySheet hξ i (familyPr i p) - commonSheet hξ (commonPr p))
      (B i) 0 := by
    intro i _
    have hf := strict_comp_zero (E := Model ξ) (F := Common ξ × Triple) (G := Normal ξ)
      (familySheet_derivative hξ i)
      (ContinuousLinearMap.hasStrictFDerivAt (𝕜 := ℝ) (E := Model ξ) (F := Common ξ × Triple)
        (familyPr i) (x := 0)) (map_zero _)
    apply (HasStrictFDerivAt.fun_sub (𝕜 := ℝ) (E := Model ξ) (F := Normal ξ) hf hc).congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    change kernelMap hξ (p.1.1, Pi.single i (p.1.2 i)) - kernelMap hξ (p.1.1,0) =
      kernelMap hξ (0, Pi.single i (p.1.2 i))
    rw [← map_sub]
    congr 1
    ext <;> simp
  have hsum := HasStrictFDerivAt.fun_sum (𝕜 := ℝ) (E := Model ξ) (F := Normal ξ) hs
  have hadd := HasStrictFDerivAt.fun_add (𝕜 := ℝ) (E := Model ξ) (F := Normal ξ) hc hsum
  have hd := HasStrictFDerivAt.fun_add (𝕜 := ℝ) (E := Model ξ) (F := Normal ξ) hadd
    (ContinuousLinearMap.hasStrictFDerivAt (𝕜 := ℝ) (E := Model ξ) (F := Normal ξ) complementPr (x := 0))
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro p
  change _ = sheetDerivative hξ p
  rw [sheetDerivative_apply]
  simp only [add_apply, sum_apply, ContinuousLinearMap.comp_apply]
  change kernelMap hξ (p.1.1,0) +
    (∑ i : Fin 4, kernelMap hξ (0,Pi.single i (p.1.2 i))) +
    (p.2 : Normal ξ) = kernelMap hξ p.1 + (p.2 : Normal ξ)
  have hsum : (∑ i : Fin 4, ((0 : Common ξ), Pi.single i (p.1.2 i))) = (0,p.1.2) := by
    apply Prod.ext
    · change (ContinuousLinearMap.fst ℝ (Common ξ) Blocks)
        (∑ i : Fin 4, ((0 : Common ξ), Pi.single i (p.1.2 i))) = 0
      rw [map_sum]
      simp
    · change (ContinuousLinearMap.snd ℝ (Common ξ) Blocks)
        (∑ i : Fin 4, ((0 : Common ξ), Pi.single i (p.1.2 i))) = p.1.2
      rw [map_sum]
      change (∑ i : Fin 4, Pi.single i (p.1.2 i)) = p.1.2
      ext j
      simp
  rw [← map_sum, hsum, ← map_add]
  congr 2
  exact Prod.ext (add_zero _) (zero_add _)

theorem sheetMap_C2 : ContDiffAt ℝ 2 (sheetMap hξ) 0 := (sheetMap_analytic hξ).contDiffAt

def familyAxis (i : Fin 4) : (Common ξ × Triple) →L[ℝ] Model ξ := (axisInclusion i).prod 0
def commonAxis : Common ξ →L[ℝ] Model ξ :=
  ((ContinuousLinearMap.id ℝ (Common ξ)).prod (0 : Common ξ →L[ℝ] Blocks)).prod 0

theorem sheetMap_common_germ :
    (fun c : Common ξ => sheetMap hξ (commonAxis c)) =ᶠ[𝓝 0] commonSheet hξ := by
  filter_upwards [Filter.eventually_all.mpr (familySheet_common_germ hξ)] with c hc
  change commonSheet hξ c + ∑ i : Fin 4, (familySheet hξ i (c,0) - commonSheet hξ c) + 0 = _
  simp [hc]

theorem sheetMap_family_germ (i : Fin 4) :
    (fun p : Common ξ × Triple => sheetMap hξ (familyAxis i p)) =ᶠ[𝓝 0] familySheet hξ i := by
  have ht : Filter.Tendsto (Prod.fst : Common ξ × Triple → Common ξ) (𝓝 0) (𝓝 0) := continuousAt_fst.tendsto
  filter_upwards [ht.eventually (Filter.eventually_all.mpr (familySheet_common_germ hξ))] with p hp
  change commonSheet hξ p.1 + ∑ j : Fin 4,
    (familySheet hξ j (p.1,(Pi.single i p.2 : Blocks) j) - commonSheet hξ p.1) + 0 = _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj, hp j]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem sheetMap_family_originalF_germ (i : Fin 4) :
    ∀ᶠ p in 𝓝 (0 : Common ξ × Triple),
      AnalyticDerivative.originalF (literalCfg ξ + (sheetMap hξ (familyAxis i p) : Cfg)) = 0 := by
  have ht : Filter.Tendsto (familyParam hξ i) (𝓝 (0 : Common ξ × Triple)) (𝓝 0) := by
    simpa only [familyParam_zero] using (familyParam_analytic hξ i).continuousAt.tendsto
  filter_upwards [sheetMap_family_germ hξ i,
    ht.eventually (eventually_originalF_sliceFam hξ.1 i)] with p hp hz
  rw [hp]
  exact hz

theorem sheetMap_fderiv_native (c : Common ξ) (z : Blocks) (e : Complement ξ) :
    (fderiv ℝ (sheetMap hξ) 0 ((c,z),e) : Cfg) = (c : Cfg) +
      (normalProjXi ξ hξ.1 (unpackNative (Vxi ξ hξ.1 z)) : Cfg) + ((e : Normal ξ) : Cfg) := by
  rw [(sheetMap_derivative hξ).hasFDerivAt.fderiv]
  change (sheetDerivative hξ ((c,z),e) : Cfg) = _
  rw [sheetDerivative_apply]
  exact congrArg (fun n : Cfg => n + ((e : Normal ξ) : Cfg)) (kernelMap_apply hξ c z)

def sheetPH : OpenPartialHomeomorph (Model ξ) (Normal ξ) :=
  (sheetMap_C2 hξ).toOpenPartialHomeomorph (sheetMap hξ)
    (sheetMap_derivative hξ).hasFDerivAt (by norm_num)

theorem zero_mem_sheetPH_source : (0 : Model ξ) ∈ (sheetPH hξ).source :=
  (sheetMap_C2 hξ).mem_toOpenPartialHomeomorph_source (sheetMap_derivative hξ).hasFDerivAt (by norm_num)

@[simp] theorem sheetPH_coe : ⇑(sheetPH hξ) = sheetMap hξ := rfl
@[simp] theorem sheetPH_zero : sheetPH hξ 0 = 0 := sheetMap_zero hξ

theorem zero_mem_sheetPH_target : (0 : Normal ξ) ∈ (sheetPH hξ).target := by
  simpa only [sheetPH_zero] using (sheetPH hξ).map_source (zero_mem_sheetPH_source hξ)

@[simp] theorem sheetPH_symm_zero : (sheetPH hξ).symm 0 = 0 := by
  simpa only [sheetPH_zero] using (sheetPH hξ).left_inv (zero_mem_sheetPH_source hξ)

theorem sheetPH_symm_C2 : ContDiffAt ℝ 2 (sheetPH hξ).symm 0 := by
  apply OpenPartialHomeomorph.contDiffAt_symm (𝕜 := ℝ) (E := Model ξ) (F := Normal ξ)
    (sheetPH hξ) (zero_mem_sheetPH_target hξ) (f₀' := sheetDerivative hξ)
  · simpa only [sheetPH_symm_zero, sheetPH_coe] using (sheetMap_derivative hξ).hasFDerivAt
  · simpa only [sheetPH_symm_zero, sheetPH_coe] using sheetMap_C2 hξ

end Option2.NativeStress.PhaseSheetChart

#print axioms Option2.NativeStress.PhaseSheetChart.sheetMap_family_germ
#print axioms Option2.NativeStress.PhaseSheetChart.sheetMap_fderiv_native
#print axioms Option2.NativeStress.PhaseSheetChart.sheetPH
#print axioms Option2.NativeStress.PhaseSheetChart.sheetPH_symm_C2
#print axioms Option2.NativeStress.PhaseSheetChart.sheetMap_family_originalF_germ

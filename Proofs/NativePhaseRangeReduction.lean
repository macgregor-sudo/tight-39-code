module

public import NativePhaseSheetChart

@[expose] public section

/-! Range elimination in the native good-phase simultaneous sheet chart.
All statements retain actual inverse-function domains; no exhaustion is assumed. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.PhaseRangeReduction
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeSliceNormalSplitting CKM.NativeSliceImplicitReduction
open HTPhaseComplete BookHT PhaseSheetChart
open BookHT.NativeNormalKernelBridge (unpackNative)
open scoped Topology
variable {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)

abbrev ReducedCoordinates (ξ : Fin 4 → ℂ) := KernelModel ξ × normalRange ξ

def rangeDerivativeEquiv : Model ξ ≃L[ℝ] ReducedCoordinates ξ :=
  (ContinuousLinearEquiv.refl ℝ (KernelModel ξ)).prodCongr (complementRangeEquiv ξ)

def rangeMap (p : Model ξ) : ReducedCoordinates ξ :=
  (p.1, rangeProjection ξ (normalResidual ξ (sheetMap hξ p)))

@[simp] theorem rangeMap_zero : rangeMap hξ 0 = 0 := by
  simp [rangeMap, normalResidual, originalF_literalCfg ξ hξ.1]

theorem kernelMap_normalDerivative (x : KernelModel ξ) : normalDerivative ξ (kernelMap hξ x) = 0 :=
  (bookPhaseKernelEquiv hξ x).property

theorem rangeDerivative_sheet (p : Model ξ) :
    rangeDerivative ξ (sheetDerivative hξ p) = complementRangeEquiv ξ p.2 := by
  apply Subtype.ext
  rw [coe_rangeDerivative, sheetDerivative_apply, map_add, kernelMap_normalDerivative, zero_add]
  exact (complementRangeEquiv_apply ξ p.2).symm

theorem rangeMap_C2 : ContDiffAt ℝ 2 (rangeMap hξ) 0 := by
  have hf : ContDiffAt ℝ 2 (fun p : Model ξ => normalResidual ξ (sheetMap hξ p)) 0 :=
    (normalResidual_contDiff ξ 2).contDiffAt.comp 0 (sheetMap_C2 hξ)
  exact (ContinuousLinearMap.fst ℝ (KernelModel ξ) (Complement ξ)).contDiff.contDiffAt.prodMk
    ((rangeProjection ξ).contDiff.contDiffAt.comp 0 hf)

theorem rangeMap_derivative : HasFDerivAt (rangeMap hξ)
    (rangeDerivativeEquiv (ξ := ξ) : Model ξ →L[ℝ] ReducedCoordinates ξ) 0 := by
  have hn : HasFDerivAt (normalResidual ξ) (normalDerivative ξ) (sheetMap hξ 0) := by
    rw [sheetMap_zero]; exact normalResidual_hasFDerivAt ξ
  have hf := HasFDerivAt.comp (𝕜 := ℝ) (E := Model ξ) (F := Normal ξ) (G := Residual)
    0 hn (sheetMap_derivative hξ).hasFDerivAt
  have hp := HasFDerivAt.comp (𝕜 := ℝ) (E := Model ξ) (F := Residual) (G := normalRange ξ)
    0 (rangeProjection ξ).hasFDerivAt hf
  have hd := HasFDerivAt.prodMk (𝕜 := ℝ) (E := Model ξ) (F := KernelModel ξ) (G := normalRange ξ)
    (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := Model ξ) (F := KernelModel ξ)
      (ContinuousLinearMap.fst ℝ (KernelModel ξ) (Complement ξ))) hp
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro p
  change (p.1,rangeProjection ξ (normalDerivative ξ (sheetDerivative hξ p))) =
    (p.1,complementRangeEquiv ξ p.2)
  rw [rangeProjection_normalDerivative, rangeDerivative_sheet]

def rangePH : OpenPartialHomeomorph (Model ξ) (ReducedCoordinates ξ) :=
  (rangeMap_C2 hξ).toOpenPartialHomeomorph (rangeMap hξ) (rangeMap_derivative hξ) (by norm_num)
@[simp] theorem rangePH_coe : ⇑(rangePH hξ) = rangeMap hξ := rfl
@[simp] theorem rangePH_zero : rangePH hξ 0 = 0 := rangeMap_zero hξ
theorem zero_mem_rangePH_source : (0 : Model ξ) ∈ (rangePH hξ).source :=
  (rangeMap_C2 hξ).mem_toOpenPartialHomeomorph_source (rangeMap_derivative hξ) (by norm_num)
theorem zero_mem_rangePH_target : (0 : ReducedCoordinates ξ) ∈ (rangePH hξ).target := by
  simpa only [rangePH_zero] using (rangePH hξ).map_source (zero_mem_rangePH_source hξ)
@[simp] theorem rangePH_symm_zero : (rangePH hξ).symm 0 = 0 := by
  simpa only [rangePH_zero] using (rangePH hξ).left_inv (zero_mem_rangePH_source hξ)

theorem rangePH_symm_C2 : ContDiffAt ℝ 2 (rangePH hξ).symm 0 := by
  apply OpenPartialHomeomorph.contDiffAt_symm (𝕜 := ℝ) (E := Model ξ) (F := ReducedCoordinates ξ)
    (rangePH hξ) (zero_mem_rangePH_target hξ) (f₀' := rangeDerivativeEquiv)
  · simpa only [rangePH_symm_zero, rangePH_coe] using rangeMap_derivative hξ
  · simpa only [rangePH_symm_zero, rangePH_coe] using rangeMap_C2 hξ

theorem rangePH_symm_derivative : HasFDerivAt (rangePH hξ).symm
    ((rangeDerivativeEquiv (ξ := ξ)).symm : ReducedCoordinates ξ →L[ℝ] Model ξ) 0 := by
  apply OpenPartialHomeomorph.hasFDerivAt_symm (𝕜 := ℝ) (E := Model ξ) (F := ReducedCoordinates ξ)
    (rangePH hξ) (zero_mem_rangePH_target hξ) (f' := rangeDerivativeEquiv)
  simpa only [rangePH_symm_zero, rangePH_coe] using rangeMap_derivative hξ

def reducedPH : OpenPartialHomeomorph (ReducedCoordinates ξ) (Normal ξ) :=
  (rangePH hξ).symm.trans (sheetPH hξ)
def reducedEmbedding (x : KernelModel ξ) : Normal ξ := reducedPH hξ (x,0)
def sheetResidual (x : KernelModel ξ) : Residual := normalResidual ξ (reducedEmbedding hξ x)

@[simp] theorem reducedPH_apply (q : ReducedCoordinates ξ) :
    reducedPH hξ q = sheetMap hξ ((rangePH hξ).symm q) := rfl
@[simp] theorem reducedPH_zero : reducedPH hξ 0 = 0 := by simp
@[simp] theorem reducedEmbedding_zero : reducedEmbedding hξ 0 = 0 := by
  simp only [reducedEmbedding, Prod.mk_zero_zero, reducedPH_zero]
@[simp] theorem sheetResidual_zero : sheetResidual hξ 0 = 0 := by
  simp [sheetResidual, normalResidual, originalF_literalCfg ξ hξ.1]

theorem zero_mem_reducedPH_source : (0 : ReducedCoordinates ξ) ∈ (reducedPH hξ).source := by
  change 0 ∈ (rangePH hξ).target ∧ (rangePH hξ).symm 0 ∈ (sheetPH hξ).source
  exact ⟨zero_mem_rangePH_target hξ, by rw [rangePH_symm_zero]; exact zero_mem_sheetPH_source hξ⟩

theorem reducedPH_C2 : ContDiffAt ℝ 2 (reducedPH hξ) 0 := by
  have hs : ContDiffAt ℝ 2 (sheetMap hξ) ((rangePH hξ).symm 0) := by
    rw [rangePH_symm_zero]; exact sheetMap_C2 hξ
  exact hs.comp 0 (rangePH_symm_C2 hξ)

theorem reducedPH_symm_C2 : ContDiffAt ℝ 2 (reducedPH hξ).symm 0 := by
  have hr : ContDiffAt ℝ 2 (rangePH hξ) ((sheetPH hξ).symm 0) := by
    rw [sheetPH_symm_zero]; exact rangeMap_C2 hξ
  exact hr.comp 0 (sheetPH_symm_C2 hξ)

theorem reducedEmbedding_C2 : ContDiffAt ℝ 2 (reducedEmbedding hξ) 0 := by
  have hi : ContDiffAt ℝ 2 (fun x : KernelModel ξ => (x,(0 : normalRange ξ))) 0 :=
    contDiff_id.contDiffAt.prodMk contDiff_const.contDiffAt
  exact (reducedPH_C2 hξ).comp 0 (f := fun x : KernelModel ξ => (x,(0 : normalRange ξ))) hi

theorem sheetResidual_C2 : ContDiffAt ℝ 2 (sheetResidual hξ) 0 :=
  (normalResidual_contDiff ξ 2).contDiffAt.comp 0 (reducedEmbedding_C2 hξ)

theorem reducedEmbedding_derivative : HasFDerivAt (reducedEmbedding hξ) (kernelMap hξ) 0 := by
  let I : KernelModel ξ →L[ℝ] ReducedCoordinates ξ := ContinuousLinearMap.inl ℝ (KernelModel ξ) (normalRange ξ)
  have hs := HasFDerivAt.comp (𝕜 := ℝ) (E := KernelModel ξ) (F := ReducedCoordinates ξ) (G := Model ξ)
    0 (rangePH_symm_derivative hξ) I.hasFDerivAt
  have hm : HasFDerivAt (sheetMap hξ) (sheetDerivative hξ : Model ξ →L[ℝ] Normal ξ)
      ((rangePH hξ).symm ((0 : KernelModel ξ),0)) := by
    simpa only [Prod.mk_zero_zero, rangePH_symm_zero] using (sheetMap_derivative hξ).hasFDerivAt
  have hd := HasFDerivAt.comp (𝕜 := ℝ) (E := KernelModel ξ) (F := Model ξ) (G := Normal ξ)
    (f := fun x : KernelModel ξ => (rangePH hξ).symm (x,0)) 0 hm hs
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro x
  change sheetDerivative hξ (x,(complementRangeEquiv ξ).symm 0) = kernelMap hξ x
  rw [map_zero, sheetDerivative_apply]
  simp

theorem sheetResidual_derivative_zero : HasFDerivAt (sheetResidual hξ)
    (0 : KernelModel ξ →L[ℝ] Residual) 0 := by
  have hn : HasFDerivAt (normalResidual ξ) (normalDerivative ξ) (reducedEmbedding hξ 0) := by
    rw [reducedEmbedding_zero]; exact normalResidual_hasFDerivAt ξ
  apply (hn.comp 0 (reducedEmbedding_derivative hξ)).congr_fderiv
  apply ContinuousLinearMap.ext
  intro x
  exact kernelMap_normalDerivative hξ x

theorem reducedEmbedding_range_zero (x : KernelModel ξ)
    (hx : (x,(0 : normalRange ξ)) ∈ (rangePH hξ).target) :
    rangeProjection ξ (sheetResidual hξ x) = 0 := congrArg Prod.snd ((rangePH hξ).right_inv hx)

theorem eliminated_family_germ (i : Fin 4) :
    (fun p : Common ξ × Triple => reducedEmbedding hξ (p.1,Pi.single i p.2)) =ᶠ[𝓝 0] familySheet hξ i := by
  have hs : ∀ᶠ p in 𝓝 (0 : Common ξ × Triple), familyAxis i p ∈ (rangePH hξ).source :=
    (familyAxis i).continuous.continuousAt.preimage_mem_nhds
      (by rw [map_zero]; exact (rangePH hξ).open_source.mem_nhds (zero_mem_rangePH_source hξ))
  filter_upwards [hs, sheetMap_family_originalF_germ hξ i, sheetMap_family_germ hξ i] with p hp hz he
  have hm : rangePH hξ (familyAxis i p) = ((p.1,(Pi.single i p.2 : Blocks)),0) := by
    change ((p.1,(Pi.single i p.2 : Blocks)),rangeProjection ξ
      (AnalyticDerivative.originalF (literalCfg ξ + (sheetMap hξ (familyAxis i p) : Cfg)))) = _
    rw [hz,map_zero]
  change sheetMap hξ ((rangePH hξ).symm ((p.1,Pi.single i p.2),0)) = _
  rw [← hm, (rangePH hξ).left_inv hp, he]

theorem originalF_zero_iff_coordinates (q : ReducedCoordinates ξ) (hq : q ∈ (rangePH hξ).target) :
    AnalyticDerivative.originalF (literalCfg ξ + (reducedPH hξ q : Cfg)) = 0 ↔
      q.2 = 0 ∧ sheetResidual hξ q.1 = 0 := by
  have hi := congrArg Prod.snd ((rangePH hξ).right_inv hq)
  constructor
  · intro hz
    have h2 : q.2 = 0 := by
      change rangeProjection ξ (AnalyticDerivative.originalF (literalCfg ξ + (reducedPH hξ q : Cfg))) = q.2 at hi
      rw [hz,map_zero] at hi
      exact hi.symm
    refine ⟨h2, ?_⟩
    have he : (q.1,(0 : normalRange ξ)) = q := Prod.ext rfl h2.symm
    simpa only [sheetResidual, normalResidual, reducedEmbedding, he] using hz
  · rintro ⟨h2,hz⟩
    have he : (q.1,(0 : normalRange ξ)) = q := Prod.ext rfl h2.symm
    simpa only [sheetResidual, normalResidual, reducedEmbedding, he] using hz

theorem originalF_zero_iff_normal (n : Normal ξ) (hn : n ∈ (reducedPH hξ).target) :
    AnalyticDerivative.originalF (literalCfg ξ + (n : Cfg)) = 0 ↔
      ((reducedPH hξ).symm n).2 = 0 ∧ sheetResidual hξ ((reducedPH hξ).symm n).1 = 0 := by
  have hq := (reducedPH hξ).map_target hn
  have he := originalF_zero_iff_coordinates hξ ((reducedPH hξ).symm n) hq.1
  rwa [(reducedPH hξ).right_inv hn] at he

end Option2.NativeStress.PhaseRangeReduction
#print axioms Option2.NativeStress.PhaseRangeReduction.reducedEmbedding_derivative
#print axioms Option2.NativeStress.PhaseRangeReduction.eliminated_family_germ
#print axioms Option2.NativeStress.PhaseRangeReduction.originalF_zero_iff_normal
#print axioms Option2.NativeStress.PhaseRangeReduction.reducedPH_symm_C2

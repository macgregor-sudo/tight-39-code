module

public import HTPhaseCompleteSeed
public import HTPhaseCompleteDirectionFamily

@[expose] public section

/-!
# The phase-normal kernel equivalence for `Vxi`

`Vxi` and `phaseV` are the same continuous-linear map at every unit phase
(`phaseV_eq_Vxi`, from `Vxi_family`). The equivalences below are
proved by the concrete maps of `HTPhaseCompleteKernel`.
-/

set_option Elab.async false
noncomputable section

namespace Option2.NativeStress.HTPhaseComplete

open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open Option2.NativeStress.BookHT.NativeNormalKernelBridge (unpackNative normalProjection)
open QuadraticCertificate.ExactCKMConfiguration (exactPhases)
open Option2.NativeStress.BookHT.TangentCoordinates (exactPhases_unit)

theorem phaseV_eq_Vxi (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : phaseV ξ hξ = Vxi ξ hξ := by
  apply ContinuousLinearMap.ext
  intro z
  rw [Vxi_family]
  change packCLM (familyDirection ξ hξ z) = _
  rw [familyDirection_apply, map_sum]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [packCLM_apply, preDer_apply]

/-- (interface) the intended phase map, ambient in `Cfg`. -/
def phaseCommonAmbient (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (fixQK ξ × BookHT.Blocks) →L[ℝ] Cfg :=
  (fixQK ξ).subtypeL.coprod
    ((normalC ξ).subtypeL.comp ((normalProjXi ξ hξ).comp (unpackNative.comp (Vxi ξ hξ))))

theorem phaseCommonAmbient_eq (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    phaseCommonAmbient ξ hξ = (tanN ξ).subtypeL.comp (bookPhaseMap hξ) := by
  apply ContinuousLinearMap.ext
  rintro ⟨c, z⟩
  rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, bookPhaseMap_coe, phaseV_eq_Vxi]
  simp only [phaseCommonAmbient, ContinuousLinearMap.coprod_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply]

/-- (b0) -/
theorem sliceRep_hasStrictFDerivAt_normalProjXi' (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    HasStrictFDerivAt (sliceRep ξ hξ) (normalProjXi ξ hξ) (literalCfg ξ) :=
  sliceRep_hasStrictFDerivAt_normalProjXi ξ hξ

/-- (b1) the GoodPhase equivalence onto `tanN ξ`, with the ambient formula preserved. -/
theorem phase_normal_kernel_equiv {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    ∃ e : (fixQK ξ × BookHT.Blocks) ≃L[ℝ] tanN ξ, ∀ (c : fixQK ξ) (z : BookHT.Blocks),
      (e (c, z) : Cfg) = (c : Cfg) + (normalProjXi ξ hξ.1 (unpackNative (Vxi ξ hξ.1 z)) : Cfg) :=
  ⟨bookPhaseEquiv hξ, fun c z => by rw [bookPhaseEquiv_apply, phaseV_eq_Vxi]⟩

/-- (b1') onto the actual normal kernel of the originalF derivative on `normalC ξ`. -/
theorem phase_normal_kernel_equiv' {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    ∃ e : (fixQK ξ × BookHT.Blocks) ≃L[ℝ] CKM.NativeSliceNormalSplitting.normalKernel ξ,
      ∀ (c : fixQK ξ) (z : BookHT.Blocks),
        (((e (c, z) : normalC ξ)) : Cfg) =
          (c : Cfg) + (normalProjXi ξ hξ.1 (unpackNative (Vxi ξ hξ.1 z)) : Cfg) :=
  ⟨bookPhaseKernelEquiv hξ, fun c z => by rw [bookPhaseKernelEquiv_apply, phaseV_eq_Vxi]⟩

/-- (b2) per-axis binding through the constructed parameter equivalence. -/
theorem axis_slice_binding {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (H : Fin 4) :
    ∃ φ : (fixQK ξ × BookHT.Triple) ≃L[ℝ] SliceParam, ∀ (c : fixQK ξ) (u : BookHT.Triple),
      ((sliceFamDer ξ hξ.1 H (φ (c, u)) : normalC ξ) : Cfg) =
        (c : Cfg) + (normalProjXi ξ hξ.1 (unpackNative (Vxi ξ hξ.1 (Pi.single H u))) : Cfg) :=
  ⟨axisSliceEquiv hξ H, fun c u => by rw [sliceFamDer_axisSliceEquiv, phaseV_eq_Vxi]⟩

/-- (b3) the actual common derivative parametrizes the common tangent. -/
theorem common_slice_binding {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    ∃ ψ : (Fin 4 → ℝ) ≃L[ℝ] fixQK ξ, ∀ θ : Fin 4 → ℝ,
      (ψ θ : Cfg) = ((sliceCommonDer ξ hξ.1 θ : normalC ξ) : Cfg) :=
  ⟨commonParamEquiv hξ, fun θ => commonParamEquiv_apply hξ θ⟩

/-- (b0') fixed-seed agreement. -/
theorem normalProjXi_exactPhases' :
    normalProjXi exactPhases exactPhases_unit = normalProjection :=
  normalProjXi_exactPhases

end Option2.NativeStress.HTPhaseComplete

open Option2.NativeStress.HTPhaseComplete
#check @phase_normal_kernel_equiv
#check @phase_normal_kernel_equiv'
#check @axis_slice_binding
#check @common_slice_binding
#print axioms phaseV_eq_Vxi
#print axioms phaseCommonAmbient
#print axioms phaseCommonAmbient_eq
#print axioms sliceRep_hasStrictFDerivAt_normalProjXi'
#print axioms phase_normal_kernel_equiv
#print axioms phase_normal_kernel_equiv'
#print axioms axis_slice_binding
#print axioms common_slice_binding
#print axioms normalProjXi_exactPhases'

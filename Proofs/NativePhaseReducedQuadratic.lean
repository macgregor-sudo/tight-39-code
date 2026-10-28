module

public import NativePhaseReducedHStress
public import HTPhaseCompleteHPhase
public import HTPhaseCompleteTValue
public import BookNativeReducedQuadraticTransfer

@[expose] public section

/-! Exact H/T contractions of the actual reduced half-Hessian at every good
phase. Nonlinear acceleration and orbit corrections are removed by stationary
native stresses, never by identifying the nonlinear map with its tangent. -/
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Option2.NativeStress.PhaseReducedQuadratic
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeSliceImplicitReduction
open HTPhaseComplete BookHT PhaseSheetChart PhaseRangeReduction PhaseReducedHStress
open BookHT.NativeNormalKernelBridge (unpackNative)
open SupportedStress.ReducedQuadratic SupportedStress.HessianPullback
open scoped Topology
variable {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)

def reducedQuadratic (z : Blocks) : Residual :=
  (1/2 : ℝ) • fderiv ℝ (fderiv ℝ (sheetResidual hξ)) 0 (0,z) (0,z)

theorem nativeEmbedding_derivative : HasFDerivAt (nativeEmbedding hξ)
    ((normalC ξ).subtypeL.comp (kernelMap hξ)) 0 :=
  ((normalC ξ).subtypeL.hasFDerivAt.comp 0 (reducedEmbedding_derivative hξ)).const_add (literalCfg ξ)

theorem nativeEmbedding_Book_derivative (z : Blocks) :
    fderiv ℝ (nativeEmbedding hξ) 0 (0,z) =
      (normalProjXi ξ hξ.1 (familyDirection ξ hξ.1 z) : Cfg) := by
  rw [(nativeEmbedding_derivative hξ).fderiv]
  change (kernelMap hξ (0,z) : Cfg) = _
  rw [kernelMap_apply, ← phaseV_eq_Vxi, unpack_phaseV]
  simp

theorem sheetResidual_family_zero (i : Fin 4) :
    ∀ᶠ p in 𝓝 (0 : Common ξ × Triple), sheetResidual hξ (p.1,Pi.single i p.2) = 0 := by
  filter_upwards [eliminated_family_germ hξ i, sheetMap_family_germ hξ i,
    sheetMap_family_originalF_germ hξ i] with p he hs hz
  change AnalyticDerivative.originalF (literalCfg ξ + (reducedEmbedding hξ (p.1,Pi.single i p.2) : Cfg)) = 0
  rw [he,← hs]
  exact hz

theorem reducedQuadratic_single (i : Fin 4) (z : Triple) :
    reducedQuadratic hξ (Pi.single i z) = 0 := by
  have h := second_zero_of_linear_germ (sheetResidual hξ) (axisInclusion i)
    (sheetResidual_C2 hξ) (sheetResidual_family_zero hξ i) (0,z) (0,z)
  change fderiv ℝ (fderiv ℝ (sheetResidual hξ)) 0 (0,Pi.single i z) (0,Pi.single i z) = 0 at h
  simp only [reducedQuadratic,h,smul_zero]

def affineBook (z : Blocks) : Cfg := literalCfg ξ + familyDirection ξ hξ.1 z
def affineResidual (z : Blocks) : Residual := Option2.NativeStress.originalF (Pxi ξ + Vxi ξ hξ.1 z)
@[simp] theorem affineBook_zero : affineBook hξ 0 = literalCfg ξ := by simp [affineBook]
theorem affineBook_derivative (z : Blocks) : HasFDerivAt (affineBook hξ) (familyDirection ξ hξ.1) z :=
  (familyDirection ξ hξ.1).hasFDerivAt.const_add (literalCfg ξ)
theorem affineBook_C2 : ContDiff ℝ 2 (affineBook hξ) :=
  contDiff_const.add (familyDirection ξ hξ.1).contDiff

theorem affineResidual_native : affineResidual hξ = AnalyticDerivative.originalF ∘ affineBook hξ := by
  funext z
  have he : NativePolynomial.PartialAction.pack (affineBook hξ z) = Pxi ξ + Vxi ξ hξ.1 z := by
    change NativePolynomial.PartialAction.pack (literalCfg ξ) + phaseV ξ hξ.1 z = _
    rw [phaseV_eq_Vxi]
  change Option2.NativeStress.originalF (Pxi ξ + Vxi ξ hξ.1 z) =
    Option2.NativeStress.originalF (NativePolynomial.PartialAction.pack (affineBook hξ z))
  rw [he]

theorem affineResidual_C2 : ContDiffAt ℝ 2 (affineResidual hξ) 0 := by
  rw [affineResidual_native]
  exact (AnalyticDerivative.originalF_contDiff 2).contDiffAt.comp 0 (affineBook_C2 hξ).contDiffAt

theorem stress_reducedQuadratic_eq_affine {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (ell : Residual →L[ℝ] W)
    (hann : ell.comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg ξ)) = 0) (z : Blocks) :
    ell (reducedQuadratic hξ z) = ell ((1/2 : ℝ) •
      fderiv ℝ (fderiv ℝ (affineResidual hξ)) 0 z z) := by
  have hp := stress_half_quadratic_pullback_zero AnalyticDerivative.originalF (nativeEmbedding hξ) ell
    (AnalyticDerivative.originalF_contDiff 2).contDiffAt (nativeEmbedding_C2 hξ)
    (by simpa only [nativeEmbedding_zero] using hann) (0,z)
  have hred : ell (reducedQuadratic hξ z) = (1/2 : ℝ) • ell
      (fderiv ℝ (fderiv ℝ AnalyticDerivative.originalF) (literalCfg ξ)
        (normalProjXi ξ hξ.1 (familyDirection ξ hξ.1 z) : Cfg)
        (normalProjXi ξ hξ.1 (familyDirection ξ hξ.1 z) : Cfg)) := by
    simpa only [← sheetResidual_native, nativeEmbedding_zero, nativeEmbedding_Book_derivative,
      reducedQuadratic] using hp
  have ho := OrbitStressJet.originalF_sub_orbit_hessian ξ hξ.1
    (familyDirection ξ hξ.1 z)
    (familyDirection ξ hξ.1 z - (normalProjXi ξ hξ.1 (familyDirection ξ hξ.1 z) : Cfg))
    (familyDirection_mem_tangent hξ.1 z) (sub_normalProj_mem_orbit hξ.1 _) ell hann
  simp only [sub_sub_cancel] at ho
  rw [hred,ho]
  have ha := stress_half_quadratic_pullback_zero AnalyticDerivative.originalF (affineBook hξ) ell
    (AnalyticDerivative.originalF_contDiff 2).contDiffAt (affineBook_C2 hξ).contDiffAt
    (by simpa only [affineBook_zero] using hann) z
  simpa only [← affineResidual_native, affineBook_zero, (affineBook_derivative hξ 0).fderiv] using ha.symm

theorem stress_reducedQuadratic_of_reproduction {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (ell : Residual →L[ℝ] W) (Q : QuadraticMap ℝ Blocks W)
    (hann : ell.comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg ξ)) = 0)
    (hrepro : ∀ z, ell (Option2.NativeStress.originalF (Pxi ξ + Vxi ξ hξ.1 z)) = Q z) (z : Blocks) :
    ell (reducedQuadratic hξ z) = Q z := by
  rw [stress_reducedQuadratic_eq_affine hξ ell hann, map_smul,
    ← second_post_linear (affineResidual hξ) ell (affineResidual_C2 hξ)]
  have he : ell ∘ affineResidual hξ = Q := funext hrepro
  rw [he]
  exact half_hessian_quadratic Q z

theorem packed_annihilation_to_native {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (ell : Residual →L[ℝ] W)
    (hann : ell.comp (fderiv ℝ Option2.NativeStress.originalF (Pxi ξ)) = 0) :
    ell.comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg ξ)) = 0 := by
  have he : AnalyticDerivative.originalF = Option2.NativeStress.originalF ∘ packCLM := rfl
  rw [he, fderiv_comp _ (originalF_ambient_differentiable _) packCLM.differentiableAt,
    packCLM.fderiv, ← ContinuousLinearMap.comp_assoc]
  change (ell.comp (fderiv ℝ Option2.NativeStress.originalF (Pxi ξ))).comp packCLM = 0
  rw [hann,ContinuousLinearMap.zero_comp]

theorem H_reduced (z : Blocks) : residualHxi ξ hξ.1 (reducedQuadratic hξ z) = H z :=
  stress_reducedQuadratic_of_reproduction hξ _ H
    (packed_annihilation_to_native _ (residual_equilibrium ξ hξ.1).2)
    (H_reproduction_phase ξ hξ.1) z

theorem T_reduced (z : Blocks) : residualTxi ξ hξ.1 (reducedQuadratic hξ z) = T z :=
  stress_reducedQuadratic_of_reproduction hξ _ T
    (packed_annihilation_to_native _ (residual_equilibrium ξ hξ.1).1)
    (T_reproduction_phase ξ hξ.1) z

/-- Exact cone of the full reduced quadratic; both actual H/T contractions are discharged. -/
theorem reducedQuadratic_zero_cone (z : Blocks) :
    reducedQuadratic hξ z = 0 ↔ ∃ i : Fin 4, FourBlock.OnAxis i z := by
  constructor
  · intro hz
    apply (zero_cone z).mp
    constructor
    · rw [← H_reduced hξ z,hz,map_zero]
    · rw [← T_reduced hξ z,hz,map_zero]
  · rintro ⟨i,hi⟩
    have he : Pi.single i (z i) = z := by
      ext j
      by_cases hj : j = i
      · subst j; simp
      · simp [hj,hi j hj]
    rw [← he]
    exact reducedQuadratic_single hξ i (z i)

end Option2.NativeStress.PhaseReducedQuadratic
#print axioms Option2.NativeStress.PhaseReducedQuadratic.H_reduced
#print axioms Option2.NativeStress.PhaseReducedQuadratic.T_reduced
#print axioms Option2.NativeStress.PhaseReducedQuadratic.reducedQuadratic_zero_cone

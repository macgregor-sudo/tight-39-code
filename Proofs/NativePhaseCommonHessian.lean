module

public import NativePhaseRawBookFamily
public import OriginalResidualSmoothnessV2
public import StressHessianPullback

@[expose] public section

/-! The original residual's stress Hessian vanishes along each actual zero family.
The stress annihilation hypothesis removes nonlinear chart acceleration.
No H/T values or complex quadratic-coefficient identities are assumed here. -/

noncomputable section
set_option maxRecDepth 2000
namespace Option2.NativeStress.PhaseCommonHessianA6
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open AnalyticDerivative PhaseRawBookA6 BookHT
open HTPhaseComplete
open BookHT.NativeNormalKernelBridge (unpackNative)

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem zero_family_pullback (f : Cfg → Fin 2184 → ℝ) (g : RawParam → Cfg)
    (ell : (Fin 2184 → ℝ) →L[ℝ] W)
    (hf : ContDiffAt ℝ 2 f (g 0)) (hg : ContDiffAt ℝ 2 g 0)
    (hann : ell.comp (fderiv ℝ f (g 0)) = 0)
    (hz : f ∘ g = fun _ => 0) (u v : RawParam) :
    ell ((fderiv ℝ (fderiv ℝ f) (g 0)) ((fderiv ℝ g 0) u) ((fderiv ℝ g 0) v)) = 0 := by
  have h := SupportedStress.HessianPullback.stress_hessian_pullback_zero
    f g ell hf hg hann u v
  rw [hz] at h
  simpa only [fderiv_fun_const, fderiv_zero, Pi.zero_apply, zero_apply, map_zero] using h.symm

theorem rawMap_at_zero {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    rawMap ξ hξ H 0 = literalCfg ξ := by
  simp only [rawMap, Prod.fst_zero, Prod.snd_zero, groupChart_zero,
    actC_one, ContinuousLinearMap.id_apply, preMap_zero]

/-- Actual ambient Hessian, without the quadratic coefficient's factor 1/2. -/
def stressHessian (ξ : Fin 4 → ℂ) (ell : (Fin 2184 → ℝ) →L[ℝ] W) :
    Cfg →L[ℝ] Cfg →L[ℝ] W :=
  (ContinuousLinearMap.compL ℝ Cfg (Fin 2184 → ℝ) W ell).comp
    (fderiv ℝ (fderiv ℝ AnalyticDerivative.originalF) (literalCfg ξ))

set_option maxHeartbeats 200000 in
theorem stressHessian_rawDer_zero {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ)
    (H : Fin 4) (ell : (Fin 2184 → ℝ) →L[ℝ] W)
    (hann : ell.comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg ξ)) = 0) (u v : RawParam) :
    stressHessian ξ ell (rawDer ξ hξ H u) (rawDer ξ hξ H v) = 0 := by
  have hbase := rawMap_at_zero hξ H
  have hf : ContDiffAt ℝ 2 AnalyticDerivative.originalF (rawMap ξ hξ H 0) :=
    (originalF_contDiff 2).contDiffAt
  have hg : ContDiffAt ℝ 2 (rawMap ξ hξ H) 0 :=
    (analyticAt_rawMap hξ H).contDiffAt
  have hann' : ell.comp (fderiv ℝ AnalyticDerivative.originalF (rawMap ξ hξ H 0)) = 0 := by
    rwa [hbase]
  have hz : (AnalyticDerivative.originalF ∘ rawMap ξ hξ H) = fun _ => 0 :=
    funext (originalF_rawMap hξ H)
  have h := zero_family_pullback
    AnalyticDerivative.originalF (rawMap ξ hξ H) ell hf hg hann' hz u v
  rw [hbase] at h
  change ell ((fderiv ℝ (fderiv ℝ AnalyticDerivative.originalF) (literalCfg ξ))
    ((fderiv ℝ (rawMap ξ hξ H) 0) u) ((fderiv ℝ (rawMap ξ hξ H) 0) v)) = 0
  exact h

theorem stressHessian_family_range_zero {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ)
    (H : Fin 4) (ell : (Fin 2184 → ℝ) →L[ℝ] W)
    (hann : ell.comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg ξ)) = 0)
    {u v : Cfg} (hu : u ∈ LinearMap.range (rawDer ξ hξ H).toLinearMap)
    (hv : v ∈ LinearMap.range (rawDer ξ hξ H).toLinearMap) :
    stressHessian ξ ell u v = 0 := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  exact stressHessian_rawDer_zero hξ H ell hann a b

end Option2.NativeStress.PhaseCommonHessianA6

module

public import NativePhaseCommonHessian

@[expose] public section

/-! Common56 is in the radical of every equilibrium stress Hessian.
This uses actual zero-family tangents and the exact raw Book equivalence.
The result is a real Hessian identity, not yet a complex polynomial coefficient bridge. -/

noncomputable section
set_option maxRecDepth 2000
namespace Option2.NativeStress.PhaseCommonHessianA6
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open PhaseRawBookA6 BookHT HTPhaseComplete
open BookHT.NativeNormalKernelBridge (unpackNative)

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem bilinear_common_left_zero {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (B : Cfg →L[ℝ] Cfg →L[ℝ] W)
    (hfamily : ∀ (H : Fin 4) (u v : Cfg),
      u ∈ LinearMap.range (rawDer ξ hξ.1 H).toLinearMap →
      v ∈ LinearMap.range (rawDer ξ hξ.1 H).toLinearMap → B u v = 0)
    (o : orbitC ξ) (c : fixQK ξ) (x : tangentSpace ξ) :
    B ((o : Cfg) + (c : Cfg)) (x : Cfg) = 0 := by
  have hc (H : Fin 4) (a : orbitC ξ) (b : fixQK ξ) :
      (a : Cfg) + (b : Cfg) ∈ LinearMap.range (rawDer ξ hξ.1 H).toLinearMap := by
    simpa only [Pi.single_zero, rawBookEquiv_common] using
      rawBook_axis_mem_rawDer_range hξ H a b 0
  have ha (H : Fin 4) (u : Triple) :
      unpackNative (Vxi ξ hξ.1 (Pi.single H u)) ∈
        LinearMap.range (rawDer ξ hξ.1 H).toLinearMap := by
    simpa only [rawBookEquiv_book] using
      rawBook_axis_mem_rawDer_range hξ H 0 0 u
  obtain ⟨⟨⟨a,b⟩,z⟩, rfl⟩ := (rawBookEquiv hξ).surjective x
  rw [rawBookEquiv_coe, map_add, hfamily 0 _ _ (hc 0 o c) (hc 0 a b), zero_add]
  have hsum : unpackNative (Vxi ξ hξ.1 z) =
      ∑ H : Fin 4, unpackNative (Vxi ξ hξ.1 (Pi.single H (z H))) := by
    conv_lhs => rw [← Finset.univ_sum_single z]
    rw [map_sum, map_sum]
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun H _ => hfamily H _ _ (hc H o c) (ha H (z H))

theorem stressHessian_common_left_zero {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (ell : (Fin 2184 → ℝ) →L[ℝ] W)
    (hann : ell.comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg ξ)) = 0)
    (o : orbitC ξ) (c : fixQK ξ) (x : tangentSpace ξ) :
    stressHessian ξ ell ((o : Cfg) + (c : Cfg)) (x : Cfg) = 0 :=
  bilinear_common_left_zero hξ (stressHessian ξ ell)
    (fun H _ _ hu hv => stressHessian_family_range_zero hξ.1 H ell hann hu hv) o c x

theorem stressHessian_common_right_zero {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (ell : (Fin 2184 → ℝ) →L[ℝ] W)
    (hann : ell.comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg ξ)) = 0)
    (o : orbitC ξ) (c : fixQK ξ) (x : tangentSpace ξ) :
    stressHessian ξ ell (x : Cfg) ((o : Cfg) + (c : Cfg)) = 0 :=
  bilinear_common_left_zero hξ (stressHessian ξ ell).flip
    (fun H _ _ hu hv => stressHessian_family_range_zero hξ.1 H ell hann hv hu) o c x

theorem stressHessian_book_only {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (ell : (Fin 2184 → ℝ) →L[ℝ] W)
    (hann : ell.comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg ξ)) = 0)
    (o : orbitC ξ) (c : fixQK ξ) (z : Blocks) :
    stressHessian ξ ell (rawBookEquiv hξ ((o,c),z) : Cfg)
      (rawBookEquiv hξ ((o,c),z) : Cfg) =
    stressHessian ξ ell (unpackNative (Vxi ξ hξ.1 z))
      (unpackNative (Vxi ξ hξ.1 z)) := by
  have hl := stressHessian_common_left_zero hξ ell hann o c (rawBookEquiv hξ ((o,c),z))
  have hr := stressHessian_common_right_zero hξ ell hann o c (rawBookEquiv hξ ((0,0),z))
  rw [rawBookEquiv_book] at hr
  rw [rawBookEquiv_coe] at hl ⊢
  rw [map_add (stressHessian ξ ell), add_apply, hl, zero_add, map_add, hr, zero_add]

end Option2.NativeStress.PhaseCommonHessianA6

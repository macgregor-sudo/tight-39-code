module
public import PairingDefinitions
public import PairingA5Geometry
public import NativePhaseRealEndpoint
public import NativePhaseNormalForm
public import NativeExactFrameStability
@[expose] public section

noncomputable section
/- Compact definitions for the unchanged R and exact-frame hook endpoints.
Uses the completed concrete A5 maps and intrinsic normal slice. -/
namespace Option2StatementR
open CKM.NativeFirstOrder CKM.NativeTightCode CKM.NativeExactFrameEnergy
open Option2StatementA5Raw Option2StatementA5Slice Option2StatementA5
open scoped BigOperators Topology

end Option2StatementR

namespace Option2StatementR
open CKM.NativeFirstOrder CKM.NativeTightCode CKM.NativeExactFrameEnergy
open Option2StatementA5Raw Option2StatementA5Slice Option2StatementA5
open Filter Topology
theorem native_real_endpoint {ξ : Fin 4 → ℂ} (hξ : CKM.NativeFourFamily.IsGoodPhase ξ) :
    ∃ m : Product, NativeProduct m ∧
    ∃ σ : OpenPartialHomeomorph (derOf m × normal m ξ) Cfg,
      (0 : derOf m × normal m ξ) ∈ σ.source ∧ (∀ p, σ p = sliceChart m ξ p) ∧
    ∃ (Uraw : Fin 4 → Set (RawParam62 m)) (Vraw : Fin 4 → Set SliceParam),
      (∀ i, Uraw i ∈ 𝓝 0) ∧ (∀ i, Vraw i ∈ 𝓝 0) ∧
      rawUnion m ξ hξ.1 Uraw =ᶠ[𝓝 (literalCfg ξ)]
        saturation (sliceUnion σ hξ.1 Vraw) ∧
      (∀ᶠ y : Cfg in 𝓝 (literalCfg ξ),
        Option2StatementResidual.originalF y = 0 ↔ y ∈ rawUnion m ξ hξ.1 Uraw) ∧
      (∀ α : ℝ, 1/2 < α →
        (¬ ∃ (W : Set Cfg) (C : ℝ), W ∈ 𝓝 (literalCfg ξ) ∧ 0 < C ∧
          ∀ y ∈ W, Metric.infDist y (saturation (sliceUnion σ hξ.1 Vraw)) ≤
            C * ‖Option2StatementResidual.originalF y‖ ^ α) ∧
        (¬ ∃ (W : Set Cfg) (C : ℝ), W ∈ 𝓝 (literalCfg ξ) ∧ 0 < C ∧
          ∀ y ∈ W, traceInfDist y (saturation (sliceUnion σ hξ.1 Vraw)) ≤
            C * ‖Option2StatementResidual.originalF y‖ ^ α)) ∧
      ∃ U : Set Cfg, IsOpen U ∧ nativeOrbit ξ ⊆ U ∧ ∃ M : ℝ, 0 < M ∧
        ∀ y ∈ U,
          Metric.infDist y (saturation (sliceUnion σ hξ.1 Vraw))^2 ≤
            M * ‖Option2StatementResidual.originalF y‖ ∧
          traceInfDist y (saturation (sliceUnion σ hξ.1 Vraw))^2 ≤
            (2116 * M) * ‖Option2StatementResidual.originalF y‖ ∧
          (Option2StatementResidual.originalF y = 0 ↔
            y ∈ saturation (sliceUnion σ hξ.1 Vraw)) := by
  refine ⟨CKM.NativeGroupSlice.prodC, CKM.NativeGroupSlice.prodC_eq_native,
    CKM.NativeGroupSlice.slicePH ξ hξ.1, CKM.NativeGroupSlice.zero_mem_slicePH_source ξ hξ.1,
    (fun _ => rfl), ?_⟩
  have hf : Option2StatementResidual.originalF = Option2.NativeStress.AnalyticDerivative.originalF :=
    funext Option2StatementResidual.originalF_eq_native
  simp only [hf, Option2StatementA5.saturation_eq_native, Option2StatementA5.nativeOrbit_eq_native]
  exact Option2.NativeStress.PhaseRealEndpoint.native_real_endpoint hξ


theorem normal_form_exists {ξ : Fin 4 → ℂ} (hξ : CKM.NativeFourFamily.IsGoodPhase ξ) :
    ∃ m : Product, NativeProduct m ∧
    ∃ σ : OpenPartialHomeomorph (derOf m × normal m ξ) Cfg,
      (0 : derOf m × normal m ξ) ∈ σ.source ∧ (∀ p, σ p = sliceChart m ξ p) ∧
      NormalForm m ξ hξ.1 σ := by
  refine ⟨CKM.NativeGroupSlice.prodC, CKM.NativeGroupSlice.prodC_eq_native,
    CKM.NativeGroupSlice.slicePH ξ hξ.1, CKM.NativeGroupSlice.zero_mem_slicePH_source ξ hξ.1,
    (fun _ => rfl), ?_⟩
  unfold NormalForm
  have hf : Option2StatementResidual.originalF = Option2.NativeStress.AnalyticDerivative.originalF :=
    funext Option2StatementResidual.originalF_eq_native
  rw [hf]
  refine ⟨CKM.NativeFourFamily.fixQK ξ,
    (CKM.NativeFourFamily.range_sliceCommonDer hξ).symm,
    CKM.NativeFourFamily.finrank_fixQK hξ,
    CKM.NativeSliceNormalSplitting.normalRange ξ, rfl,
    CKM.NativeSliceNormalSplitting.finrank_normalRange hξ,
    Option2.NativeStress.PhaseRangeReduction.reducedPH hξ,
    Option2.NativeStress.PhaseRangeReduction.reducedPH_zero hξ, ?_, ?_⟩
  · refine ⟨Option2.NativeStress.PhaseSheetChart.familyParam hξ,
      Option2.NativeStress.PhaseSheetChart.familyParam_zero hξ, ?_, ?_⟩
    · intro i
      exact (Option2.NativeStress.PhaseSheetChart.familyParam_analytic hξ i).contDiffAt
    · intro i
      exact Option2.NativeStress.PhaseRangeReduction.eliminated_family_germ hξ i
  · exact Option2.NativeStress.PhaseNormalForm.normal_form_homeomorph hξ


theorem native_exact_frame_quartic_stability_near_orbit {ξ : Fin 4 → ℂ}
    (hξ : CKM.NativeFourFamily.IsGoodPhase ξ)
    (φ : ℝ → ℝ) (I : Set ℝ) (hI : IsOpen I) (hconvex : Convex ℝ I)
    (hφ : ContDiffOn ℝ 2 φ I) (hbase : (1 / 3 : ℝ) ∈ I)
    (m M : ℝ) (hm : 0 < m)
    (hcurv : ∀ x ∈ I, m ≤ deriv (deriv φ) x ∧ deriv (deriv φ) x ≤ M) :
    ∃ algebra : Product, NativeProduct algebra ∧
    ∃ σ : OpenPartialHomeomorph (derOf algebra × normal algebra ξ) Cfg,
      (0 : derOf algebra × normal algebra ξ) ∈ σ.source ∧
      (∀ p, σ p = sliceChart algebra ξ p) ∧
    ∃ Vraw : Fin 4 → Set SliceParam, (∀ i, Vraw i ∈ 𝓝 0) ∧
      ∃ U : Set Cfg, IsOpen U ∧ nativeOrbit ξ ⊆ U ∧
        ∃ c : ℝ, 0 < c ∧ ∀ y ∈ U, ExactFrames y →
          c * Metric.infDist y (saturation (sliceUnion σ hξ.1 Vraw)) ^ 4 ≤
            E39 φ (codePoint y) - E0 φ ∧
          c * traceInfDist y (saturation (sliceUnion σ hξ.1 Vraw)) ^ 4 ≤
            E39 φ (codePoint y) - E0 φ ∧
          (Option2StatementResidual.originalF y = 0 ↔
            y ∈ saturation (sliceUnion σ hξ.1 Vraw)) := by
  refine ⟨CKM.NativeGroupSlice.prodC, CKM.NativeGroupSlice.prodC_eq_native,
    CKM.NativeGroupSlice.slicePH ξ hξ.1, CKM.NativeGroupSlice.zero_mem_slicePH_source ξ hξ.1,
    (fun _ => rfl), ?_⟩
  have hf : Option2StatementResidual.originalF = Option2.NativeStress.AnalyticDerivative.originalF :=
    funext Option2StatementResidual.originalF_eq_native
  simp only [hf, Option2StatementA5.saturation_eq_native, Option2StatementA5.nativeOrbit_eq_native]
  exact CKM.NativeOverlapLossHook.native_exact_frame_quartic_stability_near_orbit
    hξ φ I hI hconvex hφ hbase m M hm hcurv

end Option2StatementR

#print axioms Option2StatementR.native_real_endpoint
#print axioms Option2StatementR.normal_form_exists
#print axioms Option2StatementR.native_exact_frame_quartic_stability_near_orbit

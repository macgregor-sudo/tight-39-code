module

public import NativePhaseSharpExponent

@[expose] public section

/-! Coherent real endpoint on every good phase: original-equation exhaustion,
whole-orbit neighborhood residual bounds, and sharp ambient exponent, all for
the same actual localized four-family saturation. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.PhaseRealEndpoint
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily CKM.NativeOrbitErrorTransfer
open PhaseOrbitBound
open Filter Topology
variable {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)

/-- Every good phase has a full native-orbit neighborhood estimate and exact
raw-family zero germ. Constants may depend on the phase; the residual exponent one-half is sharp in both explicit ambient metrics. -/
theorem native_real_endpoint :
    ∃ (Uraw : Fin 4 → Set RawParam62) (Vraw : Fin 4 → Set SliceParam),
      (∀ i, Uraw i ∈ 𝓝 0) ∧ (∀ i, Vraw i ∈ 𝓝 0) ∧
      rawUnion ξ hξ.1 Uraw =ᶠ[𝓝 (literalCfg ξ)]
        saturation (sliceUnion ξ hξ.1 Vraw) ∧
      (∀ᶠ y : Cfg in 𝓝 (literalCfg ξ),
        AnalyticDerivative.originalF y = 0 ↔ y ∈ rawUnion ξ hξ.1 Uraw) ∧
      (∀ α : ℝ, 1/2 < α →
        (¬ ∃ (W : Set Cfg) (C : ℝ), W ∈ 𝓝 (literalCfg ξ) ∧ 0 < C ∧
          ∀ y ∈ W, Metric.infDist y (saturation (sliceUnion ξ hξ.1 Vraw)) ≤
            C * ‖AnalyticDerivative.originalF y‖ ^ α) ∧
        (¬ ∃ (W : Set Cfg) (C : ℝ), W ∈ 𝓝 (literalCfg ξ) ∧ 0 < C ∧
          ∀ y ∈ W, traceInfDist y (saturation (sliceUnion ξ hξ.1 Vraw)) ≤
            C * ‖AnalyticDerivative.originalF y‖ ^ α)) ∧
      ∃ U : Set Cfg, IsOpen U ∧ nativeOrbit ξ ⊆ U ∧ ∃ M : ℝ, 0 < M ∧
        ∀ y ∈ U,
          Metric.infDist y (saturation (sliceUnion ξ hξ.1 Vraw))^2 ≤
            M * ‖AnalyticDerivative.originalF y‖ ∧
          traceInfDist y (saturation (sliceUnion ξ hξ.1 Vraw))^2 ≤
            (2116 * M) * ‖AnalyticDerivative.originalF y‖ ∧
          (AnalyticDerivative.originalF y = 0 ↔
            y ∈ saturation (sliceUnion ξ hξ.1 Vraw)) := by
  obtain ⟨Uraw, Vraw, hUraw, hVraw, hfamilyzero, hgerm⟩ := raw_saturation_germ ξ hξ
  obtain ⟨V, hV, hsub, r, C, hr, hC, hnormal⟩ := normal_control_inside hξ Vraw hVraw
  obtain ⟨U, hU, hOrbit, M, hM, hbound⟩ :=
    orbit_transfer_from_smaller_family ξ hξ V Vraw hV hsub hfamilyzero r C hr hC hnormal
  have hP : literalCfg ξ ∈ U := by
    apply hOrbit
    apply (mem_saturation {literalCfg ξ} _).mpr
    refine ⟨1, one_mem_autOf prodC, literalCfg ξ, Set.mem_singleton _, ?_⟩
    rw [actC_one]
    rfl
  have hrawzero : ∀ᶠ y : Cfg in 𝓝 (literalCfg ξ),
      AnalyticDerivative.originalF y = 0 ↔ y ∈ rawUnion ξ hξ.1 Uraw := by
    have hg := hgerm
    rw [Filter.eventuallyEqSet_iff] at hg
    filter_upwards [hU.mem_nhds hP, hg] with y hy hgy
    exact (hbound y hy).2.trans hgy.symm
  have hs : (saturation (sliceUnion ξ hξ.1 Vraw)).Nonempty := by
    obtain ⟨x, hx⟩ := sliceUnion_nonempty ξ hξ.1 Vraw hVraw
    refine ⟨x, (mem_saturation _ _).mpr ⟨1, one_mem_autOf prodC, x, hx, ?_⟩⟩
    rw [actC_one]
    rfl
  have hsz : ∀ y ∈ saturation (sliceUnion ξ hξ.1 Vraw), AnalyticDerivative.originalF y = 0 := by
    intro y hy
    obtain ⟨A,hA,x,hx,rfl⟩ := (mem_saturation _ y).mp hy
    exact (originalF_actC_eq_zero_iff hA x).mpr (hfamilyzero x hx)
  have hsharp := PhaseSharpness.no_better_ambient_exponent hξ
    (saturation (sliceUnion ξ hξ.1 Vraw)) hs hsz
  refine ⟨Uraw, Vraw, hUraw, hVraw, hgerm, hrawzero, ?_, U, hU, hOrbit, M, hM, ?_⟩
  · intro α hα
    refine ⟨hsharp α hα,?_⟩
    rintro ⟨W,C,hW,hC,hb⟩
    exact hsharp α hα ⟨W,C,hW,hC,fun y hy => (traceInfDist_comparison y _ hs).1.trans (hb y hy)⟩
  · intro y hy
    obtain ⟨hd, hz⟩ := hbound y hy
    refine ⟨hd, ?_, hz⟩
    have hc := (traceInfDist_comparison y _ hs).2
    have hsq := pow_le_pow_left₀ (traceInfDist_nonneg y _ hs) hc 2
    nlinarith

end Option2.NativeStress.PhaseRealEndpoint
#print axioms Option2.NativeStress.PhaseRealEndpoint.native_real_endpoint

module

public import NativePhaseNormalExhaustion
public import NativeOrbitTraceMetric

@[expose] public section

/-! All-good-phase native normal-to-orbit composition. Every analytic premise
of the existing orbit transfer is discharged by the actual nonlinear chart,
original residual and native four-family union. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.PhaseOrbitBound
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily CKM.NativeOrbitErrorTransfer
open Filter Topology
variable {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)

/-- Literal definition equality, including the actual phase proof and native slice parametrization. -/
theorem actualFamilyUnion_eq_sliceUnion (V : Fin 4 → Set SliceParam) :
    PhaseSheetDistance.actualFamilyUnion hξ V = sliceUnion ξ hξ.1 V := rfl

/-- Reconcile the exact raw-descent neighborhoods with the normal-exhaustion neighborhoods.
The family neighborhoods are intersected, and the two positive native radii are minimized.
This supplies every normal-local input, with no reproduction premise left. -/
theorem normal_control_inside (Vraw : Fin 4 → Set SliceParam) (hraw : ∀ i, Vraw i ∈ 𝓝 0) :
    ∃ V : Fin 4 → Set SliceParam, (∀ i, V i ∈ 𝓝 0) ∧ (∀ i, V i ⊆ Vraw i) ∧
      ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
        ∀ n : normalC ξ, ‖n‖ < r →
          Metric.infDist (literalCfg ξ + (n : Cfg))
              (sliceUnion ξ hξ.1 V)^2 ≤
            C * ‖AnalyticDerivative.originalF (literalCfg ξ + (n : Cfg))‖ ∧
          (AnalyticDerivative.originalF (literalCfg ξ + (n : Cfg)) = 0 ↔
            literalCfg ξ + (n : Cfg) ∈ sliceUnion ξ hξ.1 V) := by
  obtain ⟨V0, hV0, hzero⟩ := PhaseNormalExhaustion.local_normal_zero_iff_family hξ
  let V : Fin 4 → Set SliceParam := fun i => Vraw i ∩ V0 i
  have hV : ∀ i, V i ∈ 𝓝 0 := fun i => inter_mem (hraw i) (hV0 i)
  have hVr : ∀ i, V i ⊆ Vraw i := fun _ => Set.inter_subset_left
  have hVn : ∀ i, V i ⊆ V0 i := fun _ => Set.inter_subset_right
  obtain ⟨rb, C, hrb, hC, hbound⟩ := PhaseFullNormalBound.local_normal_family_bound hξ V hV
  obtain ⟨rz, hrz, hz⟩ := hzero V hV hVn
  refine ⟨V, hV, hVr, min rb rz, C, lt_min hrb hrz, hC, ?_⟩
  intro n hn
  have hb := (hbound n (lt_of_lt_of_le hn (min_le_left rb rz))).2
  have he := (hz n (lt_of_lt_of_le hn (min_le_right rb rz))).2
  simpa only [actualFamilyUnion_eq_sliceUnion] using And.intro hb he

/-- Every good phase has a full native-orbit neighborhood estimate and exact
raw-family zero germ. Constants may depend on the phase; no sharpness is asserted. -/
theorem phase_orbit_bound :
    ∃ (Uraw : Fin 4 → Set RawParam62) (Vraw : Fin 4 → Set SliceParam),
      (∀ i, Uraw i ∈ 𝓝 0) ∧ (∀ i, Vraw i ∈ 𝓝 0) ∧
      rawUnion ξ hξ.1 Uraw =ᶠ[𝓝 (literalCfg ξ)]
        saturation (sliceUnion ξ hξ.1 Vraw) ∧
      (∀ᶠ y : Cfg in 𝓝 (literalCfg ξ),
        AnalyticDerivative.originalF y = 0 ↔ y ∈ rawUnion ξ hξ.1 Uraw) ∧
      ∃ U : Set Cfg, IsOpen U ∧ nativeOrbit ξ ⊆ U ∧ ∃ M : ℝ, 0 < M ∧
        ∀ y ∈ U,
          Metric.infDist y (saturation (sliceUnion ξ hξ.1 Vraw))^2 ≤
            M * ‖AnalyticDerivative.originalF y‖ ∧
          traceInfDist y (saturation (sliceUnion ξ hξ.1 Vraw))^2 ≤
            (2116 * M) * ‖AnalyticDerivative.originalF y‖ ∧
          (AnalyticDerivative.originalF y = 0 ↔
            y ∈ saturation (sliceUnion ξ hξ.1 Vraw)) := by
  obtain ⟨Uraw, Vraw, hUraw, hVraw, hgerm, htransfer⟩ := raw_orbit_transfer ξ hξ
  obtain ⟨V, hV, hsub, r, C, hr, hC, hnormal⟩ := normal_control_inside hξ Vraw hVraw
  obtain ⟨U, hU, hOrbit, M, hM, hbound⟩ := htransfer V hV hsub r C hr hC hnormal
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
  refine ⟨Uraw, Vraw, hUraw, hVraw, hgerm, hrawzero, U, hU, hOrbit, M, hM, ?_⟩
  intro y hy
  obtain ⟨hd, hz⟩ := hbound y hy
  refine ⟨hd, ?_, hz⟩
  have hc := (traceInfDist_comparison y _ hs).2
  have hsq := pow_le_pow_left₀ (traceInfDist_nonneg y _ hs) hc 2
  nlinarith

end Option2.NativeStress.PhaseOrbitBound
#print axioms Option2.NativeStress.PhaseOrbitBound.phase_orbit_bound

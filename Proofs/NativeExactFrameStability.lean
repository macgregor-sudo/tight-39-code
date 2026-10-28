module

public import NativeExactFrameResidual
public import NativePhaseRealEndpoint
public import NativeExactFrameNeighborhood

@[expose] public section

/-! Quartic stability on the canonical native exact-frame class. -/
noncomputable section

namespace CKM.NativeOverlapLossHook

/-- Scalar composition; the coefficient is positive and retains all comparison constants. -/
theorem quartic_of_squared_residual_bound (d f D gap C b m : ℝ)
    (hC : 0 < C) (hb : 0 < b) (hm : 0 < m)
    (hd : d ^ 2 ≤ C * f)
    (hres : f ^ 2 ≤ b ^ 2 * D) (hgap : (m / 2) * D ≤ gap) :
    0 < m / (2 * C ^ 2 * b ^ 2) ∧
      (m / (2 * C ^ 2 * b ^ 2)) * d ^ 4 ≤ gap := by
  have hsq : d ^ 4 ≤ C ^ 2 * f ^ 2 := by
    have h := mul_self_le_mul_self (sq_nonneg d) hd
    nlinarith
  have hbound : d ^ 4 ≤ C ^ 2 * b ^ 2 * D := by
    have h := mul_le_mul_of_nonneg_left hres (sq_nonneg C)
    nlinarith
  constructor
  · positivity
  · have hden : 0 < 2 * C ^ 2 * b ^ 2 := by positivity
    have h := mul_le_mul_of_nonneg_left hbound (show 0 ≤ m / (2 * C ^ 2 * b ^ 2) by positivity)
    have heq : m / (2 * C ^ 2 * b ^ 2) * (C ^ 2 * b ^ 2 * D) = (m / 2) * D := by
      field_simp
    exact (h.trans_eq heq).trans hgap

open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeOrbitErrorTransfer CKM.NativeTightCode CKM.NativeExactFrameEnergy
open SupportedStress.NativeFrames Option2.NativeStress
open Filter Topology

/-- On the canonical exact-frame class, the native energy gap controls the fourth
powers of both distances to the same actual localized four-family saturation.
The coefficient and orbit neighborhood may depend on the good phase. The overlap
domain is explicit; no restricted sharpness or unrestricted energy claim is made. -/
theorem native_exact_frame_quartic_stability {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (φ : ℝ → ℝ) (I : Set ℝ) (hI : IsOpen I) (hconvex : Convex ℝ I)
    (hφ : ContDiffOn ℝ 2 φ I) (hbase : (1 / 3 : ℝ) ∈ I)
    (m M : ℝ) (hm : 0 < m)
    (hcurv : ∀ x ∈ I, m ≤ deriv (deriv φ) x ∧ deriv (deriv φ) x ≤ M) :
    ∃ Vraw : Fin 4 → Set SliceParam, (∀ i, Vraw i ∈ 𝓝 0) ∧
      ∃ U : Set Cfg, IsOpen U ∧ nativeOrbit ξ ⊆ U ∧
        ∃ c : ℝ, 0 < c ∧ ∀ y ∈ U, ExactFrames y →
          (∀ k : ThirteenCrossPair,
            thirteenCrossOverlap (framesOf literalLabel (codePoint y)) k ∈ I) →
          c * Metric.infDist y (saturation (sliceUnion ξ hξ.1 Vraw)) ^ 4 ≤
            E39 φ (codePoint y) - E0 φ ∧
          c * traceInfDist y (saturation (sliceUnion ξ hξ.1 Vraw)) ^ 4 ≤
            E39 φ (codePoint y) - E0 φ ∧
          (AnalyticDerivative.originalF y = 0 ↔
            y ∈ saturation (sliceUnion ξ hξ.1 Vraw)) := by
  obtain ⟨Uraw, Vraw, hUraw, hVraw, hgerm, hzero, hsharp,
    U, hU, hOrbit, C, hC, hbound⟩ := PhaseRealEndpoint.native_real_endpoint hξ
  have hCt : 0 < 2116 * C := by positivity
  refine ⟨Vraw, hVraw, U, hU, hOrbit, m / (2 * (2116 * C) ^ 2 * 1 ^ 2),
    by positivity, ?_⟩
  intro y hy hframe hnear
  obtain ⟨hd, ht, hz⟩ := hbound y hy
  have hd' : Metric.infDist y (saturation (sliceUnion ξ hξ.1 Vraw)) ^ 2 ≤
      (2116 * C) * ‖AnalyticDerivative.originalF y‖ := by
    have hn := norm_nonneg (AnalyticDerivative.originalF y)
    nlinarith
  have hr := originalF_norm_sq_le_cross_defect y hframe
  have he := (native_energy_sandwich (codePoint y) literalLabel hframe
    φ I hI hconvex hφ hbase m M hm hcurv hnear).1
  have hr' : ‖AnalyticDerivative.originalF y‖ ^ 2 ≤
      (1 : ℝ) ^ 2 * D (framesOf literalLabel (codePoint y)) := by simpa using hr
  exact ⟨(quartic_of_squared_residual_bound _ _ _ _ _ 1 m hCt (by norm_num)
    hm hd' hr' he).2,
    (quartic_of_squared_residual_bound _ _ _ _ _ 1 m hCt (by norm_num)
    hm ht hr' he).2, hz⟩

/-- Shrinking the whole-orbit neighborhood makes the cross-overlap domain automatic.
Only the canonical exact-frame restriction remains on each configuration. -/
theorem native_exact_frame_quartic_stability_near_orbit {ξ : Fin 4 → ℂ}
    (hξ : IsGoodPhase ξ)
    (φ : ℝ → ℝ) (I : Set ℝ) (hI : IsOpen I) (hconvex : Convex ℝ I)
    (hφ : ContDiffOn ℝ 2 φ I) (hbase : (1 / 3 : ℝ) ∈ I)
    (m M : ℝ) (hm : 0 < m)
    (hcurv : ∀ x ∈ I, m ≤ deriv (deriv φ) x ∧ deriv (deriv φ) x ≤ M) :
    ∃ Vraw : Fin 4 → Set SliceParam, (∀ i, Vraw i ∈ 𝓝 0) ∧
      ∃ U : Set Cfg, IsOpen U ∧ nativeOrbit ξ ⊆ U ∧
        ∃ c : ℝ, 0 < c ∧ ∀ y ∈ U, ExactFrames y →
          c * Metric.infDist y (saturation (sliceUnion ξ hξ.1 Vraw)) ^ 4 ≤
            E39 φ (codePoint y) - E0 φ ∧
          c * traceInfDist y (saturation (sliceUnion ξ hξ.1 Vraw)) ^ 4 ≤
            E39 φ (codePoint y) - E0 φ ∧
          (AnalyticDerivative.originalF y = 0 ↔
            y ∈ saturation (sliceUnion ξ hξ.1 Vraw)) := by
  obtain ⟨Vraw, hVraw, U, hU, hOrbit, c, hc, hbound⟩ :=
    native_exact_frame_quartic_stability hξ φ I hI hconvex hφ hbase m M hm hcurv
  obtain ⟨N, hN, hNOrbit, hNP, hnear⟩ :=
    native_cross_overlap_neighborhood ξ hξ.1 I hI hbase
  exact ⟨Vraw, hVraw, U ∩ N, hU.inter hN,
    fun y hy => ⟨hOrbit hy, hNOrbit hy⟩, c, hc,
    fun y hy hframe => hbound y hy.1 hframe (hnear y hy.2)⟩

end CKM.NativeOverlapLossHook

#print axioms CKM.NativeOverlapLossHook.quartic_of_squared_residual_bound
#print axioms CKM.NativeOverlapLossHook.native_exact_frame_quartic_stability
#print axioms CKM.NativeOverlapLossHook.native_exact_frame_quartic_stability_near_orbit

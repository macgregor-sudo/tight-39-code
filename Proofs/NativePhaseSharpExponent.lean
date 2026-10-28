module

public import NativePhaseSharpness
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section

/-! The exponent one-half cannot be improved on any ambient neighborhood,
for any nonempty subset of the actual original-equation zero set. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.PhaseSharpness
open CKM.NativeFirstOrder CKM.NativeFourFamily CKM.NativeGroupSlice
open Filter Topology
variable {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)

theorem no_better_curve_exponent (S : Set Cfg) (hS : S.Nonempty)
    (hz : ∀ y ∈ S, AnalyticDerivative.originalF y = 0)
    (α : ℝ) (hα : 1/2 < α) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in 𝓝[>] 0,
      Metric.infDist (witnessCurve hξ t) S ≤ C * ‖AnalyticDerivative.originalF (witnessCurve hξ t)‖ ^ α := by
  obtain ⟨c,hc,hlower⟩ := native_zero_set_lower_bound hξ
  obtain ⟨B,hB,hupper⟩ := witness_residual_bound hξ
  rintro ⟨C,hC,hbound⟩
  have hk : 0 < 2*α-1 := by linarith
  have hlim : Tendsto (fun t : ℝ => (C*B^α)*t^(2*α-1)) (𝓝[>] 0) (𝓝 0) := by
    have ht := (Real.continuousAt_rpow_const 0 (2*α-1) (Or.inr hk.le)).tendsto
    simpa only [Real.zero_rpow hk.ne',mul_zero] using
      (tendsto_const_nhds.mul ht).mono_left nhdsWithin_le_nhds
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0, c ≤ (C*B^α)*t^(2*α-1) := by
    filter_upwards [hbound, hupper.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hb hu ht
    have ht' : 0 < t := ht
    have hp := Real.rpow_le_rpow (norm_nonneg _) hu (by linarith : 0 ≤ α)
    rw [Real.mul_rpow hB.le (sq_nonneg t),← Real.rpow_natCast_mul ht'.le 2 α] at hp
    have hlo := hlower S hS hz t ht'
    have hi : c*t ≤ (C*B^α)*t^(2*α) := by
      calc
        c*t ≤ Metric.infDist (witnessCurve hξ t) S := hlo
        _ ≤ C * ‖AnalyticDerivative.originalF (witnessCurve hξ t)‖ ^ α := hb
        _ ≤ C*(B^α*t^(2*α)) := mul_le_mul_of_nonneg_left hp hC.le
        _ = _ := by ring
    have hpow : t^(2*α) = t^(2*α-1)*t := by
      calc
        t^(2*α) = t^((2*α-1)+1) := by congr 1; ring
        _ = t^(2*α-1)*t := by rw [Real.rpow_add ht',Real.rpow_one]
    rw [hpow,← mul_assoc] at hi
    nlinarith
  exact (not_le_of_gt hc) (ge_of_tendsto hlim hevent)

include hξ in
theorem no_better_ambient_exponent (S : Set Cfg) (hS : S.Nonempty)
    (hz : ∀ y ∈ S, AnalyticDerivative.originalF y = 0)
    (α : ℝ) (hα : 1/2 < α) :
    ¬ ∃ (U : Set Cfg) (C : ℝ), U ∈ 𝓝 (literalCfg ξ) ∧ 0 < C ∧
      ∀ y ∈ U, Metric.infDist y S ≤ C * ‖AnalyticDerivative.originalF y‖ ^ α := by
  rintro ⟨U,C,hU,hC,hbound⟩
  apply no_better_curve_exponent hξ S hS hz α hα
  have ht : Tendsto (witnessCurve hξ) (𝓝 (0 : ℝ)) (𝓝 (literalCfg ξ)) := by
    have hc : Continuous (witnessCurve hξ) := continuous_const.add (continuous_id.smul continuous_const)
    simpa only [witnessCurve,zero_smul,add_zero] using hc.continuousAt.tendsto (x := 0)
  exact ⟨C,hC,((ht.eventually hU).mono fun t ht => hbound _ ht).filter_mono nhdsWithin_le_nhds⟩

end Option2.NativeStress.PhaseSharpness
#print axioms Option2.NativeStress.PhaseSharpness.no_better_ambient_exponent

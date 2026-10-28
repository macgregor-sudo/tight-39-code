module

public import NativePhaseOrbitBound
public import Mathlib.Analysis.Calculus.Taylor

@[expose] public section

/-! A stationary native quadratic separates a transverse curve from every
original-equation zero, including the full saturated family union. -/
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Option2.NativeStress.PhaseSharpness
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily CKM.NativeOrbitErrorTransfer
open BookHT HTPhaseComplete AnalyticDerivative NativePolynomial.PartialAction
open Filter Topology
open scoped BigOperators

/-- Homogeneous separation controls distance to any nonempty subset of zeros,
without compactness, local closedness or localization of that subset. -/
theorem homogeneous_zero_distance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : E → ℂ) (hq : Continuous q)
    (hhom : ∀ (t : ℝ) (x : E), q (t • x) = (t : ℂ)^2 * q x)
    (P v : E) (hv : q v ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (S : Set E), S.Nonempty →
      (∀ y ∈ S, q (y-P) = 0) → ∀ t : ℝ, 0 < t →
        c*t ≤ Metric.infDist (P+t•v) S := by
  have hn : {x | q x ≠ 0} ∈ 𝓝 v := (isOpen_compl_singleton.preimage hq).mem_nhds hv
  obtain ⟨c,hc,hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨c,hc,?_⟩
  intro S hS hz t ht
  apply (Metric.le_infDist hS).mpr
  intro y hy
  let w : E := t⁻¹ • (y-P)
  have hqw : q w = 0 := by rw [hhom,hz y hy,mul_zero]
  have hd : c ≤ dist v w := by
    by_contra! h
    have hw : w ∈ Metric.ball v c := by simpa only [Metric.mem_ball,dist_comm] using h
    exact hball hw hqw
  have htw : t • w = y-P := by
    dsimp [w]
    rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  have he : P+t•v-y = t • (v-w) := by rw [smul_sub,htw]; abel
  rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
  simpa only [dist_eq_norm,mul_comm] using mul_le_mul_of_nonneg_left hd ht.le

variable {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)

def witnessBlocks : Blocks := fun _ => WithLp.toLp 2 (fun _ => (1 : ℂ))
def witnessDirection : Cfg := familyDirection ξ hξ.1 witnessBlocks
def separatingQuadratic (v : Cfg) : ℂ :=
  stressCovector (ellH ξ hξ.1 0 0) (AnalyticDerivative.originalF (literalCfg ξ+v))

theorem witness_H : (H witnessBlocks 0).ofLp 0 = 1 := by
  norm_num [H,HValue,witnessBlocks,QuadraticMap.ofPolar]

theorem separatingQuadratic_continuous : Continuous (separatingQuadratic hξ) := by
  exact (stressCovector (ellH ξ hξ.1 0 0)).continuous.comp
    (originalF_ambient_differentiable.continuous.comp
      (packCLM.continuous.comp (continuous_const.add continuous_id)))

theorem separatingQuadratic_homogeneous (t : ℝ) (v : Cfg) :
    separatingQuadratic hξ (t•v) = (t : ℂ)^2 * separatingQuadratic hξ v := by
  have hline (s : ℝ) := transported_line ξ hξ.1 0 0 (pack v) s
  have h1 := hline 1
  rw [one_smul,Complex.ofReal_one,one_pow,one_mul] at h1
  have he (s : ℝ) : separatingQuadratic hξ (s•v) =
      HTPhaseKron.mono (Ux ξ hξ.1) (HTPhaseKron.Ex.neg (cExp 0 0)) *
        stressCovector (ellRaw ξ hξ.1 0 0)
          (Option2.NativeStress.originalF (packCLM (literalCfg ξ) + s • packCLM v)) := by
    unfold separatingQuadratic ellH
    rw [stressCovector_smul]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    congr 1
  simp only [packCLM_apply] at he
  rw [he, hline]
  have hv1 : separatingQuadratic hξ v =
      HTPhaseKron.mono (Ux ξ hξ.1) (HTPhaseKron.Ex.neg (cExp 0 0)) *
        stressCovector (ellRaw ξ hξ.1 0 0)
          (Option2.NativeStress.originalF (packCLM (literalCfg ξ) + packCLM v)) := by
    simpa only [one_smul,packCLM_apply] using he 1
  simp only [packCLM_apply] at hv1
  rw [hv1,h1]
  ring

theorem separatingQuadratic_witness : separatingQuadratic hξ (witnessDirection hξ) = 1 := by
  have he := congrArg (fun z : Blocks => (z 0).ofLp 0)
    (H_reproduction_phase ξ hξ.1 witnessBlocks)
  rw [witness_H] at he
  change (residualHxi ξ hξ.1 (Option2.NativeStress.originalF
    (packCLM (literalCfg ξ) + Vxi ξ hξ.1 witnessBlocks)) 0).ofLp 0 = 1 at he
  rw [residualHxi,residualOf_apply,← stressCovector_apply] at he
  change stressCovector (ellH ξ hξ.1 0 0)
    (Option2.NativeStress.originalF (packCLM (literalCfg ξ + familyDirection ξ hξ.1 witnessBlocks))) = 1
  rw [map_add]
  rw [← phaseV_eq_Vxi] at he
  exact he

theorem native_zero_set_lower_bound : ∃ c : ℝ, 0 < c ∧
    ∀ S : Set Cfg, S.Nonempty → (∀ y ∈ S, AnalyticDerivative.originalF y = 0) →
      ∀ t : ℝ, 0 < t → c*t ≤ Metric.infDist (literalCfg ξ+t•witnessDirection hξ) S := by
  obtain ⟨c,hc,h⟩ := homogeneous_zero_distance (separatingQuadratic hξ)
    (separatingQuadratic_continuous hξ) (separatingQuadratic_homogeneous hξ)
    (literalCfg ξ) (witnessDirection hξ) (by rw [separatingQuadratic_witness]; exact one_ne_zero)
  refine ⟨c,hc,?_⟩
  intro S hS hz
  apply h S hS
  intro y hy
  change stressCovector (ellH ξ hξ.1 0 0) (AnalyticDerivative.originalF (literalCfg ξ+(y-literalCfg ξ))) = 0
  rw [show literalCfg ξ + (y-literalCfg ξ) = y by abel, hz y hy,map_zero]

/-- A native tangent curve has second-order residual, using genuine C² Taylor
expansion of all original rows rather than a contracted residual surrogate. -/
theorem c2_tangent_residual_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : ContDiff ℝ 2 f) (h0 : f 0 = 0) (hd : deriv f 0 = 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ t : ℝ in 𝓝 0, ‖f t‖ ≤ B*t^2 := by
  let a : E := (1/2 : ℝ) • iteratedDeriv 2 f 0
  have he (t : ℝ) : taylorWithinEval f 2 Set.univ 0 t = t^2 • a := by
    simp [taylorWithinEval_succ,iteratedDerivWithin_univ,iteratedDeriv_one,h0,hd,a,smul_smul]
    <;> congr 1 <;> ring
  have hl := (taylor_isLittleO_univ hf (x₀ := 0)).bound (by norm_num : (0 : ℝ) < 1)
  simp only [he,sub_zero,one_mul,Real.norm_eq_abs,sq_abs] at hl
  refine ⟨1+‖a‖,by positivity,?_⟩
  filter_upwards [hl] with t ht
  rw [abs_of_nonneg (sq_nonneg t)] at ht
  have hh := norm_add_le (f t-t^2 • a) (t^2 • a)
  rw [sub_add_cancel,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg t)] at hh
  nlinarith

def witnessCurve (t : ℝ) : Cfg := literalCfg ξ + t • witnessDirection hξ

theorem witness_residual_bound : ∃ B : ℝ, 0 < B ∧
    ∀ᶠ t : ℝ in 𝓝 0, ‖AnalyticDerivative.originalF (witnessCurve hξ t)‖ ≤ B*t^2 := by
  apply c2_tangent_residual_bound
  · exact (AnalyticDerivative.originalF_contDiff 2).comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  · simpa only [witnessCurve,zero_smul,add_zero] using originalF_literalCfg ξ hξ.1
  · have hc : HasDerivAt (witnessCurve hξ) (witnessDirection hξ) 0 := by
      convert! ((hasDerivAt_id (0 : ℝ)).smul_const (witnessDirection hξ)).const_add (literalCfg ξ) using 1 <;> simp [witnessCurve]
    have hf := (AnalyticDerivative.originalF_differentiable (witnessCurve hξ 0)).hasFDerivAt.comp_hasDerivAt 0 hc
    have hz : fderiv ℝ AnalyticDerivative.originalF (witnessCurve hξ 0) (witnessDirection hξ) = 0 := by
      have h := familyDirection_mem_tangent hξ.1 witnessBlocks
      change fderiv ℝ AnalyticDerivative.originalF (literalCfg ξ) (witnessDirection hξ) = 0 at h
      simpa only [witnessCurve,zero_smul,add_zero] using h
    exact hf.deriv.trans hz

end Option2.NativeStress.PhaseSharpness
#print axioms Option2.NativeStress.PhaseSharpness.native_zero_set_lower_bound

#print axioms Option2.NativeStress.PhaseSharpness.witness_residual_bound

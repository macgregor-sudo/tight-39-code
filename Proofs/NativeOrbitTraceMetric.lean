module

public import NativeOrbitErrorTransfer

@[expose] public section

/-! Comparison of the unchanged native coordinate metric with the actual weighted trace form.
No replacement norm instance and no coordinate-action isometry is introduced. -/
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace CKM.NativeOrbitErrorTransfer
open NativeFirstOrder NativeGroupSlice NativeFourFamily NativePolynomial
open Option2.NativeStress.AnalyticDerivative
open Filter Topology
open scoped BigOperators

private theorem trace_weight_bounds (j : Fin 27) :
    (1 : ℝ) ≤ (IntegralStructureConstants.coordinateTraceWeight j : ℝ) ∧
      (IntegralStructureConstants.coordinateTraceWeight j : ℝ) ≤ 2 := by
  unfold IntegralStructureConstants.coordinateTraceWeight
  split_ifs <;> norm_num

theorem cfgPairing_nonneg (x : Cfg) : 0 ≤ cfgPairing x x := by
  by_cases hx : x = 0
  · subst x
    simp [cfgPairing, CoordinateMaps.coordinatePairing]
  · exact (cfgPairing_self_pos hx).le

private theorem coordinate_sq_le_cfgPairing (x : Cfg) (i : Fin 39) (j : Fin 27) :
    (x i j)^2 ≤ cfgPairing x x := by
  have hn (i : Fin 39) (j : Fin 27) :
      0 ≤ (IntegralStructureConstants.coordinateTraceWeight j : ℝ) * x i j * x i j := by
    rw [mul_assoc]
    exact mul_nonneg (le_trans zero_le_one (trace_weight_bounds j).1) (mul_self_nonneg _)
  have h1 : (x i j)^2 ≤ CoordinateMaps.coordinatePairing (x i) (x i) := by
    refine le_trans ?_ (Finset.single_le_sum (fun k _ => hn i k) (Finset.mem_univ j))
    simpa only [pow_two, mul_assoc] using
      (le_mul_of_one_le_left (mul_self_nonneg (x i j)) (trace_weight_bounds j).1)
  exact h1.trans (Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg (fun j _ => hn k j)) (Finset.mem_univ i))

theorem cfgPairing_le_coordinate_norm (x : Cfg) : cfgPairing x x ≤ 2106 * ‖x‖^2 := by
  have ht (i : Fin 39) (j : Fin 27) :
      (IntegralStructureConstants.coordinateTraceWeight j : ℝ) * x i j * x i j ≤ 2 * ‖x‖^2 := by
    have hc : |x i j| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (x i) j).trans (norm_le_pi_norm x i)
    have hs : x i j * x i j ≤ ‖x‖^2 := by
      simpa only [pow_two, abs_mul_abs_self] using mul_self_le_mul_self (abs_nonneg _) hc
    rw [mul_assoc]
    exact mul_le_mul (trace_weight_bounds j).2 hs (mul_self_nonneg _) (by norm_num)
  calc
    cfgPairing x x ≤ ∑ i : Fin 39, ∑ j : Fin 27, 2 * ‖x‖^2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ht i j))
    _ = 2106 * ‖x‖^2 := by simp; ring

def traceLength (x : Cfg) : ℝ := Real.sqrt (cfgPairing x x)
def traceDistance (x y : Cfg) : ℝ := traceLength (x-y)

theorem traceLength_comparison (x : Cfg) : ‖x‖ ≤ traceLength x ∧ traceLength x ≤ 46 * ‖x‖ := by
  have hs : 0 ≤ traceLength x := Real.sqrt_nonneg _
  have he : (traceLength x)^2 = cfgPairing x x := Real.sq_sqrt (cfgPairing_nonneg x)
  constructor
  · apply (pi_norm_le_iff_of_nonneg hs).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg hs).mpr
    intro j
    rw [Real.norm_eq_abs]
    have h := coordinate_sq_le_cfgPairing x i j
    nlinarith [sq_abs (x i j), abs_nonneg (x i j)]
  · have h := cfgPairing_le_coordinate_norm x
    nlinarith [norm_nonneg x, sq_nonneg ‖x‖]

theorem traceDistance_comparison (x y : Cfg) : dist x y ≤ traceDistance x y ∧
    traceDistance x y ≤ 46 * dist x y := by
  simpa only [traceDistance, dist_eq_norm] using traceLength_comparison (x-y)

theorem traceDistance_action {A : CEnd} (hA : A ∈ autC) (x y : Cfg) :
    traceDistance (actC A x) (actC A y) = traceDistance x y := by
  unfold traceDistance traceLength
  rw [← map_sub, cfgPairing_actC hA]

/-- Infimum of the explicitly specified weighted-trace distances, without changing instances. -/
def traceInfDist (x : Cfg) (S : Set Cfg) : ℝ := sInf ((traceDistance x) '' S)

theorem traceInfDist_nonneg (x : Cfg) (S : Set Cfg) (hS : S.Nonempty) : 0 ≤ traceInfDist x S := by
  apply le_csInf (hS.image _)
  rintro _ ⟨y, hy, rfl⟩
  exact Real.sqrt_nonneg _

theorem traceInfDist_comparison (x : Cfg) (S : Set Cfg) (hS : S.Nonempty) :
    Metric.infDist x S ≤ traceInfDist x S ∧ traceInfDist x S ≤ 46 * Metric.infDist x S := by
  have hb : BddBelow ((traceDistance x) '' S) := ⟨0, by
    rintro _ ⟨y, hy, rfl⟩
    exact Real.sqrt_nonneg _⟩
  constructor
  · apply le_csInf (hS.image _)
    rintro _ ⟨y, hy, rfl⟩
    exact (Metric.infDist_le_dist_of_mem hy).trans (traceDistance_comparison x y).1
  · have h : traceInfDist x S / 46 ≤ Metric.infDist x S := by
      apply (Metric.le_infDist hS).mpr
      intro y hy
      apply (div_le_iff₀ (by norm_num : (0:ℝ)<46)).mpr
      have hi : traceInfDist x S ≤ traceDistance x y := csInf_le hb (Set.mem_image_of_mem _ hy)
      nlinarith [(traceDistance_comparison x y).2]
    nlinarith [(div_le_iff₀ (by norm_num : (0:ℝ)<46)).mp h]

/-- The conditional orbit transfer also controls the specified weighted-trace distance.
The existing coordinate residual norm is unchanged; the explicit metric factor is 46². -/
theorem orbit_transfer_coordinate_and_trace (ξ : Fin 4 → ℂ) (hξ : IsGoodPhase ξ)
    (V : Fin 4 → Set SliceParam) (hV : ∀ i, V i ∈ 𝓝 0)
    (hzero : ∀ x ∈ sliceUnion ξ hξ.1 V, originalF x = 0)
    (r C : ℝ) (hr : 0 < r) (hC : 0 < C)
    (hnormal : ∀ n : normalC ξ, ‖n‖ < r →
      Metric.infDist (literalCfg ξ + (n : Cfg)) (sliceUnion ξ hξ.1 V)^2 ≤
        C * ‖originalF (literalCfg ξ + (n : Cfg))‖ ∧
      (originalF (literalCfg ξ + (n : Cfg)) = 0 ↔ literalCfg ξ + (n : Cfg) ∈ sliceUnion ξ hξ.1 V)) :
    ∃ U : Set Cfg, IsOpen U ∧ nativeOrbit ξ ⊆ U ∧ ∃ M : ℝ, 0 < M ∧
      ∀ y ∈ U, Metric.infDist y (saturation (sliceUnion ξ hξ.1 V))^2 ≤ M * ‖originalF y‖ ∧
        traceInfDist y (saturation (sliceUnion ξ hξ.1 V))^2 ≤ (2116 * M) * ‖originalF y‖ ∧
        (originalF y = 0 ↔ y ∈ saturation (sliceUnion ξ hξ.1 V)) := by
  obtain ⟨U, hU, hOrbit, M, hM, hb⟩ := orbit_transfer ξ hξ V hV hzero r C hr hC hnormal
  have hs : (saturation (sliceUnion ξ hξ.1 V)).Nonempty := by
    obtain ⟨x, hx⟩ := sliceUnion_nonempty ξ hξ.1 V hV
    refine ⟨x, (mem_saturation _ _).mpr ⟨1, one_mem_autOf prodC, x, hx, ?_⟩⟩
    rw [actC_one]
    rfl
  refine ⟨U, hU, hOrbit, M, hM, ?_⟩
  intro y hy
  obtain ⟨hd, hz⟩ := hb y hy
  refine ⟨hd, ?_, hz⟩
  have hc := (traceInfDist_comparison y _ hs).2
  have hsq := pow_le_pow_left₀ (traceInfDist_nonneg y _ hs) hc 2
  nlinarith

end CKM.NativeOrbitErrorTransfer

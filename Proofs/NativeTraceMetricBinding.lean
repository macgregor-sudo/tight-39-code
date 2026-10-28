module

public import NativeOrbitTraceMetric
public import ULStab
public import Mathlib.Analysis.InnerProductSpace.Defs

@[expose] public section

/-! Explicit trace metric on the unchanged native configuration type. The
topology agrees definitionally with the original coordinate topology. No global
metric/norm instance is replaced. NativeOrbitTraceMetric supplies the imported metric comparison. -/
noncomputable section
namespace CKM.NativeTraceMetricBinding
open NativeGroupSlice NativeUnlabelledSlice NativeOrbitErrorTransfer

private abbrev traceCore : InnerProductSpace.Core ℝ Cfg where
  inner := cfgPairing
  conj_inner_symm x y := by simpa using orbit_cfgPairing_comm y x
  re_inner_nonneg x := cfgPairing_nonneg x
  add_left := orbit_cfgPairing_add_left
  smul_left x y r := by simpa using orbit_cfgPairing_smul_left r x y
  definite x hx := by
    by_contra h
    exact (cfgPairing_self_pos h).ne' hx

private theorem core_dist (x y : Cfg) :
    @dist Cfg traceCore.toNormedAddCommGroup.toDist x y = traceDistance y x := by
  change Real.sqrt (cfgPairing (-x + y) (-x + y)) =
    Real.sqrt (cfgPairing (y-x) (y-x))
  rw [sub_eq_add_neg, add_comm (-x) y]

theorem traceDistance_triangle (x y z : Cfg) :
    traceDistance x z ≤ traceDistance x y + traceDistance y z := by
  have h := @dist_triangle Cfg traceCore.toNormedAddCommGroup.toPseudoMetricSpace z y x
  simpa only [core_dist, add_comm] using h

theorem traceDistance_comm (x y : Cfg) : traceDistance x y = traceDistance y x := by
  have h := @dist_comm Cfg traceCore.toNormedAddCommGroup.toPseudoMetricSpace y x
  simpa only [core_dist] using h

theorem traceDistance_self (x : Cfg) : traceDistance x x = 0 := by
  have h := @dist_self Cfg traceCore.toNormedAddCommGroup.toPseudoMetricSpace x
  simpa only [core_dist] using h

theorem traceDistance_topology (s : Set Cfg) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, traceDistance x y < ε → y ∈ s := by
  constructor
  · intro hs x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs x hx
    refine ⟨ε, hε, fun y hy => hball ?_⟩
    show dist y x < ε
    rw [dist_comm]
    exact lt_of_le_of_lt (traceDistance_comparison x y).1 hy
  · intro hs
    apply Metric.isOpen_iff.mpr
    intro x hx
    obtain ⟨ε, hε, hball⟩ := hs x hx
    refine ⟨ε / 46, by positivity, fun y hy => hball y ?_⟩
    have hy' : dist x y < ε / 46 := by simpa [Metric.mem_ball, dist_comm] using hy
    have hc := (traceDistance_comparison x y).2
    linarith

/-- Explicit compatible metric; deliberately not a global instance. -/
abbrev traceMetricSpace : MetricSpace Cfg :=
  MetricSpace.ofDistTopology traceDistance traceDistance_self traceDistance_comm
    traceDistance_triangle traceDistance_topology
    (fun x y h => dist_le_zero.mp (h ▸ (traceDistance_comparison x y).1))

theorem traceDistance_big_action (g : Big) (x y : Cfg) :
    traceDistance (g • x) (g • y) = traceDistance x y := by
  have hsub : g • x - g • y = g • (x - y) := (map_sub (bigLin g) x y).symm
  unfold traceDistance traceLength
  rw [hsub, cfgPairing_smul]

theorem isometry_big_action (g : Big) :
    @Isometry Cfg Cfg traceMetricSpace.toPseudoEMetricSpace traceMetricSpace.toPseudoEMetricSpace
      (fun x : Cfg => g • x) :=
  @Isometry.of_dist_eq Cfg Cfg traceMetricSpace.toPseudoMetricSpace
    traceMetricSpace.toPseudoMetricSpace _ (traceDistance_big_action g)

/-- Actual compensated group action, with the explicit trace metric. -/
theorem bigIsIsometricSMul :
    @IsIsometricSMul Big Cfg traceMetricSpace.toPseudoEMetricSpace _ :=
  @IsIsometricSMul.mk Big Cfg traceMetricSpace.toPseudoEMetricSpace _ isometry_big_action

#print axioms traceMetricSpace
#print axioms isometry_big_action
end CKM.NativeTraceMetricBinding

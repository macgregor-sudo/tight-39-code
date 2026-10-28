module

public import BookHTQuartic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

noncomputable section
namespace Option2.NativeStress.BookHT.SheetDistance
open scoped Topology

/-- The four axes in the unchanged Book outer Pi maximum norm. -/
def axisUnion : Set Blocks := {z | ∃ H : Fin 4, FourBlock.OnAxis H z}

theorem zero_mem_axisUnion : (0 : Blocks) ∈ axisUnion :=
  ⟨0, by intro J hJ; rfl⟩

theorem single_mem_axisUnion (H : Fin 4) (u : Triple) :
    Pi.single H u ∈ axisUnion := by
  refine ⟨H, ?_⟩
  intro J hJ
  simp [hJ]

theorem axisUnion_closed : IsClosed axisUnion := by
  have heq : axisUnion = ⋃ H : Fin 4, {z : Blocks | FourBlock.OnAxis H z} := by
    ext z; simp [axisUnion]
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro H
  have hclosed : IsClosed (⋂ J : Fin 4, ⋂ (_ : J ≠ H), {z : Blocks | z J = 0}) :=
    isClosed_iInter fun J => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply J) continuous_const
  have hs : {z : Blocks | FourBlock.OnAxis H z} =
      ⋂ J : Fin 4, ⋂ (_ : J ≠ H), {z : Blocks | z J = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter, FourBlock.OnAxis]
  rw [hs]
  exact hclosed

/-- An actual finite-axis coordinate projection is nearest and never enlarges
the Book norm; in particular it remains in every centered ball containing z. -/
theorem exists_nearest_axis (z : Blocks) :
    ∃ H : Fin 4, ‖(Pi.single H (z H) : Blocks)‖ ≤ ‖z‖ ∧
      ‖z - Pi.single H (z H)‖ = Metric.infDist z axisUnion := by
  obtain ⟨y, hy, hdist⟩ := axisUnion_closed.exists_infDist_eq_dist
    ⟨0, zero_mem_axisUnion⟩ z
  obtain ⟨H, hH⟩ := hy
  refine ⟨H, ?_, le_antisymm ?_ ?_⟩
  · rw [Pi.norm_single]
    exact norm_le_pi_norm z H
  · rw [hdist, dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg (z - y))).mpr
    intro J
    have hc : ‖(z - (Pi.single H (z H) : Blocks)) J‖ ≤ ‖(z - y) J‖ := by
      by_cases hj : J = H
      · subst J
        simp
      · simp [Pi.sub_apply, hj, hH J hj]
    exact hc.trans (norm_le_pi_norm (z - y) J)
  · simpa only [dist_eq_norm] using
      (Metric.infDist_le_dist_of_mem (x := z) (single_mem_axisUnion H (z H)))

end Option2.NativeStress.BookHT.SheetDistance

module

public import BookOrthogonalBlockModel
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Tactic.Positivity

@[expose] public section

noncomputable section

namespace Option2.NativeStress.BookOrthogonal.Distance

open scoped NNReal

/-- The unchanged finite Book axis union, without changing its Pi maximum norm. -/
def bookAxisUnion : Set BookHT.Blocks := {z | ∃ i, FourBlock.OnAxis i z}

/-- Explicit positive bounds; adding one avoids any nontriviality side condition. -/
def forwardConstant : ℝ≥0 := ‖(toBlocks : E →L[ℝ] BookHT.Blocks)‖₊ + 1
def inverseConstant : ℝ≥0 := ‖(toBlocks.symm : BookHT.Blocks →L[ℝ] E)‖₊ + 1

theorem forwardConstant_pos : 0 < (forwardConstant : ℝ) := by
  simp only [forwardConstant, NNReal.coe_add, NNReal.coe_one]
  positivity

theorem inverseConstant_pos : 0 < (inverseConstant : ℝ) := by
  simp only [inverseConstant, NNReal.coe_add, NNReal.coe_one]
  positivity

/-- Use the actual proved image identity, with no new axis/image assumption. -/
theorem actual_axis_image :
    toBlocks '' SupportedStress.blockUnion W = bookAxisUnion := image_blockUnion

theorem blockUnion_nonempty : (SupportedStress.blockUnion W).Nonempty := by
  refine ⟨0, ?_⟩
  change (0 : E) ∈ ⋃ i, (W i : Set E)
  exact Set.mem_iUnion.mpr ⟨0, (W 0).zero_mem⟩

theorem bookAxisUnion_nonempty : bookAxisUnion.Nonempty := by
  rw [← actual_axis_image]
  exact blockUnion_nonempty.image toBlocks

private theorem infDist_image_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) (K : ℝ≥0) (hf : LipschitzWith K f) (hK : 0 < (K : ℝ))
    (S : Set X) (hS : S.Nonempty) (x : X) :
    Metric.infDist (f x) (f '' S) ≤ (K : ℝ) * Metric.infDist x S := by
  have hdiv : Metric.infDist (f x) (f '' S) / (K : ℝ) ≤ Metric.infDist x S := by
    apply (Metric.le_infDist hS).mpr
    intro y hy
    apply (div_le_iff₀ hK).mpr
    calc
      Metric.infDist (f x) (f '' S) ≤ dist (f x) (f y) :=
        Metric.infDist_le_dist_of_mem ⟨y, hy, rfl⟩
      _ ≤ (K : ℝ) * dist x y := hf.dist_le_mul x y
      _ = dist x y * (K : ℝ) := mul_comm _ _
  simpa only [mul_comm] using (div_le_iff₀ hK).mp hdiv

theorem forward_infDist (x : E) :
    Metric.infDist (toBlocks x) bookAxisUnion ≤
      (forwardConstant : ℝ) * Metric.infDist x (SupportedStress.blockUnion W) := by
  have hLip : LipschitzWith forwardConstant toBlocks :=
    toBlocks.lipschitzWith.weaken (by simp [forwardConstant])
  have h := infDist_image_le toBlocks forwardConstant hLip forwardConstant_pos
    (SupportedStress.blockUnion W) blockUnion_nonempty x
  rw [actual_axis_image] at h
  exact h

theorem actual_inverse_axis_image :
    toBlocks.symm '' bookAxisUnion = SupportedStress.blockUnion W := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← actual_axis_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hy
  · intro hx
    refine ⟨toBlocks x, ?_, toBlocks.symm_apply_apply x⟩
    rw [← actual_axis_image]
    exact ⟨x, hx, rfl⟩

theorem inverse_infDist (x : E) :
    Metric.infDist x (SupportedStress.blockUnion W) ≤
      (inverseConstant : ℝ) * Metric.infDist (toBlocks x) bookAxisUnion := by
  have hLip : LipschitzWith inverseConstant toBlocks.symm :=
    toBlocks.symm.lipschitzWith.weaken (by simp [inverseConstant])
  have h := infDist_image_le toBlocks.symm inverseConstant hLip inverseConstant_pos
    bookAxisUnion bookAxisUnion_nonempty (toBlocks x)
  rw [actual_inverse_axis_image, ContinuousLinearEquiv.symm_apply_apply] at h
  exact h

/-- Global two-sided comparison of the two actual axis distances. No isometry
between the outer Euclidean norm and the Book Pi maximum norm is asserted. -/
theorem two_sided_infDist (x : E) :
    Metric.infDist x (SupportedStress.blockUnion W) / (inverseConstant : ℝ) ≤
        Metric.infDist (toBlocks x) bookAxisUnion ∧
      Metric.infDist (toBlocks x) bookAxisUnion ≤
        (forwardConstant : ℝ) * Metric.infDist x (SupportedStress.blockUnion W) := by
  refine ⟨(div_le_iff₀ inverseConstant_pos).mpr ?_, forward_infDist x⟩
  simpa only [mul_comm] using inverse_infDist x

theorem two_sided_infDist_blocks (z : BookHT.Blocks) :
    Metric.infDist (toBlocks.symm z) (SupportedStress.blockUnion W) / (inverseConstant : ℝ) ≤
        Metric.infDist z bookAxisUnion ∧
      Metric.infDist z bookAxisUnion ≤ (forwardConstant : ℝ) *
        Metric.infDist (toBlocks.symm z) (SupportedStress.blockUnion W) := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using two_sided_infDist (toBlocks.symm z)

end Option2.NativeStress.BookOrthogonal.Distance

module

public import FiniteOverlapGapV2
public import NativeFrameOverlapCancellation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum

@[expose] public section
set_option backward.proofsInPublic true

/-!
# Optional overlap-loss sandwich for thirteen actual native frames

The carrier and Frame predicate are the existing literal Glennie declarations.
Unordered frame pairs use their unique increasing order. Within each frame,
unordered pairs of its three labels likewise use increasing order. The disjoint
sum of within-frame and cross-frame indices defines the full pair energy below.
No native norm/distance comparison, global optimality or distinctness is assumed.
The imported native source owners retain their existing provenance and notices.
-/

open scoped BigOperators

namespace SupportedStress.NativeFrames

abbrev ThirteenFramePair := {ab : Fin 13 × Fin 13 // ab.1 < ab.2}
abbrev FrameTriplePair := {ij : Fin 3 × Fin 3 // ij.1 < ij.2}
abbrev ThirteenFrameEntry := Fin 13 × Fin 3
abbrev ThirteenWithinPair := Fin 13 × FrameTriplePair
abbrev ThirteenCrossPair := ThirteenFramePair × (Fin 3 × Fin 3)
abbrev ThirteenPointPair := ThirteenWithinPair ⊕ ThirteenCrossPair

theorem thirteen_frame_pair_card : Fintype.card ThirteenFramePair = 78 := by decide
theorem frame_triple_pair_card : Fintype.card FrameTriplePair = 3 := by decide

/-- There are 39 labelled entries; this does not assert distinctness of their values. -/
theorem thirteen_frame_entry_card : Fintype.card ThirteenFrameEntry = 39 := by
  norm_num [ThirteenFrameEntry, Fintype.card_prod]

theorem thirteen_within_pair_card : Fintype.card ThirteenWithinPair = 39 := by
  simp [ThirteenWithinPair, Fintype.card_prod, frame_triple_pair_card]

theorem thirteen_cross_pair_card : Fintype.card ThirteenCrossPair = 702 := by
  simp [ThirteenCrossPair, Fintype.card_prod, thirteen_frame_pair_card]

theorem thirteen_point_pair_card : Fintype.card ThirteenPointPair = 741 := by
  change Fintype.card (ThirteenWithinPair ⊕ ThirteenCrossPair) = 741
  rw [Fintype.card_sum, thirteen_within_pair_card, thirteen_cross_pair_card]

noncomputable def thirteenWithinOverlap
    (p : Fin 13 → Fin 3 → Glennie.Albert) (k : ThirteenWithinPair) : ℝ :=
  Glennie.trace (Glennie.jordan (p k.1 k.2.val.1) (p k.1 k.2.val.2))

noncomputable def thirteenCrossOverlap
    (p : Fin 13 → Fin 3 → Glennie.Albert) (k : ThirteenCrossPair) : ℝ :=
  Glennie.trace (Glennie.jordan (p k.1.val.1 k.2.1) (p k.1.val.2 k.2.2))

noncomputable def thirteenPairOverlap
    (p : Fin 13 → Fin 3 → Glennie.Albert) : ThirteenPointPair → ℝ :=
  Sum.elim (thirteenWithinOverlap p) (thirteenCrossOverlap p)

noncomputable def thirteenFrameEnergy
    (φ : ℝ → ℝ) (p : Fin 13 → Fin 3 → Glennie.Albert) : ℝ :=
  ∑ k : ThirteenPointPair, φ (thirteenPairOverlap p k)

noncomputable def thirteenCrossResidualSquared
    (p : Fin 13 → Fin 3 → Glennie.Albert) : ℝ :=
  ∑ k : ThirteenCrossPair, (thirteenCrossOverlap p k - (1 / 3 : ℝ)) ^ 2

theorem thirteen_within_overlap_zero
    (p : Fin 13 → Fin 3 → Glennie.Albert)
    (hp : ∀ a : Fin 13, Glennie.Frame (p a)) (k : ThirteenWithinPair) :
    thirteenWithinOverlap p k = 0 := by
  unfold thirteenWithinOverlap
  rw [(hp k.1).orthogonal k.2.val.1 k.2.val.2 (ne_of_lt k.2.property)]
  simp [Glennie.trace]

theorem thirteen_cross_deviation_sum_zero
    (p : Fin 13 → Fin 3 → Glennie.Albert)
    (hp : ∀ a : Fin 13, Glennie.Frame (p a)) :
    ∑ k : ThirteenCrossPair, (thirteenCrossOverlap p k - (1 / 3 : ℝ)) = 0 := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro ab _
  exact frame_pair_deviation_sum_zero (p ab.val.1) (p ab.val.2)
    (hp ab.val.1) (hp ab.val.2)

/-- The 39 within-frame pairs contribute their literal constant value `φ 0`. -/
theorem thirteen_frame_energy_decomposition
    (φ : ℝ → ℝ) (p : Fin 13 → Fin 3 → Glennie.Albert)
    (hp : ∀ a : Fin 13, Glennie.Frame (p a)) :
    thirteenFrameEnergy φ p = (39 : ℝ) * φ 0 +
      ∑ k : ThirteenCrossPair, φ (thirteenCrossOverlap p k) := by
  unfold thirteenFrameEnergy
  rw [Fintype.sum_sum_type]
  change (∑ k : ThirteenWithinPair, φ (thirteenWithinOverlap p k)) +
      (∑ k : ThirteenCrossPair, φ (thirteenCrossOverlap p k)) = _
  have hwithin : (∑ k : ThirteenWithinPair, φ (thirteenWithinOverlap p k)) =
      (39 : ℝ) * φ 0 := by
    simp only [thirteen_within_overlap_zero p hp, Finset.sum_const,
      Finset.card_univ, thirteen_within_pair_card]
    norm_num
  rw [hwithin]

/-- Actual thirteen-frame pair loss is comparable to the literal cross-overlap
squared residual. Regularity is required near `1/3`, not at the constant within-
frame value `0`. No native residual-to-distance estimate is used or concluded. -/
theorem thirteen_frame_overlap_loss_sandwich
    (p : Fin 13 → Fin 3 → Glennie.Albert)
    (hp : ∀ a : Fin 13, Glennie.Frame (p a))
    (φ : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hconvex : Convex ℝ U)
    (hφ : ContDiffOn ℝ 2 φ U) (hbase : (1 / 3 : ℝ) ∈ U)
    (m M : ℝ) (hm : 0 < m)
    (hcurv : ∀ x ∈ U, m ≤ deriv (deriv φ) x ∧ deriv (deriv φ) x ≤ M)
    (hnear : ∀ k : ThirteenCrossPair, thirteenCrossOverlap p k ∈ U) :
    (m / 2) * thirteenCrossResidualSquared p ≤
        thirteenFrameEnergy φ p - ((39 : ℝ) * φ 0 + 702 * φ (1 / 3)) ∧
      thirteenFrameEnergy φ p - ((39 : ℝ) * φ 0 + 702 * φ (1 / 3)) ≤
        (M / 2) * thirteenCrossResidualSquared p := by
  have hnormalize : ∀ k : ThirteenCrossPair,
      (1 / 3 : ℝ) + (thirteenCrossOverlap p k - 1 / 3) =
        thirteenCrossOverlap p k := by
    intro k
    ring
  have hshift : ∀ k : ThirteenCrossPair,
      (1 / 3 : ℝ) + (thirteenCrossOverlap p k - 1 / 3) ∈ U := by
    intro k
    rw [hnormalize]
    exact hnear k
  have hgap := SupportedStress.finite_overlap_gap_of_curvature φ U hU hconvex hφ
    (1 / 3) m M hbase hm hcurv (fun k => thirteenCrossOverlap p k - 1 / 3)
    hshift (thirteen_cross_deviation_sum_zero p hp)
  have hsum : (∑ k : ThirteenCrossPair,
      (φ ((1 / 3 : ℝ) + (thirteenCrossOverlap p k - 1 / 3)) - φ (1 / 3))) =
      (∑ k, φ (thirteenCrossOverlap p k)) - 702 * φ (1 / 3) := by
    simp only [hnormalize, Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.card_univ, thirteen_cross_pair_card]
    norm_num
  rw [hsum] at hgap
  rw [thirteen_frame_energy_decomposition φ p hp]
  unfold thirteenCrossResidualSquared
  constructor <;> linarith [hgap.1, hgap.2]

end SupportedStress.NativeFrames

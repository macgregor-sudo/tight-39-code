module

public import EFDefs

@[expose] public section

/-!
# Exact native row, column and block sums

From the native `Glennie.Frame` fields (`trace_one`, `idempotent`, `orthogonal`, `sum_unit`) and
the native Jordan/trace laws (`jordan_add_right`, `jordan_unit_right`, `jordan_comm`, `trace_add`),
for any thirteen frames `p h`:
* every row `∑ j, B p h k i j` and every column `∑ i, B p h k i j` equals `1` (all `h k`, including
  `h = k`), each nine-entry block sums to `3`, the 702 cross overlaps sum to `234 = 78 · 3`;
* hence `D p = ∑ (cross)^2 - 78`, and the cross overlaps all equal `1/3` as soon as they are all
  `≤ 1/3` (each block of nine sums to `3`).
No Gram table, row-sum, positivity, tightness or distinctness premise is used.
-/

noncomputable section

namespace CKM.NativeExactFrameEnergy

open Glennie SupportedStress.NativeFrames

/-- Native purity `IsPure` is derived from the `idempotent` and `trace_one` Frame fields. -/
theorem isPure_of_frame {q : Fin 3 → Albert} (hq : Frame q) (a : Fin 3) :
    CKM.NativeTightCode.IsPure (q a) := by
  exact ⟨hq.idempotent a, hq.trace_one a⟩

theorem frame_row_sum (p : Fin 13 → Fin 3 → Albert) (hp : ∀ h, Frame (p h))
    (h k : Fin 13) (i : Fin 3) : ∑ j, B p h k i j = 1 := by
  have hrow := congrArg (fun x : Albert => trace (jordan (p h i) x)) (hp k).sum_unit
  simp only [Glennie.jordan_add_right, Glennie.trace_add, Glennie.jordan_unit_right,
    (hp h).trace_one] at hrow
  simp only [B, Fin.sum_univ_three]
  exact hrow

theorem frame_col_sum (p : Fin 13 → Fin 3 → Albert) (hp : ∀ h, Frame (p h))
    (h k : Fin 13) (j : Fin 3) : ∑ i, B p h k i j = 1 := by
  have hcol := congrArg (fun x : Albert => trace (jordan (p k j) x)) (hp h).sum_unit
  simp only [Glennie.jordan_add_right, Glennie.trace_add, Glennie.jordan_unit_right,
    (hp k).trace_one] at hcol
  simp only [B, Fin.sum_univ_three]
  rw [Glennie.jordan_comm (p h 0), Glennie.jordan_comm (p h 1), Glennie.jordan_comm (p h 2)]
  exact hcol

theorem frame_block_sum (p : Fin 13 → Fin 3 → Albert) (hp : ∀ h, Frame (p h))
    (h k : Fin 13) : ∑ i, ∑ j, B p h k i j = 3 := by
  simp only [frame_row_sum p hp h k, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

theorem thirteenCrossOverlap_eq_B (p : Fin 13 → Fin 3 → Albert) (k : ThirteenCrossPair) :
    thirteenCrossOverlap p k = B p k.1.val.1 k.1.val.2 k.2.1 k.2.2 := rfl

theorem cross_overlap_sum (p : Fin 13 → Fin 3 → Albert) (hp : ∀ h, Frame (p h)) :
    ∑ k : ThirteenCrossPair, thirteenCrossOverlap p k = 234 := by
  have h0 := thirteen_cross_deviation_sum_zero p hp
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, thirteen_cross_pair_card]
    at h0
  norm_num at h0
  linarith

theorem D_eq_sq_sum_sub (p : Fin 13 → Fin 3 → Albert) (hp : ∀ h, Frame (p h)) :
    D p = (∑ k : ThirteenCrossPair, (thirteenCrossOverlap p k) ^ 2) - 78 := by
  have hexp : ∀ k : ThirteenCrossPair, (thirteenCrossOverlap p k - 1 / 3) ^ 2 =
      (thirteenCrossOverlap p k) ^ 2 - (2 / 3) * thirteenCrossOverlap p k + 1 / 9 := by
    intro k; ring
  show (∑ k : ThirteenCrossPair, (thirteenCrossOverlap p k - 1 / 3) ^ 2) = _
  simp only [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, cross_overlap_sum p hp,
    Finset.sum_const, Finset.card_univ, thirteen_cross_pair_card]
  norm_num
  ring

theorem D_nonneg (p : Fin 13 → Fin 3 → Albert) : 0 ≤ D p := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem D_eq_zero_iff (p : Fin 13 → Fin 3 → Albert) :
    D p = 0 ↔ ∀ k : ThirteenCrossPair, thirteenCrossOverlap p k = 1 / 3 := by
  show (∑ k : ThirteenCrossPair, (thirteenCrossOverlap p k - 1 / 3) ^ 2) = 0 ↔ _
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  simp [sub_eq_zero]

/-- Cross overlaps that are all `≤ 1/3` are all `= 1/3` (each nine-entry block sums to `3`). -/
theorem cross_eq_third_of_le (p : Fin 13 → Fin 3 → Albert) (hp : ∀ h, Frame (p h))
    (hle : ∀ k : ThirteenCrossPair, thirteenCrossOverlap p k ≤ 1 / 3) :
    ∀ k : ThirteenCrossPair, thirteenCrossOverlap p k = 1 / 3 := by
  have h0 := thirteen_cross_deviation_sum_zero p hp
  rw [Finset.sum_eq_zero_iff_of_nonpos (fun k _ => sub_nonpos.mpr (hle k))] at h0
  intro k
  have hk : thirteenCrossOverlap p k - 1 / 3 = 0 := h0 k (by simp)
  linarith

end CKM.NativeExactFrameEnergy

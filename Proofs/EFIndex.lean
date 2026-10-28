module

public import EFDefs

@[expose] public section

/-!
# The indexed energy is the thirteen-frame energy

`pairMap e` is a bijection from the 741 unordered index pairs `i < j` of `Fin 39` onto the existing
disjoint index `ThirteenPointPair = ThirteenWithinPair ⊕ ThirteenCrossPair` (39 + 702), and it
carries the native overlap `inner (P i) (P j)` to the existing `thirteenPairOverlap` of the frame
array `framesOf e P`. When `pairMap` reverses the point order (the within case with `b < a`, or the
cross case with `k < h`), native symmetry `Glennie.jordan_comm` / `Glennie.inner_comm` is used.
These are index counts: no injectivity of `P` is assumed, values of `P` may repeat.
-/

noncomputable section

namespace CKM.NativeExactFrameEnergy

open Glennie SupportedStress.NativeFrames

theorem pair39_card : Fintype.card Pair39 = 741 := by
  rw [Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_fin]
  rfl

/-- `pairMap` carries the native overlap to the existing frame-pair overlap. -/
theorem pairMap_overlap (e : Fin 39 ≃ Fin 13 × Fin 3) (P : Fin 39 → Albert) (ij : Pair39) :
    thirteenPairOverlap (framesOf e P) (pairMap e ij) = inner (P ij.val.1) (P ij.val.2) := by
  obtain ⟨⟨i, j⟩, hij⟩ := ij
  have hi : e.symm ((e i).1, (e i).2) = i := by simp
  have hj : e.symm ((e j).1, (e j).2) = j := by simp
  unfold pairMap
  dsimp only
  split_ifs with hxy hab hhk
  · have hj' : e.symm ((e i).1, (e j).2) = j := by rw [hxy]; simp
    simp only [thirteenPairOverlap, Sum.elim_inl, thirteenWithinOverlap, framesOf, hi, hj',
      Glennie.inner]
  · have hj' : e.symm ((e i).1, (e j).2) = j := by rw [hxy]; simp
    simp only [thirteenPairOverlap, Sum.elim_inl, thirteenWithinOverlap, framesOf, hi, hj',
      Glennie.inner]
    rw [Glennie.jordan_comm]
  · simp only [thirteenPairOverlap, Sum.elim_inr, thirteenCrossOverlap, framesOf, hi, hj,
      Glennie.inner]
  · simp only [thirteenPairOverlap, Sum.elim_inr, thirteenCrossOverlap, framesOf, hi, hj,
      Glennie.inner]
    rw [Glennie.jordan_comm]

/-- The two labels of a point pair, in the stored order. -/
private def pairLabels : ThirteenPointPair → (Fin 13 × Fin 3) × (Fin 13 × Fin 3)
  | Sum.inl (h, ab) => ((h, ab.val.1), (h, ab.val.2))
  | Sum.inr (hk, ab) => ((hk.val.1, ab.1), (hk.val.2, ab.2))

private theorem pairLabels_pairMap (e : Fin 39 ≃ Fin 13 × Fin 3) (ij : Pair39) :
    pairLabels (pairMap e ij) = (e ij.val.1, e ij.val.2) ∨
      pairLabels (pairMap e ij) = (e ij.val.2, e ij.val.1) := by
  obtain ⟨⟨i, j⟩, hij⟩ := ij
  unfold pairMap
  dsimp only
  split_ifs with hxy hab hhk
  · left; simp [pairLabels, Prod.ext_iff, hxy]
  · right; simp [pairLabels, Prod.ext_iff, hxy]
  · left; simp [pairLabels]
  · right; simp [pairLabels]

theorem pairMap_injective (e : Fin 39 ≃ Fin 13 × Fin 3) : Function.Injective (pairMap e) := by
  rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨i', j'⟩, hij'⟩ h
  have h1 := pairLabels_pairMap e ⟨(i, j), hij⟩
  have h2 := pairLabels_pairMap e ⟨(i', j'), hij'⟩
  rw [h] at h1
  dsimp only at h1 h2 hij hij'
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1] at h2 <;>
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h2 <;>
    obtain ⟨rfl, rfl⟩ := h2 <;>
    first | rfl | exact absurd (hij.trans hij') (lt_irrefl _)

theorem pairMap_bijective (e : Fin 39 ≃ Fin 13 × Fin 3) : Function.Bijective (pairMap e) := by
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨pairMap_injective e, by rw [pair39_card, thirteen_point_pair_card]⟩

/-- The bijection of unordered index pairs. -/
def pairEquiv (e : Fin 39 ≃ Fin 13 × Fin 3) : Pair39 ≃ ThirteenPointPair :=
  Equiv.ofBijective _ (pairMap_bijective e)

/-- Of the 741 index pairs, exactly 39 lie within a frame of the labelling `e`. -/
private theorem within_iff_isLeft (e : Fin 39 ≃ Fin 13 × Fin 3) (ij : Pair39) :
    (e ij.val.1).1 = (e ij.val.2).1 ↔ (pairEquiv e ij).isLeft = true := by
  change _ ↔ (pairMap e ij).isLeft = true
  obtain ⟨⟨i, j⟩, hij⟩ := ij
  unfold pairMap
  dsimp only
  split_ifs <;> simp [*]

theorem card_within_index_pairs (e : Fin 39 ≃ Fin 13 × Fin 3) :
    (Finset.univ.filter fun ij : Pair39 => (e ij.val.1).1 = (e ij.val.2).1).card = 39 := by
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr
    ((Equiv.subtypeEquiv (pairEquiv e) (within_iff_isLeft e)).trans Equiv.sumIsLeft)).trans
    thirteen_within_pair_card

/-- Of the 741 index pairs, exactly 702 join two different frames of the labelling `e`. -/
theorem card_cross_index_pairs (e : Fin 39 ≃ Fin 13 × Fin 3) :
    (Finset.univ.filter fun ij : Pair39 => (e ij.val.1).1 ≠ (e ij.val.2).1).card = 702 := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun ij : Pair39 => (e ij.val.1).1 = (e ij.val.2).1)
  rw [card_within_index_pairs, Finset.card_univ, pair39_card] at h
  simp only [ne_eq]
  omega

/-- **Finite-index identity.** The indexed energy equals the existing thirteen-frame energy of the
frame array, for every `φ`, every labelling `e` and every `P` (no frame or injectivity premise). -/
theorem E39_eq_thirteenFrameEnergy (φ : ℝ → ℝ) (e : Fin 39 ≃ Fin 13 × Fin 3)
    (P : Fin 39 → Albert) : E39 φ P = thirteenFrameEnergy φ (framesOf e P) := by
  unfold E39 thirteenFrameEnergy
  exact Fintype.sum_bijective (pairMap e) (pairMap_bijective e) _ _
    (fun ij => by rw [pairMap_overlap])

end CKM.NativeExactFrameEnergy

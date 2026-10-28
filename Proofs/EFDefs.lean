module

public import NativeThirteenFrameOverlapLoss
public import TCDefs

@[expose] public section
set_option backward.proofsInPublic true

/-!
# Native exact-frame indexed energy: shared definitions

Definitions only, on the unchanged compact `Glennie.Albert`, `Glennie.jordan`, `Glennie.trace`
(unnormalized, `trace 1 = 3`), `Glennie.inner x y = trace (jordan x y)` and `Glennie.Frame`.

A labelled configuration is `P : Fin 39 → Albert`; an explicit label equivalence
`e : Fin 39 ≃ Fin 13 × Fin 3` gives the frame array `framesOf e P h a = P (e.symm (h, a))`.
The indexed energy `E39` sums over the 741 unordered **index** pairs `i < j`; it is not a sum over a
set of distinct values, and no injectivity of `P` is assumed anywhere in its definition.

The thirteen-frame energy, the cross overlaps and the squared cross residual are the existing
source-admitted declarations of `NativeThirteenFrameOverlapLoss` (namespace
`SupportedStress.NativeFrames`), reused unchanged.
-/

noncomputable section

namespace CKM.NativeExactFrameEnergy

open Glennie SupportedStress.NativeFrames

/-- Unordered index pairs of `Fin 39`, represented by their increasing order. -/
abbrev Pair39 := {ij : Fin 39 × Fin 39 // ij.1 < ij.2}

/-- The indexed pair energy of a labelled 39-point configuration. -/
def E39 (φ : ℝ → ℝ) (P : Fin 39 → Albert) : ℝ :=
  ∑ ij : Pair39, φ (inner (P ij.val.1) (P ij.val.2))

/-- The frame array read through the label equivalence: `framesOf e P h a = P (e.symm (h, a))`. -/
def framesOf (e : Fin 39 ≃ Fin 13 × Fin 3) (P : Fin 39 → Albert) : Fin 13 → Fin 3 → Albert :=
  fun h a => P (e.symm (h, a))

/-- The native frame-block overlaps `B h k i j = trace (jordan (p h i) (p k j))`. -/
def B (p : Fin 13 → Fin 3 → Albert) (h k : Fin 13) (i j : Fin 3) : ℝ :=
  trace (jordan (p h i) (p k j))

/-- The squared cross residual, the existing `thirteenCrossResidualSquared`. -/
abbrev D (p : Fin 13 → Fin 3 → Albert) : ℝ := thirteenCrossResidualSquared p

/-- The baseline energy `39 φ(0) + 702 φ(1/3)`. -/
def E0 (φ : ℝ → ℝ) : ℝ := 39 * φ 0 + 702 * φ (1 / 3)

/-- The explicit pair map. A pair `i < j` with labels `e i = (h, a)`, `e j = (k, b)` goes to the
within-frame pair of frame `h` (labels in increasing order) when `h = k`, and otherwise to the
cross pair of the frames in increasing order, with the labels carried along (swapped with the frames
when `k < h`). The within case uses `a ≠ b`, which follows from injectivity of `e` and `i ≠ j`. -/
def pairMap (e : Fin 39 ≃ Fin 13 × Fin 3) (ij : Pair39) : ThirteenPointPair :=
  if hxy : (e ij.val.1).1 = (e ij.val.2).1 then
    if hab : (e ij.val.1).2 < (e ij.val.2).2 then
      Sum.inl ((e ij.val.1).1, ⟨((e ij.val.1).2, (e ij.val.2).2), hab⟩)
    else
      Sum.inl ((e ij.val.1).1, ⟨((e ij.val.2).2, (e ij.val.1).2), by
        refine lt_of_le_of_ne (not_lt.mp hab) ?_
        intro h
        exact (ne_of_lt ij.property) (e.injective (Prod.ext hxy h.symm))⟩)
  else if hhk : (e ij.val.1).1 < (e ij.val.2).1 then
    Sum.inr (⟨((e ij.val.1).1, (e ij.val.2).1), hhk⟩, ((e ij.val.1).2, (e ij.val.2).2))
  else
    Sum.inr (⟨((e ij.val.2).1, (e ij.val.1).1), lt_of_le_of_ne (not_lt.mp hhk) (Ne.symm hxy)⟩,
      ((e ij.val.2).2, (e ij.val.1).2))

end CKM.NativeExactFrameEnergy

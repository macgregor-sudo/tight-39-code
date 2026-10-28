module

public import NativeLeftPartialPreservation

@[expose] public section

/-!
# Every original row is preserved at the canonical complex anchors

The input is any real solution of the literal F equations with the twelve
canonical included anchor values at their exact first-four-frame labels.
Original scalar pair rows give all twelve unbiased readouts of every later
point. The accepted quartet tomography theorem forces its visible matrix I/3.
Thus every point is either a fixed visible anchor or on the classified native
slice, where special-unitary multiplication proves idempotency preservation.
Native trace-pair isometry, linearity and the fixed unit preserve every other
original row. Neither transformed equations nor point-position coverage are
premises. The actual fixed rational CKM point is a separate importing consumer.

The short coordinate bridges below re-establish the already accepted native
normalization from imported numerator/coordinate identities, avoiding heavy
differential and frame-proof imports. No upstream implementation is copied.
Native provenance, Apache-2.0 notices and mathlib pins remain in the unchanged
imports. This is first-party theorem composition with no novelty, ideal,
dimension, full-group, other-anchor or exhaustion claim.
Thanks to the native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace NativePolynomial.PartialAction

open scoped BigOperators
open CoordinateMaps IntegralStructureConstants ConfigurationResiduals
open ConfigurationResidualIndices CompactAlbert
open UnitaryErrorBases.ComplexQuartet

/-- The original real coordinate product is the actual native Jordan product. -/
theorem product_half_native (x y : NativeVector ℝ) :
    coordinateProduct (1 / 2 : ℝ) x y =
      upperCoordinates (Glennie.jordan (fromUpperCoordinates x) (fromUpperCoordinates y)) := by
  funext k
  rw [coordinateProduct_apply, upperCoordinates_jordan]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [numerator_cast_eq_two_nativeStructureConstant]
  ring

theorem upper_unit_native :
    upperCoordinates (1 : Glennie.Albert) = (coordinateUnit : NativeVector ℝ) := by
  funext k
  fin_cases k <;> rfl

theorem trace_upper_native (x : Glennie.Albert) :
    coordinateTrace (upperCoordinates x) = Glennie.trace x := by
  simp [coordinateTrace_apply, upperCoordinates, Glennie.trace]

theorem trace_decode_native (x : NativeVector ℝ) :
    Glennie.trace (fromUpperCoordinates x) = coordinateTrace x := by
  simp [coordinateTrace_apply, fromUpperCoordinates, Glennie.trace]

/-- The weighted original coordinate pairing, with no Euclidean replacement. -/
theorem pairing_decode_native (x y : NativeVector ℝ) :
    coordinatePairing x y =
      Glennie.trace (Glennie.jordan (fromUpperCoordinates x) (fromUpperCoordinates y)) := by
  rw [← coordinateTrace_product (1 / 2 : ℝ) (by norm_num) x y,
    product_half_native, trace_upper_native]

/-- Conjugate the actual native real-linear partial action into upper coordinates. -/
def coordinatePartialLeft (V : TitsComplexMatrix) :
    NativeVector ℝ →ₗ[ℝ] NativeVector ℝ :=
  upperCoordinateEquiv.toLinearMap.comp
    ((nativePartialLeft V).comp upperCoordinateEquiv.symm.toLinearMap)

theorem coordinatePartialLeft_apply (V : TitsComplexMatrix) (x : NativeVector ℝ) :
    coordinatePartialLeft V x = upperCoordinates (nativePartialLeft V (fromUpperCoordinates x)) := rfl

theorem decode_coordinatePartialLeft (V : TitsComplexMatrix) (x : NativeVector ℝ) :
    fromUpperCoordinates (coordinatePartialLeft V x) =
      nativePartialLeft V (fromUpperCoordinates x) := by
  rw [coordinatePartialLeft_apply, fromUpperCoordinates_upperCoordinates]

theorem coordinatePartialLeft_unit (V : TitsComplexMatrix) :
    coordinatePartialLeft V coordinateUnit = coordinateUnit := by
  calc
    _ = coordinatePartialLeft V (upperCoordinates (1 : Glennie.Albert)) :=
      congrArg (coordinatePartialLeft V) upper_unit_native.symm
    _ = upperCoordinates (nativePartialLeft V 1) := by
      rw [coordinatePartialLeft_apply, fromUpperCoordinates_upperCoordinates]
    _ = coordinateUnit := by rw [nativePartialLeft_unit, upper_unit_native]

theorem coordinatePartialLeft_trace (V : TitsComplexMatrix) (x : NativeVector ℝ) :
    coordinateTrace (coordinatePartialLeft V x) = coordinateTrace x := by
  rw [coordinatePartialLeft_apply, trace_upper_native, nativePartialLeft_trace,
    trace_decode_native]

theorem coordinatePartialLeft_pairing (V : TitsComplexMatrix)
    (hV : V * V.conjTranspose = (1 : TitsComplexMatrix)) (hd : V.det = 1)
    (x y : NativeVector ℝ) :
    coordinatePairing (coordinatePartialLeft V x) (coordinatePartialLeft V y) =
      coordinatePairing x y := by
  simp only [pairing_decode_native, decode_coordinatePartialLeft,
    nativePartialLeft_trace_pairing V hV hd]

/-- The exact phase-frame labels 1,2,3; no relabelling of F is performed. -/
def canonicalPhaseFrame (s : Fin 3) : Fin 13 := ⟨1 + s.val, by omega⟩

/-- Twelve equalities of input points at their actual first-four-frame labels. -/
structure CanonicalAnchors (C : Configuration ℝ) : Prop where
  coordinate : ∀ a : Fin 3,
    fromUpperCoordinates (C (framePointIndex 0 a)) = includedCoordinatePoint a
  phase : ∀ s a : Fin 3,
    fromUpperCoordinates (C (framePointIndex (canonicalPhaseFrame s) a)) =
      includedPhasePoint (s.val : PhaseIndex) (a.val : PhaseIndex)

private theorem included_coordinate_hidden_zero (a : Fin 3) :
    (nativeTitsMatrixPair (includedCoordinatePoint a)).2 = 0 := by
  change (nativeTitsMatrixPair (includeHermitianMatrix _)).2 = 0
  rw [includeHermitianMatrix_pair]

private theorem included_phase_hidden_zero (s a : PhaseIndex) :
    (nativeTitsMatrixPair (includedPhasePoint s a)).2 = 0 := by
  change (nativeTitsMatrixPair (includeHermitianMatrix _)).2 = 0
  rw [includeHermitianMatrix_pair]

/-- Every first-twelve label is an actual fixed visible anchor. -/
theorem canonical_anchor_hidden_zero {C : Configuration ℝ} (hA : CanonicalAnchors C)
    (i : Fin 39) (hi : i.val < 12) :
    (nativeTitsMatrixPair (fromUpperCoordinates (C i))).2 = 0 := by
  by_cases hi3 : i.val < 3
  · let a : Fin 3 := ⟨i.val, hi3⟩
    have hIndex : framePointIndex 0 a = i := by
      apply Fin.ext
      dsimp only [framePointIndex, a]
      omega
    rw [← hIndex, hA.coordinate a, included_coordinate_hidden_zero]
  · let s : Fin 3 := ⟨(i.val - 3) / 3, by omega⟩
    let a : Fin 3 := ⟨(i.val - 3) % 3, Nat.mod_lt _ (by decide)⟩
    have hIndex : framePointIndex (canonicalPhaseFrame s) a = i := by
      apply Fin.ext
      dsimp only [framePointIndex, canonicalPhaseFrame, s, a]
      omega
    rw [← hIndex, hA.phase s a, included_phase_hidden_zero]

private theorem phase_fin_representative (s : PhaseIndex) :
    ∃ a : Fin 3, (a.val : PhaseIndex) = s := by
  have hCases : s = 0 ∨ s = 1 ∨ s = 2 :=
    (by decide : ∀ z : PhaseIndex, z = 0 ∨ z = 1 ∨ z = 2) s
  rcases hCases with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

/-- An outside point's readout against any first-twelve label is an original
scalar pair row, in its canonical increasing orientation. -/
theorem original_outside_anchor_readout {C : Configuration ℝ}
    (hC : OriginalEquations (1 / 2 : ℝ) (1 / 3 : ℝ) C)
    (i j : Fin 39) (hi : 12 ≤ i.val) (hj : j.val < 12) :
    Glennie.trace (Glennie.jordan (fromUpperCoordinates (C i))
      (fromUpperCoordinates (C j))) = (1 / 3 : ℝ) := by
  let ij : Pair 39 := ⟨(j, i), by change j.val < i.val; omega⟩
  have hDifferent : j.val / 3 ≠ i.val / 3 := by omega
  have hPair := hC.pair ij
  change coordinatePairing (C j) (C i) =
    (if j.val / 3 = i.val / 3 then 0 else (1 / 3 : ℝ)) at hPair
  rw [if_neg hDifferent, pairing_decode_native] at hPair
  calc
    _ = Glennie.trace (Glennie.jordan (fromUpperCoordinates (C j))
        (fromUpperCoordinates (C i))) := congrArg Glennie.trace (Glennie.jordan_comm _ _)
    _ = (1 / 3 : ℝ) := hPair

/-- All later labels have visible component I/3, derived from all twelve
original overlaps and the accepted included-quartet tomography theorem. -/
theorem canonical_outside_visible_third {C : Configuration ℝ}
    (hC : OriginalEquations (1 / 2 : ℝ) (1 / 3 : ℝ) C) (hA : CanonicalAnchors C)
    (i : Fin 39) (hi : 12 ≤ i.val) :
    hermitianMatrix (toTitsCoordinates (fromUpperCoordinates (C i))) =
      (1 / 3 : ℂ) • (1 : TitsComplexMatrix) := by
  apply (native_included_quartet_readouts_iff _).mp
  constructor
  · intro a
    have hj : (framePointIndex 0 a).val < 12 := by
      rw [framePointIndex_val]
      omega
    have h := original_outside_anchor_readout hC i (framePointIndex 0 a) hi hj
    rw [hA.coordinate a] at h
    exact h
  · intro s a
    obtain ⟨sf, hsf⟩ := phase_fin_representative s
    obtain ⟨af, haf⟩ := phase_fin_representative a
    have hj : (framePointIndex (canonicalPhaseFrame sf) af).val < 12 := by
      dsimp only [framePointIndex, canonicalPhaseFrame]
      omega
    have h := original_outside_anchor_readout hC i
      (framePointIndex (canonicalPhaseFrame sf) af) hi hj
    rw [hA.phase sf af, hsf, haf] at h
    exact h

/-- All39 native position cases are consequences of the original input data. -/
theorem canonical_all_positions {C : Configuration ℝ}
    (hC : OriginalEquations (1 / 2 : ℝ) (1 / 3 : ℝ) C) (hA : CanonicalAnchors C)
    (i : Fin 39) :
    (nativeTitsMatrixPair (fromUpperCoordinates (C i))).2 = 0 ∨
      hermitianMatrix (toTitsCoordinates (fromUpperCoordinates (C i))) =
        (1 / 3 : ℂ) • (1 : TitsComplexMatrix) := by
  by_cases hi : i.val < 12
  · exact Or.inl (canonical_anchor_hidden_zero hA i hi)
  · exact Or.inr (canonical_outside_visible_third hC hA i (by omega))

/-- Fixation at all twelve canonical input labels needs no solution premise. -/
theorem canonical_anchors_fixed {C : Configuration ℝ} (hA : CanonicalAnchors C)
    (V : TitsComplexMatrix) (i : Fin 39) (hi : i.val < 12) :
    coordinatePartialLeft V (C i) = C i := by
  rw [coordinatePartialLeft_apply,
    nativePartialLeft_eq_self_of_hidden_zero V _ (canonical_anchor_hidden_zero hA i hi),
    upperCoordinates_fromUpperCoordinates]

/-- Preserve the faithful four-branch original predicate. -/
theorem OriginalEquations.canonical_partial_left {C : Configuration ℝ}
    (hC : OriginalEquations (1 / 2 : ℝ) (1 / 3 : ℝ) C) (hA : CanonicalAnchors C)
    (V : TitsComplexMatrix) (hV : V * V.conjTranspose = (1 : TitsComplexMatrix))
    (hd : V.det = 1) :
    OriginalEquations (1 / 2 : ℝ) (1 / 3 : ℝ) (fun i => coordinatePartialLeft V (C i)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have hNative : Glennie.jordan (fromUpperCoordinates (C i))
        (fromUpperCoordinates (C i)) = fromUpperCoordinates (C i) := by
      apply upperCoordinateEquiv.injective
      change upperCoordinates (Glennie.jordan (fromUpperCoordinates (C i))
        (fromUpperCoordinates (C i))) = upperCoordinates (fromUpperCoordinates (C i))
      rw [← product_half_native, upperCoordinates_fromUpperCoordinates, hC.idempotent]
    have hTransformed := nativePartialLeft_idempotent_of_position V hV hd _ hNative
      (canonical_all_positions hC hA i)
    rw [product_half_native]
    simp only [decode_coordinatePartialLeft]
    exact congrArg upperCoordinates hTransformed
  · intro i
    rw [coordinatePartialLeft_trace, hC.trace_one]
  · intro f
    rw [← map_sum, hC.frame_sum, coordinatePartialLeft_unit]
  · intro ij
    rw [coordinatePartialLeft_pairing V hV hd, hC.pair]

/-- Every literal original F row, at the original real normalizations, after
the canonical partial action. The only geometric input is the twelve actual
input-anchor equalities; all39 positions and output equations are proved. -/
theorem all_fRows_canonical_partial_left {C : Configuration ℝ}
    (hF : ∀ r : Fin 2184, MvPolynomial.eval (pack C)
      (ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r) = 0)
    (hA : CanonicalAnchors C) (V : TitsComplexMatrix)
    (hV : V * V.conjTranspose = (1 : TitsComplexMatrix)) (hd : V.det = 1) :
    ∀ r : Fin 2184, MvPolynomial.eval (pack (fun i => coordinatePartialLeft V (C i)))
      (ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r) = 0 := by
  apply (originalEquations_iff_all_fRows (1 / 2 : ℝ) (1 / 3 : ℝ) _).mp
  exact OriginalEquations.canonical_partial_left
    ((originalEquations_iff_all_fRows (1 / 2 : ℝ) (1 / 3 : ℝ) C).mpr hF) hA V hV hd

end NativePolynomial.PartialAction

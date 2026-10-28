module

public import NativeComplementaryDictionary
public import NativeActualStateEquivalence

@[expose] public section

/-!
# Ordered complementary frames at the actual twelve native labels

The actual-label equivalence is composed from the native state and frame dictionaries.

The statement keeps the existing real Albert carrier, first twelve labels of
the literal native configuration, all nine cross-frame readouts, and both
central orders. It is an existence dictionary: no uniqueness, gauge quotient,
global family, phase transport, smoothness, chart or exhaustion is asserted.

This is first-party composition of accepted declarations. It completes the
actual-label join anticipated in the retained NativeActualComplementaryFrame
design, without editing that earlier prototype or copying upstream proof code.
Dependencies: NativeActualStateEquivalence source SHA256
1673c508d8546acc57599f0c8cbe8802816b02674d0e927b8bcca4f569c22805;
NativeComplementaryDictionary source SHA256
4acd0172c474eeb6fa2306a8317b95a100ef4f673a82683e718c8b075d983e65.
Their unchanged owners retain source attribution, licenses and dependency pins.
Thanks to the native-model, CKM, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace CompactAlbert.ActualFrameDictionary

open ActualQuartetStates
open QuadraticCertificate.ExactCKMConfiguration

/-- The original twelve native readouts, together with the existing ordered
frame predicate, are equivalent to either central order of an explicit
special-unitary matrix. No readout or idempotency premise is discarded. -/
theorem actual_frame_iff_specialUnitary_central_order
    (p : Fin 3 → Glennie.Albert) :
    (Glennie.Frame p ∧
      ∀ k : Fin 3, ∀ i : Fin 39, i.val < 12 →
        Glennie.trace (Glennie.jordan (p k) (nativePoint i)) = (1 / 3 : ℝ)) ↔
      ∃ U : TitsComplexMatrix,
        (U * U.conjTranspose = (1 : TitsComplexMatrix) ∧ U.det = 1) ∧
          (p = nativeCentralTriple U ∨ p = nativeReverseCentralTriple U) := by
  constructor
  · rintro ⟨hframe, hactual⟩
    refine (native_complementary_frame_iff_exists_central_order p).mp
      ⟨hframe, ?_, ?_⟩
    · intro k
      exact ((actualQuartetReadouts_iff_literal (p k)).mp (hactual k)).1
    · intro k
      exact ((actualQuartetReadouts_iff_literal (p k)).mp (hactual k)).2
  · intro hcentral
    obtain ⟨hframe, hcoordinate, hphase⟩ :=
      (native_complementary_frame_iff_exists_central_order p).mpr hcentral
    exact ⟨hframe, fun k =>
      (actualQuartetReadouts_iff_literal (p k)).mpr
        ⟨hcoordinate k, hphase k⟩⟩

/-- Two actual complementary ordered frames have all nine cross-readouts
equal to one third exactly when they have special-unitary central-order
representatives with zero complex Hilbert-Schmidt inner product. -/
theorem actual_frame_pair_iff_trace_orthogonal_representatives
    (p q : Fin 3 → Glennie.Albert) :
    ((Glennie.Frame p ∧
        ∀ k : Fin 3, ∀ i : Fin 39, i.val < 12 →
          Glennie.trace (Glennie.jordan (p k) (nativePoint i)) = (1 / 3 : ℝ)) ∧
      (Glennie.Frame q ∧
        ∀ k : Fin 3, ∀ i : Fin 39, i.val < 12 →
          Glennie.trace (Glennie.jordan (q k) (nativePoint i)) = (1 / 3 : ℝ)) ∧
      (∀ k l : Fin 3,
        Glennie.trace (Glennie.jordan (p k) (q l)) = (1 / 3 : ℝ))) ↔
      ∃ U V : TitsComplexMatrix,
        (U * U.conjTranspose = (1 : TitsComplexMatrix) ∧ U.det = 1) ∧
        (V * V.conjTranspose = (1 : TitsComplexMatrix) ∧ V.det = 1) ∧
        (p = nativeCentralTriple U ∨ p = nativeReverseCentralTriple U) ∧
        (q = nativeCentralTriple V ∨ q = nativeReverseCentralTriple V) ∧
        (U.conjTranspose * V).trace = 0 := by
  constructor
  · rintro ⟨hp, hq, hpq⟩
    obtain ⟨U, hU, hporder⟩ :=
      (actual_frame_iff_specialUnitary_central_order p).mp hp
    obtain ⟨V, hV, hqorder⟩ :=
      (actual_frame_iff_specialUnitary_central_order q).mp hq
    exact ⟨U, V, hU, hV, hporder, hqorder,
      (native_ordered_central_triples_overlap_iff_hilbertSchmidt
        U V p q hporder hqorder).mp hpq⟩
  · rintro ⟨U, V, hU, hV, hporder, hqorder, htrace⟩
    exact ⟨
      (actual_frame_iff_specialUnitary_central_order p).mpr ⟨U, hU, hporder⟩,
      (actual_frame_iff_specialUnitary_central_order q).mpr ⟨V, hV, hqorder⟩,
      (native_ordered_central_triples_overlap_iff_hilbertSchmidt
        U V p q hporder hqorder).mpr htrace⟩

end CompactAlbert.ActualFrameDictionary

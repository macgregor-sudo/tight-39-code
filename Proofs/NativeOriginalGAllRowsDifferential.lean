module

public import NativeOriginalGCrossDifferential

/-!
# All3159 original G rows bind to the four actual native differentials

The target is the unchanged original translated3159-row,1053-column matrix
at h=1/2,t=1/3, acting on an arbitrary real tangent array u at arbitrary p.
The actual gNumber equivalence covers its four literal row constructors;
the established block iff results give exactly the actual native idempotency,
within-frame product, frame-sum and cross-frame trace differentials.
There is no anchor, concrete lift, solution or geometric hypothesis.

First-party finite case assembly; existing row/coordinate/native owners are
imported without redefining their residuals, indexing or carrier. Imported
compact-albert-recognition, https://github.com/macgregor-sudo/compact-albert-recognition,
commit40d3b344180d9ddb78aaa2876873377c1e631515, and Mathlib,
https://github.com/leanprover-community/mathlib4,
commit065356127b1dc0016f66b7283ce0ce2c4055aa55, retain Apache-2.0 notices
in their owners. No third-party proof copied; no release license assigned.
Thanks to their contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke,1676.
-/

@[expose] public section
noncomputable section
namespace NativePolynomial.ConfigurationResiduals.FirstCoefficients
open scoped BigOperators
open CoordinateMaps ConfigurationResidualIndices PolynomialJets
open NativePolynomial.ConfigurationResiduals.MixedCoefficients

/-- Exact all-original-row iff, preserving every numbered row and1053 columns.
The right side uses only literal native differentials of the existing decoder. -/
theorem original_all_gRows_linearMatrix_zero_iff_native
    (p u : Fin 1053 → ℝ) :
    (∀ r : Fin 3159, (∑ n : Fin 1053,
      equationLinearMatrix
        (fun s : Fin 3159 => translate p (gRow (1 / 2 : ℝ) (1 / 3 : ℝ) s)) r n * u n) = 0) ↔
      ((∀ i : Fin 39, (2 : ℝ) • Glennie.jordan
        (fromUpperCoordinates (pointValues p i))
        (fromUpperCoordinates (pointValues u i)) =
          fromUpperCoordinates (pointValues u i)) ∧
      (∀ (f : Fin 13) (s : Fin 3),
        let a : Fin 39 := framePointIndex f (withinPair s).val.1
        let b : Fin 39 := framePointIndex f (withinPair s).val.2
        Glennie.jordan (fromUpperCoordinates (pointValues p a))
          (fromUpperCoordinates (pointValues u b)) +
        Glennie.jordan (fromUpperCoordinates (pointValues u a))
          (fromUpperCoordinates (pointValues p b)) = 0) ∧
      (∀ f : Fin 13,
        (∑ a : Fin 3, fromUpperCoordinates (pointValues u (framePointIndex f a))) = 0) ∧
      (∀ (fg : Pair 13) (a b : Fin 3),
        let i : Fin 39 := framePointIndex fg.val.1 a
        let j : Fin 39 := framePointIndex fg.val.2 b
        Glennie.trace (Glennie.jordan
          (fromUpperCoordinates (pointValues p i))
          (fromUpperCoordinates (pointValues u j))) +
        Glennie.trace (Glennie.jordan
          (fromUpperCoordinates (pointValues u i))
          (fromUpperCoordinates (pointValues p j))) = 0)) := by
  constructor
  · intro hall
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      exact (original_gId_linearMatrix_zero_iff_native (1 / 2 : ℝ) (1 / 3 : ℝ)
        (by norm_num) p u i).mp (fun k => hall (gNumber (gId i k)))
    · intro f s
      exact (original_gWithin_linearMatrix_zero_iff_native p u f s).mp
        (fun k => hall (gNumber (gWithin f s k)))
    · intro f
      exact (original_gSum_linearMatrix_zero_iff_native p u f).mp
        (fun k => hall (gNumber (gSum f k)))
    · intro fg a b
      exact (original_gCross_linearMatrix_zero_iff_native p u fg a b).mp
        (hall (gNumber (gCross fg a b)))
  · rintro ⟨hid, hwithin, hsum, hcross⟩
    have htyped (q : GLabel) : (∑ n : Fin 1053,
        equationLinearMatrix
          (fun s : Fin 3159 => translate p (gRow (1 / 2 : ℝ) (1 / 3 : ℝ) s))
          (gNumber q) n * u n) = 0 := by
      rcases q with ⟨i, k⟩ | ⟨⟨f, s⟩, k⟩ | ⟨f, k⟩ | ⟨fg, a, b⟩
      · exact ((original_gId_linearMatrix_zero_iff_native (1 / 2 : ℝ) (1 / 3 : ℝ)
          (by norm_num) p u i).mpr (hid i)) k
      · exact ((original_gWithin_linearMatrix_zero_iff_native p u f s).mpr (hwithin f s)) k
      · exact ((original_gSum_linearMatrix_zero_iff_native p u f).mpr (hsum f)) k
      · exact (original_gCross_linearMatrix_zero_iff_native p u fg a b).mpr (hcross fg a b)
    intro r
    simpa only [Equiv.apply_symm_apply] using htyped (gNumber.symm r)

end NativePolynomial.ConfigurationResiduals.FirstCoefficients

#print axioms NativePolynomial.ConfigurationResiduals.FirstCoefficients.original_all_gRows_linearMatrix_zero_iff_native

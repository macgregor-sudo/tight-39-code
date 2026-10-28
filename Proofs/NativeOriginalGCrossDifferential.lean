module

public import NativeOriginalGSumDifferential

/-!
# Original G cross rows bind to the actual native trace differential

Canonical gNumber(gCross fg a b) rows of the unchanged centered original G
matrix keep all1053 columns at h=1/2,t=1/3. The action is the sum of actual
native trace-Jordan pairings with the two original point/tangent orders.
The original strict frame pair and ordered outcomes retain their exact owners.
The weighted coordinate pairing is proved equal to actual native trace using
the accepted product contraction and native coordinate identities.

First-party theorem composition; no residual, row map, pairing or native
carrier is replaced. Imported compact-albert-recognition,
https://github.com/macgregor-sudo/compact-albert-recognition,
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

namespace NativePolynomial.CoordinateMaps

/-- Existing diagonal coordinate trace is exactly the actual native trace of
the actual decoder. No trace or pairing identity is supplied as a premise. -/
theorem coordinateTrace_real_eq_native_trace (x : Fin 27 → ℝ) :
    coordinateTrace x = Glennie.trace (fromUpperCoordinates x) := by
  rw [coordinateTrace_apply]
  rfl

/-- The actual integer-weight coordinate pairing is the actual unnormalized
native trace pairing, via the accepted normalized product identity. -/
theorem coordinatePairing_real_eq_native_trace (x y : Fin 27 → ℝ) :
    coordinatePairing x y =
      Glennie.trace (Glennie.jordan (fromUpperCoordinates x) (fromUpperCoordinates y)) := by
  calc
    _ = coordinateTrace (coordinateProduct (1 / 2 : ℝ) x y) :=
      (coordinateTrace_product (1 / 2 : ℝ) (by norm_num) x y).symm
    _ = coordinateTrace (upperCoordinates
        (Glennie.jordan (fromUpperCoordinates x) (fromUpperCoordinates y))) := by
      rw [coordinateProduct_real_eq_native_coordinates (1 / 2 : ℝ) (by norm_num)]
    _ = Glennie.trace (fromUpperCoordinates (upperCoordinates
        (Glennie.jordan (fromUpperCoordinates x) (fromUpperCoordinates y)))) :=
      coordinateTrace_real_eq_native_trace _
    _ = _ := by rw [fromUpperCoordinates_upperCoordinates]

end NativePolynomial.CoordinateMaps

namespace NativePolynomial.ConfigurationResiduals.FirstCoefficients
open scoped BigOperators
open CoordinateMaps ConfigurationResidualIndices PolynomialJets
open NativePolynomial.ConfigurationResiduals.MixedCoefficients

/-- Exact original cross-row action, with the original left/right frame and
outcome order, full1053 columns and actual native product/trace. -/
theorem original_gCross_linearMatrix_action_eq_native
    (p u : Fin 1053 → ℝ) (fg : Pair 13) (a b : Fin 3) :
    let i : Fin 39 := framePointIndex fg.val.1 a
    let j : Fin 39 := framePointIndex fg.val.2 b
    (∑ n : Fin 1053,
      equationLinearMatrix
        (fun r : Fin 3159 => translate p (gRow (1 / 2 : ℝ) (1 / 3 : ℝ) r))
        (gNumber (gCross fg a b)) n * u n) =
      Glennie.trace (Glennie.jordan
        (fromUpperCoordinates (pointValues p i))
        (fromUpperCoordinates (pointValues u j))) +
      Glennie.trace (Glennie.jordan
        (fromUpperCoordinates (pointValues u i))
        (fromUpperCoordinates (pointValues p j))) := by
  dsimp only
  rw [actual_linearMatrix_action]
  simp only [firstRow, Equiv.symm_apply_apply, firstResidual, gCross,
    mixedResidual, linearResidual, add_zero]
  rw [coordinatePairing_real_eq_native_trace, coordinatePairing_real_eq_native_trace]

/-- Literal original scalar cross-row vanishing iff its actual native
trace differential vanishes; no other row family is assumed. -/
theorem original_gCross_linearMatrix_zero_iff_native
    (p u : Fin 1053 → ℝ) (fg : Pair 13) (a b : Fin 3) :
    let i : Fin 39 := framePointIndex fg.val.1 a
    let j : Fin 39 := framePointIndex fg.val.2 b
    (∑ n : Fin 1053,
      equationLinearMatrix
        (fun r : Fin 3159 => translate p (gRow (1 / 2 : ℝ) (1 / 3 : ℝ) r))
        (gNumber (gCross fg a b)) n * u n) = 0 ↔
      Glennie.trace (Glennie.jordan
        (fromUpperCoordinates (pointValues p i))
        (fromUpperCoordinates (pointValues u j))) +
      Glennie.trace (Glennie.jordan
        (fromUpperCoordinates (pointValues u i))
        (fromUpperCoordinates (pointValues p j))) = 0 := by
  dsimp only
  rw [original_gCross_linearMatrix_action_eq_native]

end NativePolynomial.ConfigurationResiduals.FirstCoefficients

#print axioms NativePolynomial.CoordinateMaps.coordinateTrace_real_eq_native_trace
#print axioms NativePolynomial.CoordinateMaps.coordinatePairing_real_eq_native_trace
#print axioms NativePolynomial.ConfigurationResiduals.FirstCoefficients.original_gCross_linearMatrix_action_eq_native
#print axioms NativePolynomial.ConfigurationResiduals.FirstCoefficients.original_gCross_linearMatrix_zero_iff_native

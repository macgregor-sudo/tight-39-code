module

public import NativeOriginalGWithinDifferential

/-!
# Original G sum rows bind to the actual native variation sum

At h=1/2,t=1/3, canonical gNumber(gSum f k) rows of the unchanged centered
original G matrix retain all1053 columns. Their action is coordinate k of the
actual native sum of the three decoded variations in original frame order.
The original row number is2106+27*f+k. The base remains in the matrix target;
the derivative of the subtracted frame unit is zero. No other block is assumed.

First-party composition of the accepted coefficient and actual real-linear
coordinate owners. No decoder, residual, row number or native carrier is
redefined. Imported compact-albert-recognition,
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
namespace NativePolynomial.ConfigurationResiduals.FirstCoefficients
open scoped BigOperators
open CoordinateMaps ConfigurationResidualIndices PolynomialJets
open NativePolynomial.ConfigurationResiduals.MixedCoefficients

/-- Exact original full1053-column matrix action on each canonical G sum row. -/
theorem original_gSum_linearMatrix_action_eq_native
    (p u : Fin 1053 → ℝ) (f : Fin 13) (k : Fin 27) :
    (∑ n : Fin 1053,
      equationLinearMatrix
        (fun r : Fin 3159 => translate p (gRow (1 / 2 : ℝ) (1 / 3 : ℝ) r))
        (gNumber (gSum f k)) n * u n) =
      upperCoordinates
        (∑ a : Fin 3, fromUpperCoordinates (pointValues u (framePointIndex f a))) k := by
  have hcoords : upperCoordinates
      (∑ a : Fin 3, fromUpperCoordinates (pointValues u (framePointIndex f a))) k =
      ∑ a : Fin 3, pointValues u (framePointIndex f a) k := by
    change upperCoordinateEquiv (∑ a : Fin 3,
      fromUpperCoordinates (pointValues u (framePointIndex f a))) k = _
    rw [map_sum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    change upperCoordinates (fromUpperCoordinates (pointValues u (framePointIndex f a))) k = _
    rw [upperCoordinates_fromUpperCoordinates]
  rw [actual_linearMatrix_action, hcoords]
  simp only [firstRow, Equiv.symm_apply_apply, firstResidual, gSum,
    mixedResidual, linearResidual, zero_add]

/-- The complete27-row original sum block vanishes iff the actual three
native decoded variations sum to zero. No other native equation is assumed. -/
theorem original_gSum_linearMatrix_zero_iff_native
    (p u : Fin 1053 → ℝ) (f : Fin 13) :
    (∀ k : Fin 27, (∑ n : Fin 1053,
      equationLinearMatrix
        (fun r : Fin 3159 => translate p (gRow (1 / 2 : ℝ) (1 / 3 : ℝ) r))
        (gNumber (gSum f k)) n * u n) = 0) ↔
      (∑ a : Fin 3, fromUpperCoordinates (pointValues u (framePointIndex f a))) = 0 := by
  simp only [original_gSum_linearMatrix_action_eq_native]
  constructor
  · intro hz
    apply upperCoordinateEquiv.injective
    change upperCoordinates (∑ a : Fin 3, _) = upperCoordinates (0 : Glennie.Albert)
    funext k
    have hzero : upperCoordinates (0 : Glennie.Albert) k = 0 := by
      change upperCoordinateEquiv (0 : Glennie.Albert) k = 0
      rw [map_zero]
      rfl
    rw [hzero]
    exact hz k
  · intro hnative k
    rw [hnative]
    change upperCoordinateEquiv (0 : Glennie.Albert) k = 0
    rw [map_zero]
    rfl

end NativePolynomial.ConfigurationResiduals.FirstCoefficients

#print axioms NativePolynomial.ConfigurationResiduals.FirstCoefficients.original_gSum_linearMatrix_action_eq_native
#print axioms NativePolynomial.ConfigurationResiduals.FirstCoefficients.original_gSum_linearMatrix_zero_iff_native

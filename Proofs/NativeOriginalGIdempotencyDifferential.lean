module

public import NativeConfigurationJacobianDirectional

/-!
# Original G idempotency rows bind to the actual native differential

The target matrix is the unchanged1053-column equationLinearMatrix of every
translated numbered G residual. At the canonical gId(i,k) rows its action
is the actual upper-coordinate projection of2*jordan(p_i,u_i)-u_i, where
p_i and u_i are decoded through the existing native coordinate inverse.
The original index maps, row numbers, tensor numerator and linear term remain
owned by their accepted source modules. The scalar normalization2*h=1 is
explicit. This binds the idempotency block only, not the remaining original
within-frame, sum, cross-pair or F-row blocks.

First-party finite contraction and existing coefficient theorem composition;
no replacement residual or native carrier is defined. Imported source
compact-albert-recognition, https://github.com/macgregor-sudo/compact-albert-recognition,
commit40d3b344180d9ddb78aaa2876873377c1e631515, and Mathlib,
https://github.com/leanprover-community/mathlib4,
commit065356127b1dc0016f66b7283ce0ce2c4055aa55, retain Apache-2.0 notices
in their owners. No third-party proof is copied and no release license is
assigned. Thanks to their contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke,1676.
-/

@[expose] public section
noncomputable section

namespace NativePolynomial.CoordinateMaps
open scoped BigOperators
open IntegralStructureConstants

/-- The existing real tensor contraction is exactly the actual native product
in its existing coordinates. The normalization is explicit and unrestricted. -/
theorem coordinateProduct_real_eq_native_coordinates
    (h : ℝ) (hHalf : (2 : ℝ) * h = 1) (x y : Fin 27 → ℝ) :
    coordinateProduct h x y =
      upperCoordinates (Glennie.jordan (fromUpperCoordinates x) (fromUpperCoordinates y)) := by
  funext k
  rw [upperCoordinates_jordan]
  simp only [coordinateProduct_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [numerator_cast_eq_two_nativeStructureConstant]
  have hc : h * (2 * nativeStructureConstant i j k) = nativeStructureConstant i j k := by
    calc
      _ = (2 * h) * nativeStructureConstant i j k := by ring
      _ = _ := by rw [hHalf, one_mul]
  rw [hc]

end NativePolynomial.CoordinateMaps

namespace NativePolynomial.ConfigurationResiduals.FirstCoefficients
open scoped BigOperators
open CoordinateMaps ConfigurationResidualIndices PolynomialJets
open NativePolynomial.ConfigurationResiduals.MixedCoefficients

/-- Every original idempotency row action, retaining all1053 matrix columns,
is the corresponding coordinate of the actual native linearized equation. -/
theorem original_gId_linearMatrix_action_eq_native
    (h t : ℝ) (hHalf : (2 : ℝ) * h = 1) (p u : Fin 1053 → ℝ)
    (i : Fin 39) (k : Fin 27) :
    (∑ n : Fin 1053,
      equationLinearMatrix (fun r : Fin 3159 => translate p (gRow h t r))
        (gNumber (gId i k)) n * u n) =
      upperCoordinates
        ((2 : ℝ) • Glennie.jordan
          (fromUpperCoordinates (pointValues p i))
          (fromUpperCoordinates (pointValues u i)) -
          fromUpperCoordinates (pointValues u i)) k := by
  have hp := congrFun (coordinateProduct_real_eq_native_coordinates h hHalf
    (pointValues p i) (pointValues u i)) k
  have hcoords : upperCoordinates
      ((2 : ℝ) • Glennie.jordan
        (fromUpperCoordinates (pointValues p i))
        (fromUpperCoordinates (pointValues u i)) -
        fromUpperCoordinates (pointValues u i)) k =
      2 * upperCoordinates (Glennie.jordan
        (fromUpperCoordinates (pointValues p i))
        (fromUpperCoordinates (pointValues u i))) k - pointValues u i k := by
    change (upperCoordinateEquiv (_ - _)) k = _
    rw [map_sub, map_smul]
    change 2 * upperCoordinates (Glennie.jordan
      (fromUpperCoordinates (pointValues p i))
      (fromUpperCoordinates (pointValues u i))) k -
      upperCoordinates (fromUpperCoordinates (pointValues u i)) k = _
    rw [upperCoordinates_fromUpperCoordinates]
  rw [actual_linearMatrix_action, hcoords]
  simp only [firstRow, Equiv.symm_apply_apply, firstResidual, gId,
    mixedResidual, linearResidual]
  rw [← hp]
  ring

/-- The full27-row original idempotency block vanishes exactly when its
actual decoded native point/variation satisfy native idempotency linearization. -/
theorem original_gId_linearMatrix_zero_iff_native
    (h t : ℝ) (hHalf : (2 : ℝ) * h = 1) (p u : Fin 1053 → ℝ) (i : Fin 39) :
    (∀ k : Fin 27, (∑ n : Fin 1053,
      equationLinearMatrix (fun r : Fin 3159 => translate p (gRow h t r))
        (gNumber (gId i k)) n * u n) = 0) ↔
      (2 : ℝ) • Glennie.jordan
        (fromUpperCoordinates (pointValues p i))
        (fromUpperCoordinates (pointValues u i)) =
          fromUpperCoordinates (pointValues u i) := by
  simp only [original_gId_linearMatrix_action_eq_native h t hHalf p u i]
  constructor
  · intro hz
    apply sub_eq_zero.mp
    apply upperCoordinateEquiv.injective
    change upperCoordinates (_ - _) = upperCoordinates (0 : Glennie.Albert)
    funext k
    have hzero : upperCoordinates (0 : Glennie.Albert) k = 0 := by
      change upperCoordinateEquiv (0 : Glennie.Albert) k = 0
      rw [map_zero]
      rfl
    rw [hzero]
    exact hz k
  · intro hid k
    rw [hid, sub_self]
    change upperCoordinateEquiv (0 : Glennie.Albert) k = 0
    rw [map_zero]
    rfl

end NativePolynomial.ConfigurationResiduals.FirstCoefficients

#print axioms NativePolynomial.CoordinateMaps.coordinateProduct_real_eq_native_coordinates
#print axioms NativePolynomial.ConfigurationResiduals.FirstCoefficients.original_gId_linearMatrix_action_eq_native
#print axioms NativePolynomial.ConfigurationResiduals.FirstCoefficients.original_gId_linearMatrix_zero_iff_native

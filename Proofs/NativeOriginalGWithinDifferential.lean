module

public import NativeOriginalGIdempotencyDifferential

/-!
# Original within-frame G rows bind to the actual native differential

Canonical gNumber(gWithin f s k) rows of the unchanged centered original G
matrix retain all1053 columns, with h=1/2,t=1/3. Their action is the actual
native differential jordan(p_a,u_b)+jordan(u_a,p_b) in coordinate k; a,b
are the existing withinPair endpoints in the existing framePointIndex order.
Both product orders are retained. No base-solution or other-row premise occurs.

First-party composition of accepted coefficient/native coordinate owners.
No residual, numbering, decoder or algebra carrier is replaced. Imported
compact-albert-recognition, https://github.com/macgregor-sudo/compact-albert-recognition,
commit40d3b344180d9ddb78aaa2876873377c1e631515, and Mathlib,
https://github.com/leanprover-community/mathlib4,
commit065356127b1dc0016f66b7283ce0ce2c4055aa55, retain Apache-2.0 notices
in their owners. No third-party proof is copied; no release license assigned.
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

/-- Exact action on a canonical original within-frame G row, specialized to
the original half-product and one-third overlap normalization. -/
theorem original_gWithin_linearMatrix_action_eq_native
    (p u : Fin 1053 → ℝ) (f : Fin 13) (s : Fin 3) (k : Fin 27) :
    let a : Fin 39 := framePointIndex f (withinPair s).val.1
    let b : Fin 39 := framePointIndex f (withinPair s).val.2
    (∑ n : Fin 1053,
      equationLinearMatrix
        (fun r : Fin 3159 => translate p (gRow (1 / 2 : ℝ) (1 / 3 : ℝ) r))
        (gNumber (gWithin f s k)) n * u n) =
      upperCoordinates
        (Glennie.jordan (fromUpperCoordinates (pointValues p a))
          (fromUpperCoordinates (pointValues u b)) +
        Glennie.jordan (fromUpperCoordinates (pointValues u a))
          (fromUpperCoordinates (pointValues p b))) k := by
  have hprod (x y : Fin 27 → ℝ) :
      coordinateProduct (1 / 2 : ℝ) x y k =
        upperCoordinates (Glennie.jordan (fromUpperCoordinates x) (fromUpperCoordinates y)) k :=
    congrFun (coordinateProduct_real_eq_native_coordinates (1 / 2 : ℝ)
      (by norm_num) x y) k
  dsimp only
  rw [actual_linearMatrix_action, upperCoordinates_add]
  simp only [firstRow, Equiv.symm_apply_apply, firstResidual, gWithin,
    mixedResidual, linearResidual, add_zero, Pi.add_apply]
  rw [hprod, hprod]

/-- All27 coordinates in this original within-frame row block vanish iff
the actual native product differential at its original ordered endpoints is zero. -/
theorem original_gWithin_linearMatrix_zero_iff_native
    (p u : Fin 1053 → ℝ) (f : Fin 13) (s : Fin 3) :
    let a : Fin 39 := framePointIndex f (withinPair s).val.1
    let b : Fin 39 := framePointIndex f (withinPair s).val.2
    (∀ k : Fin 27, (∑ n : Fin 1053,
      equationLinearMatrix
        (fun r : Fin 3159 => translate p (gRow (1 / 2 : ℝ) (1 / 3 : ℝ) r))
        (gNumber (gWithin f s k)) n * u n) = 0) ↔
      Glennie.jordan (fromUpperCoordinates (pointValues p a))
        (fromUpperCoordinates (pointValues u b)) +
      Glennie.jordan (fromUpperCoordinates (pointValues u a))
        (fromUpperCoordinates (pointValues p b)) = 0 := by
  dsimp only
  simp only [original_gWithin_linearMatrix_action_eq_native]
  constructor
  · intro hz
    apply upperCoordinateEquiv.injective
    change upperCoordinates (_ + _) = upperCoordinates (0 : Glennie.Albert)
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

#print axioms NativePolynomial.ConfigurationResiduals.FirstCoefficients.original_gWithin_linearMatrix_action_eq_native
#print axioms NativePolynomial.ConfigurationResiduals.FirstCoefficients.original_gWithin_linearMatrix_zero_iff_native

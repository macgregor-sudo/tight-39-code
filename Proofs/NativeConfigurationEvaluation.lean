module

public import NativeConfigurationMixedCoefficients

@[expose] public section

/-!
# Evaluation of every actual numbered configuration polynomial

The finite scalar formulas are derived from the existing gRow and its
canonical numbering. They retain all original linear and constant terms.
This generic semantic connection is intended for later full point-solution
checking; no frozen point value, nonzero support or solution premise is
assumed or asserted. Products, pairings, units, variables and row labels
are the existing imported definitions.

First-party elementary ring-homomorphism calculations, with no novelty
claim or copied upstream implementation. Lean4.35.0-rc2 and
mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55. Retained native/Apache-2.0
provenance remains in ../THIRD_PARTY_NOTICES.md#native-albert-code and imports.
Thanks to the native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke,1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace NativePolynomial.ConfigurationResiduals.Evaluation

open scoped BigOperators
open MvPolynomial CoordinateMaps ConfigurationResidualIndices
open NativePolynomial.ConfigurationResiduals.MixedCoefficients

variable {R : Type*} [CommRing R]

/-- Derived scalar formulas, including the original subtraction/unit/overlap terms. -/
def valueResidual (h t : R) (p : Fin 1053 → R) : GLabel → R
  | .inl (i, k) =>
      coordinateProduct h (pointValues p i) (pointValues p i) k - pointValues p i k
  | .inr (.inl ((f, s), k)) =>
      coordinateProduct h
        (pointValues p (framePointIndex f (withinPair s).val.1))
        (pointValues p (framePointIndex f (withinPair s).val.2)) k
  | .inr (.inr (.inl (f, k))) =>
      (∑ a : Fin 3, pointValues p (framePointIndex f a) k) - coordinateUnit k
  | .inr (.inr (.inr (fg, (a, b)))) =>
      coordinatePairing (pointValues p (framePointIndex fg.val.1 a))
        (pointValues p (framePointIndex fg.val.2 b)) - t

def valueRow (h t : R) (p : Fin 1053 → R) (r : Fin 3159) : R :=
  valueResidual h t p (gNumber.symm r)

theorem eval_point (p : Fin 1053 → R) (i : Fin 39) (k : Fin 27) :
    MvPolynomial.eval p (point i k) = pointValues p i k := by
  simp only [point, MvPolynomial.eval_X, pointValues]

/-- Evaluation retains the full integer structure tensor and its factor h. -/
theorem eval_coordinateProduct (p : Fin 1053 → R) (h : R)
    (x y : Fin 27 → MvPolynomial (Fin 1053) R) (k : Fin 27) :
    MvPolynomial.eval p (coordinateProduct (C h) x y k) =
      coordinateProduct h (fun i => MvPolynomial.eval p (x i))
        (fun j => MvPolynomial.eval p (y j)) k := by
  simp only [coordinateProduct_apply, map_sum, map_mul, MvPolynomial.eval_C, map_intCast]

theorem eval_coordinatePairing (p : Fin 1053 → R)
    (x y : Fin 27 → MvPolynomial (Fin 1053) R) :
    MvPolynomial.eval p (coordinatePairing x y) =
      coordinatePairing (fun i => MvPolynomial.eval p (x i))
        (fun j => MvPolynomial.eval p (y j)) := by
  simp only [coordinatePairing, map_sum, map_mul, map_intCast]

private theorem eval_coordinateUnit (p : Fin 1053 → R) (k : Fin 27) :
    MvPolynomial.eval p (coordinateUnit k) = (coordinateUnit (P := R) k) := by
  unfold coordinateUnit
  split_ifs <;> simp only [map_one, map_zero]

private theorem gLabel_eval (h t : R) (p : Fin 1053 → R) (q : GLabel) :
    MvPolynomial.eval p (gRow h t (gNumber q)) = valueResidual h t p q := by
  rcases q with ⟨i, k⟩ | ⟨⟨f, s⟩, k⟩ | ⟨f, k⟩ | ⟨fg, a, b⟩
  · change MvPolynomial.eval p (gRow h t (gNumber (gId i k))) = _
    rw [gRow_id]
    simp only [FrameResiduals.idempotencyResidual, Pi.sub_apply,
      map_sub, eval_coordinateProduct, eval_point, valueResidual, gId, gWithin, gSum, gCross]
  · change MvPolynomial.eval p (gRow h t (gNumber (gWithin f s k))) = _
    rw [gRow_within, eval_coordinateProduct]
    simp only [eval_point, valueResidual, gId, gWithin, gSum, gCross]
  · change MvPolynomial.eval p (gRow h t (gNumber (gSum f k))) = _
    rw [gRow_sum]
    simp only [map_sub, map_sum, eval_point, eval_coordinateUnit, valueResidual, gSum]
  · change MvPolynomial.eval p (gRow h t (gNumber (gCross fg a b))) = _
    rw [gRow_cross]
    simp only [map_sub, eval_coordinatePairing, eval_point, MvPolynomial.eval_C, valueResidual, gCross]

/-- Every original numbered polynomial evaluates to its proved scalar formula. -/
theorem gRow_eval (h t : R) (p : Fin 1053 → R) (r : Fin 3159) :
    MvPolynomial.eval p (gRow h t r) = valueRow h t p r := by
  unfold valueRow
  simpa only [gNumber.apply_symm_apply] using gLabel_eval h t p (gNumber.symm r)

/-- A complete finite value certificate gives exactly the actual point equation. -/
theorem all_gRow_eval_zero_iff (h t : R) (p : Fin 1053 → R) :
    (∀ r : Fin 3159, MvPolynomial.eval p (gRow h t r) = 0) ↔
      ∀ r : Fin 3159, valueRow h t p r = 0 := by
  simp only [gRow_eval]

end NativePolynomial.ConfigurationResiduals.Evaluation

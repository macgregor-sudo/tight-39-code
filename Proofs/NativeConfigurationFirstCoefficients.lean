module

public import NativeConfigurationMixedCoefficients
public import AffineFirstMonomialCoefficient

@[expose] public section

/-!
# First directional coefficients of every actual numbered G residual

The existing affineSubstitution and gRow supply the polynomial expression.
Its first coefficient is the existing mixed contraction of the base point
and tangent, plus the actual linear residual: minus the tangent for
idempotency, the sum of frame tangents for frame sums, and zero for the
other rows. Both product orders are retained for within/cross rows.

This is a generic polynomial theorem, without frozen point, tangent or
annihilator arithmetic. It does not establish a tangent or Jacobian-rank
certificate. The existing product, residuals, numbering and affine maps
are imported, not redeclared. First-party elementary coefficient algebra;
no upstream proof body is copied and no novelty is claimed.
Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55; Lean4.35.0-rc2. Native
provenance and retained Apache-2.0 notices are in
../THIRD_PARTY_NOTICES.md#native-albert-code and the imported modules.
Thanks to the native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke,1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace NativePolynomial.ConfigurationResiduals.FirstCoefficients

open scoped BigOperators
open MvPolynomial CoordinateMaps ConfigurationResidualIndices
open PolynomialJets.AffineMixedCoefficients
open NativePolynomial.ConfigurationResiduals.MixedCoefficients

variable {R : Type*} [CommRing R]

/-- The actual original linear terms, in the existing typed row order. -/
def linearResidual (u : Fin 1053 → R) : GLabel → R
  | .inl (i, k) => -pointValues u i k
  | .inr (.inl _) => 0
  | .inr (.inr (.inl (f, k))) =>
      ∑ a : Fin 3, pointValues u (framePointIndex f a) k
  | .inr (.inr (.inr _)) => 0

/-- The base-point/tangent bilinear part plus all original linear terms. -/
def firstResidual (h : R) (p u : Fin 1053 → R) (q : GLabel) : R :=
  mixedResidual h p u q + linearResidual u q

/-- Use the same sole inverse index equivalence as gRow and mixedRow. -/
def firstRow (h : R) (p u : Fin 1053 → R) (r : Fin 3159) : R :=
  firstResidual h p u (gNumber.symm r)

private theorem first_coeff_sub (p q : MvPolynomial (Fin 2) R) :
    (p - q).coeff firstExponent = p.coeff firstExponent - q.coeff firstExponent :=
  map_sub (lcoeff R firstExponent) p q

private theorem first_coeff_mul_C (p : MvPolynomial (Fin 2) R) (a : R) :
    (p * C a).coeff firstExponent = p.coeff firstExponent * a := by
  rw [mul_comm, coeff_C_mul, mul_comm]

/-- The actual finite tensor contributes both base-point/tangent orders. -/
theorem coordinateProduct_first_coeff (h : R) (p u v q s t : Fin 27 → R) (k : Fin 27) :
    (coordinateProduct (C h) (affineVector p u v) (affineVector q s t) k).coeff
        firstExponent =
      coordinateProduct h p s k + coordinateProduct h u q k := by
  rw [coordinateProduct_polynomial_apply]
  simp only [tensorPolynomial, coeff_sum, first_coeff_mul_C, affineVector,
    affineTwo_mul_first_coeff, coordinateProduct_apply, add_mul, Finset.sum_add_distrib]

/-- The pairing retains the same diagonal/upper-slot integer weights. -/
theorem coordinatePairing_first_coeff (p u v q s t : Fin 27 → R) :
    (coordinatePairing (affineVector p u v) (affineVector q s t)).coeff firstExponent =
      coordinatePairing p s + coordinatePairing u q := by
  have hForm : coordinatePairing (affineVector p u v) (affineVector q s t) =
      ∑ k : Fin 27, C (IntegralStructureConstants.coordinateTraceWeight k : R) *
        (affineTwo (p k) (u k) (v k) * affineTwo (q k) (s k) (t k)) := by
    unfold coordinatePairing affineVector
    apply Finset.sum_congr rfl
    intro k _
    rw [map_intCast, mul_assoc]
  rw [hForm]
  simp only [coeff_sum, coeff_C_mul, affineTwo_mul_first_coeff]
  simp only [coordinatePairing, mul_add, ← mul_assoc, Finset.sum_add_distrib]

private theorem substitution_point (p u v : Fin 1053 → R) (i : Fin 39) (k : Fin 27) :
    affineSubstitution p u v (point i k) =
      affineTwo (pointValues p i k) (pointValues u i k) (pointValues v i k) := by
  simp only [affineSubstitution, point, eval₂Hom_X', affineVector, pointValues]

private theorem substitution_product_point (p u v : Fin 1053 → R) (h : R)
    (i j : Fin 39) (k : Fin 27) :
    affineSubstitution p u v (coordinateProduct (C h) (point i) (point j) k) =
      coordinateProduct (C h)
        (affineVector (pointValues p i) (pointValues u i) (pointValues v i))
        (affineVector (pointValues p j) (pointValues u j) (pointValues v j)) k := by
  simp only [coordinateProduct_apply, map_sum, map_mul, map_intCast,
    affineSubstitution, eval₂Hom_C, point, eval₂Hom_X', affineVector, pointValues]

private theorem substitution_pairing_point (p u v : Fin 1053 → R) (i j : Fin 39) :
    affineSubstitution p u v (coordinatePairing (point i) (point j)) =
      coordinatePairing
        (affineVector (pointValues p i) (pointValues u i) (pointValues v i))
        (affineVector (pointValues p j) (pointValues u j) (pointValues v j)) := by
  simp only [coordinatePairing, map_sum, map_mul, map_intCast,
    substitution_point, affineVector]

private theorem substitution_unit (p u v : Fin 1053 → R) (k : Fin 27) :
    affineSubstitution p u v (coordinateUnit k) = C (coordinateUnit (P := R) k) := by
  unfold coordinateUnit
  split_ifs <;> simp only [map_one, map_zero]

/-- The idempotency subtraction contributes minus the actual tangent. -/
theorem gId_first_coeff (h t : R) (p u v : Fin 1053 → R) (i : Fin 39) (k : Fin 27) :
    (affineSubstitution p u v (gRow h t (gNumber (gId i k)))).coeff firstExponent =
      2 * coordinateProduct h (pointValues p i) (pointValues u i) k - pointValues u i k := by
  rw [gRow_id]
  simp only [FrameResiduals.idempotencyResidual, Pi.sub_apply]
  rw [map_sub, first_coeff_sub, substitution_product_point, substitution_point,
    coordinateProduct_first_coeff, affineTwo_first_coeff]
  rw [coordinateProduct_comm h (pointValues u i) (pointValues p i), ← two_mul]

/-- Both original product orders occur in every within-frame row. -/
theorem gWithin_first_coeff (h t : R) (p u v : Fin 1053 → R)
    (f : Fin 13) (s : Fin 3) (k : Fin 27) :
    (affineSubstitution p u v (gRow h t (gNumber (gWithin f s k)))).coeff firstExponent =
      firstResidual h p u (gWithin f s k) := by
  rw [gRow_within, substitution_product_point, coordinateProduct_first_coeff]
  simp only [gWithin, firstResidual, mixedResidual, linearResidual, add_zero]

/-- Frame sums contribute their full tangent sum to the first coefficient. -/
theorem gSum_first_coeff (h t : R) (p u v : Fin 1053 → R) (f : Fin 13) (k : Fin 27) :
    (affineSubstitution p u v (gRow h t (gNumber (gSum f k)))).coeff firstExponent =
      firstResidual h p u (gSum f k) := by
  rw [gRow_sum, map_sub, first_coeff_sub]
  simp only [map_sum, coeff_sum, substitution_point, affineTwo_first_coeff,
    substitution_unit, first_coeff_const, sub_zero,
    gSum, firstResidual, mixedResidual, linearResidual, zero_add]

/-- The overlap constant has zero first coefficient; both pairings remain. -/
theorem gCross_first_coeff (h t : R) (p u v : Fin 1053 → R)
    (fg : Pair 13) (a b : Fin 3) :
    (affineSubstitution p u v (gRow h t (gNumber (gCross fg a b)))).coeff firstExponent =
      firstResidual h p u (gCross fg a b) := by
  have hConst : affineSubstitution p u v (C t) = C t := eval₂Hom_C _ _ _
  rw [gRow_cross, map_sub, first_coeff_sub, substitution_pairing_point,
    coordinatePairing_first_coeff, hConst, first_coeff_const, sub_zero]
  simp only [gCross, firstResidual, mixedResidual, linearResidual, add_zero]

private theorem gLabel_first_coeff (h t : R) (p u v : Fin 1053 → R) (q : GLabel) :
    (affineSubstitution p u v (gRow h t (gNumber q))).coeff firstExponent =
      firstResidual h p u q := by
  rcases q with ⟨i, k⟩ | ⟨⟨f, s⟩, k⟩ | ⟨f, k⟩ | ⟨fg, a, b⟩
  · simpa only [gId, firstResidual, mixedResidual, linearResidual, sub_eq_add_neg] using
      (gId_first_coeff h t p u v i k)
  · exact gWithin_first_coeff h t p u v f s k
  · exact gSum_first_coeff h t p u v f k
  · exact gCross_first_coeff h t p u v fg a b

/-- Every actual numbered row has its derived first directional contraction. -/
theorem gRow_first_coeff (h t : R) (p u v : Fin 1053 → R) (r : Fin 3159) :
    (affineSubstitution p u v (gRow h t r)).coeff firstExponent = firstRow h p u r := by
  unfold firstRow
  simpa only [gNumber.apply_symm_apply] using
    (gLabel_first_coeff h t p u v (gNumber.symm r))

/-- No omitted weight, row or original linear term enters this coefficient. -/
theorem weighted_gRow_first_coeff (h t : R) (p u v : Fin 1053 → R)
    (weights : Fin 3159 → R) :
    (∑ r : Fin 3159, weights r • affineSubstitution p u v (gRow h t r)).coeff
        firstExponent = ∑ r : Fin 3159, weights r * firstRow h p u r := by
  simp only [coeff_sum, coeff_smul, gRow_first_coeff, smul_eq_mul]

end NativePolynomial.ConfigurationResiduals.FirstCoefficients

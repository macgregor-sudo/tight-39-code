module

public import NativeConfigurationPolynomialResiduals
public import AffineMixedMonomialCoefficient

@[expose] public section

/-!
# Mixed coefficients of the actual numbered G residuals

The same affine substitution is applied to the original point-first
variables. Bilinearity reduces the mixed coefficient of each actual row
to two finite coordinate contractions; linear and constant terms vanish.
The final formula retains every entry of an arbitrary full row weight.
It makes no numerical certificate or point-solution assertion.

This first-party proof applies the existing native coordinate product,
numbered residuals and scalar monomial coefficient identity. No algebra
carrier or residual model is copied or replaced, and no novelty is claimed.
Mathlib APIs are pinned at065356127b1dc0016f66b7283ce0ce2c4055aa55.
The imported native source retains commit
40d3b344180d9ddb78aaa2876873377c1e631515 from
https://github.com/macgregor-sudo/compact-albert-recognition, with existing
Apache-2.0 notices/provenance in THIRD_PARTY_NOTICES.md#native-albert-code.
Thanks to the native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace NativePolynomial.ConfigurationResiduals.MixedCoefficients

open scoped BigOperators
open MvPolynomial CoordinateMaps ConfigurationResidualIndices
open PolynomialJets.AffineMixedCoefficients

variable {R : Type*} [CommRing R]

/-- Apply the checked scalar affine expression coordinate by coordinate. -/
def affineVector {α : Type*} (p u v : α → R) : α → MvPolynomial (Fin 2) R :=
  fun k => affineTwo (p k) (u k) (v k)

/-- Project an ambient value array using the original point-first index. -/
def pointValues (w : Fin 1053 → R) (i : Fin 39) : Fin 27 → R :=
  fun k => w (variableIndex i k)

/-- Substitute the same affine two-plane in the actual original variables. -/
def affineSubstitution (p u v : Fin 1053 → R) :
    MvPolynomial (Fin 1053) R →+* MvPolynomial (Fin 2) R :=
  eval₂Hom C (affineVector p u v)

/-- The finite contractions in the actual G typed row order. -/
def mixedResidual (h : R) (u v : Fin 1053 → R) : GLabel → R
  | .inl (i, k) => 2 * coordinateProduct h (pointValues u i) (pointValues v i) k
  | .inr (.inl ((f, s), k)) =>
      coordinateProduct h
        (pointValues u (framePointIndex f (withinPair s).val.1))
        (pointValues v (framePointIndex f (withinPair s).val.2)) k +
      coordinateProduct h
        (pointValues v (framePointIndex f (withinPair s).val.1))
        (pointValues u (framePointIndex f (withinPair s).val.2)) k
  | .inr (.inr (.inl _)) => 0
  | .inr (.inr (.inr (fg, (a, b)))) =>
      coordinatePairing (pointValues u (framePointIndex fg.val.1 a))
        (pointValues v (framePointIndex fg.val.2 b)) +
      coordinatePairing (pointValues v (framePointIndex fg.val.1 a))
        (pointValues u (framePointIndex fg.val.2 b))

/-- Number only through the existing canonical G equivalence. -/
def mixedRow (h : R) (u v : Fin 1053 → R) (r : Fin 3159) : R :=
  mixedResidual h u v (gNumber.symm r)

private theorem mixed_coeff_sub (p q : MvPolynomial (Fin 2) R) :
    (p - q).coeff mixedExponent = p.coeff mixedExponent - q.coeff mixedExponent :=
  map_sub (lcoeff R mixedExponent) p q

private theorem mixed_coeff_const (a : R) :
    (C a : MvPolynomial (Fin 2) R).coeff mixedExponent = 0 := by
  have hNonzero : mixedExponent ≠ 0 := by
    intro hEq
    have hAt := congrArg (fun d : Fin 2 →₀ ℕ => d (0 : Fin 2)) hEq
    simp [mixedExponent] at hAt
  exact coeff_C_of_ne_zero hNonzero a

private theorem mixed_coeff_affine (a b c : R) :
    (affineTwo a b c).coeff mixedExponent = 0 := by
  have hOne : affineTwo (1 : R) 0 0 = (1 : MvPolynomial (Fin 2) R) := by
    simp only [affineTwo, map_one, map_zero, zero_mul, add_zero]
  simpa only [hOne, mul_one, mul_zero, add_zero] using
    (affineTwo_mul_mixed_coeff a b c (1 : R) 0 0)

private theorem mixed_coeff_mul_C (p : MvPolynomial (Fin 2) R) (a : R) :
    (p * C a).coeff mixedExponent = p.coeff mixedExponent * a := by
  rw [mul_comm, coeff_C_mul, mul_comm]

/-- The unchanged finite tensor gives the two actual product contractions. -/
theorem coordinateProduct_mixed_coeff (h : R) (p u v q s t : Fin 27 → R) (k : Fin 27) :
    (coordinateProduct (C h) (affineVector p u v) (affineVector q s t) k).coeff
        mixedExponent =
      coordinateProduct h u t k + coordinateProduct h v s k := by
  rw [coordinateProduct_polynomial_apply]
  simp only [tensorPolynomial, coeff_sum, mixed_coeff_mul_C, affineVector,
    affineTwo_mul_mixed_coeff, coordinateProduct_apply, add_mul, Finset.sum_add_distrib]

/-- The same integer diagonal/upper weights are retained in the pairing. -/
theorem coordinatePairing_mixed_coeff (p u v q s t : Fin 27 → R) :
    (coordinatePairing (affineVector p u v) (affineVector q s t)).coeff mixedExponent =
      coordinatePairing u t + coordinatePairing v s := by
  have hForm : coordinatePairing (affineVector p u v) (affineVector q s t) =
      ∑ k : Fin 27, C (IntegralStructureConstants.coordinateTraceWeight k : R) *
        (affineTwo (p k) (u k) (v k) * affineTwo (q k) (s k) (t k)) := by
    unfold coordinatePairing affineVector
    apply Finset.sum_congr rfl
    intro k _
    rw [map_intCast, mul_assoc]
  rw [hForm]
  simp only [coeff_sum, coeff_C_mul, affineTwo_mul_mixed_coeff]
  simp only [coordinatePairing, mul_add, ← mul_assoc, Finset.sum_add_distrib]

private theorem substitution_point (p u v : Fin 1053 → R) (i : Fin 39) (k : Fin 27) :
    affineSubstitution p u v (point i k) =
      affineTwo (pointValues p i k) (pointValues u i k) (pointValues v i k) := by
  simp only [affineSubstitution, point, eval₂Hom_X', affineVector, pointValues]

private theorem substitution_point_vector (p u v : Fin 1053 → R) (i : Fin 39) :
    (fun k => affineSubstitution p u v (point i k)) =
      affineVector (pointValues p i) (pointValues u i) (pointValues v i) := by
  funext k
  exact substitution_point p u v i k

private theorem substitution_product (p u v : Fin 1053 → R) (h : R)
    (x y : Fin 27 → MvPolynomial (Fin 1053) R) (k : Fin 27) :
    affineSubstitution p u v (coordinateProduct (C h) x y k) =
      coordinateProduct (C h) (fun j => affineSubstitution p u v (x j))
        (fun j => affineSubstitution p u v (y j)) k := by
  simp only [coordinateProduct_apply, map_sum, map_mul, map_intCast,
    affineSubstitution, eval₂Hom_C]

private theorem substitution_pairing (p u v : Fin 1053 → R)
    (x y : Fin 27 → MvPolynomial (Fin 1053) R) :
    affineSubstitution p u v (coordinatePairing x y) =
      coordinatePairing (fun j => affineSubstitution p u v (x j))
        (fun j => affineSubstitution p u v (y j)) := by
  simp only [coordinatePairing, map_sum, map_mul, map_intCast]

private theorem substitution_product_point (p u v : Fin 1053 → R) (h : R)
    (i j : Fin 39) (k : Fin 27) :
    affineSubstitution p u v (coordinateProduct (C h) (point i) (point j) k) =
      coordinateProduct (C h)
        (affineVector (pointValues p i) (pointValues u i) (pointValues v i))
        (affineVector (pointValues p j) (pointValues u j) (pointValues v j)) k := by
  simp only [substitution_product, substitution_point_vector]

private theorem substitution_pairing_point (p u v : Fin 1053 → R) (i j : Fin 39) :
    affineSubstitution p u v (coordinatePairing (point i) (point j)) =
      coordinatePairing
        (affineVector (pointValues p i) (pointValues u i) (pointValues v i))
        (affineVector (pointValues p j) (pointValues u j) (pointValues v j)) := by
  simp only [substitution_pairing, substitution_point_vector]

private theorem substitution_unit (p u v : Fin 1053 → R) (k : Fin 27) :
    affineSubstitution p u v (coordinateUnit k) = C (coordinateUnit (P := R) k) := by
  unfold coordinateUnit
  split_ifs <;> simp only [map_one, map_zero]

/-- The linear subtraction contributes no mixed coefficient to idempotency. -/
theorem gId_mixed_coeff (h t : R) (p u v : Fin 1053 → R) (i : Fin 39) (k : Fin 27) :
    (affineSubstitution p u v (gRow h t (gNumber (gId i k)))).coeff mixedExponent =
      2 * coordinateProduct h (pointValues u i) (pointValues v i) k := by
  rw [gRow_id]
  simp only [FrameResiduals.idempotencyResidual, Pi.sub_apply]
  rw [map_sub, mixed_coeff_sub, substitution_product_point, substitution_point,
    coordinateProduct_mixed_coeff, mixed_coeff_affine, sub_zero]
  rw [coordinateProduct_comm h (pointValues v i) (pointValues u i), ← two_mul]

/-- Both input orders of the actual within-frame product are present. -/
theorem gWithin_mixed_coeff (h t : R) (p u v : Fin 1053 → R)
    (f : Fin 13) (s : Fin 3) (k : Fin 27) :
    (affineSubstitution p u v (gRow h t (gNumber (gWithin f s k)))).coeff mixedExponent =
      mixedResidual h u v (gWithin f s k) := by
  rw [gRow_within, substitution_product_point, coordinateProduct_mixed_coeff]
  rfl

/-- Actual frame sums and their constant unit have mixed coefficient zero. -/
theorem gSum_mixed_coeff (h t : R) (p u v : Fin 1053 → R) (f : Fin 13) (k : Fin 27) :
    (affineSubstitution p u v (gRow h t (gNumber (gSum f k)))).coeff mixedExponent = 0 := by
  rw [gRow_sum, map_sub, mixed_coeff_sub]
  simp only [map_sum, coeff_sum, substitution_point, mixed_coeff_affine,
    Finset.sum_const_zero, substitution_unit, mixed_coeff_const, sub_zero]

/-- The overlap constant is irrelevant to the actual cross mixed coefficient. -/
theorem gCross_mixed_coeff (h t : R) (p u v : Fin 1053 → R)
    (fg : Pair 13) (a b : Fin 3) :
    (affineSubstitution p u v (gRow h t (gNumber (gCross fg a b)))).coeff mixedExponent =
      mixedResidual h u v (gCross fg a b) := by
  have hConst : affineSubstitution p u v (C t) = C t := eval₂Hom_C _ _ _
  rw [gRow_cross, map_sub, mixed_coeff_sub, substitution_pairing_point,
    coordinatePairing_mixed_coeff, hConst, mixed_coeff_const, sub_zero]
  rfl

private theorem gLabel_mixed_coeff (h t : R) (p u v : Fin 1053 → R) (q : GLabel) :
    (affineSubstitution p u v (gRow h t (gNumber q))).coeff mixedExponent =
      mixedResidual h u v q := by
  rcases q with ⟨i, k⟩ | ⟨⟨f, s⟩, k⟩ | ⟨f, k⟩ | ⟨fg, a, b⟩
  · exact gId_mixed_coeff h t p u v i k
  · exact gWithin_mixed_coeff h t p u v f s k
  · exact gSum_mixed_coeff h t p u v f k
  · exact gCross_mixed_coeff h t p u v fg a b

/-- Every numbered original G row has its derived finite mixed contraction. -/
theorem gRow_mixed_coeff (h t : R) (p u v : Fin 1053 → R) (r : Fin 3159) :
    (affineSubstitution p u v (gRow h t r)).coeff mixedExponent = mixedRow h u v r := by
  unfold mixedRow
  simpa only [gNumber.apply_symm_apply] using
    (gLabel_mixed_coeff h t p u v (gNumber.symm r))

/-- The coefficient uses the entire arbitrary row weight, in canonical order. -/
theorem weighted_gRow_mixed_coeff (h t : R) (p u v : Fin 1053 → R)
    (weights : Fin 3159 → R) :
    (∑ r : Fin 3159, weights r • affineSubstitution p u v (gRow h t r)).coeff
        mixedExponent =
      ∑ r : Fin 3159, weights r * mixedRow h u v r := by
  simp only [coeff_sum, coeff_smul, gRow_mixed_coeff, smul_eq_mul]

end NativePolynomial.ConfigurationResiduals.MixedCoefficients


#check @NativePolynomial.ConfigurationResiduals.MixedCoefficients.coordinateProduct_mixed_coeff
#check @NativePolynomial.ConfigurationResiduals.MixedCoefficients.coordinatePairing_mixed_coeff
#check @NativePolynomial.ConfigurationResiduals.MixedCoefficients.gId_mixed_coeff
#check @NativePolynomial.ConfigurationResiduals.MixedCoefficients.gWithin_mixed_coeff
#check @NativePolynomial.ConfigurationResiduals.MixedCoefficients.gSum_mixed_coeff
#check @NativePolynomial.ConfigurationResiduals.MixedCoefficients.gCross_mixed_coeff
#check @NativePolynomial.ConfigurationResiduals.MixedCoefficients.gRow_mixed_coeff
#check @NativePolynomial.ConfigurationResiduals.MixedCoefficients.weighted_gRow_mixed_coeff
#print axioms NativePolynomial.ConfigurationResiduals.MixedCoefficients.coordinateProduct_mixed_coeff
#print axioms NativePolynomial.ConfigurationResiduals.MixedCoefficients.coordinatePairing_mixed_coeff
#print axioms NativePolynomial.ConfigurationResiduals.MixedCoefficients.gId_mixed_coeff
#print axioms NativePolynomial.ConfigurationResiduals.MixedCoefficients.gWithin_mixed_coeff
#print axioms NativePolynomial.ConfigurationResiduals.MixedCoefficients.gSum_mixed_coeff
#print axioms NativePolynomial.ConfigurationResiduals.MixedCoefficients.gCross_mixed_coeff
#print axioms NativePolynomial.ConfigurationResiduals.MixedCoefficients.gRow_mixed_coeff
#print axioms NativePolynomial.ConfigurationResiduals.MixedCoefficients.weighted_gRow_mixed_coeff

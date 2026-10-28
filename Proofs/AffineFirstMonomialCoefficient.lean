module

public import AffineMixedMonomialCoefficient

@[expose] public section

/-!
# Actual first coefficients of the existing affine two-variable input

The scalar product rule is proved by finite monomial expansion. It retains
the base point and both product orders. This is a first-party elementary
proof, with no numerical data or novelty claim. The existing affineTwo
definition and mathlib monomial API are imported rather than redefined.
Mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55; Lean4.35.0-rc2. Retained
Apache-2.0 provenance is in ../THIRD_PARTY_NOTICES.md#native-albert-code and imports.
Thanks to the Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke,1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace PolynomialJets.AffineMixedCoefficients

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- The first directional variable is z0, with no power of z1. -/
def firstExponent : Fin 2 →₀ ℕ := Finsupp.single 0 1

theorem firstExponent_ne_zero : firstExponent ≠ 0 := by
  intro hEq
  have hAt := congrArg (fun d : Fin 2 →₀ ℕ => d (0 : Fin 2)) hEq
  simp [firstExponent] at hAt

/-- The actual coefficient of z0 in an affine product is a*e+b*d. -/
theorem affineTwo_mul_first_coeff (a b c d e f : R) :
    ((affineTwo a b c) * (affineTwo d e f)).coeff firstExponent =
      a * e + b * d := by
  classical
  let u : Fin 2 →₀ ℕ := Finsupp.single 0 1
  let v : Fin 2 →₀ ℕ := Finsupp.single 1 1
  have hZero : (0 : Fin 2 →₀ ℕ) ≠ u := by
    intro hEq
    have hAt := congrArg (fun d : Fin 2 →₀ ℕ => d (0 : Fin 2)) hEq
    simp [u] at hAt
  have hV : v ≠ u := by
    intro hEq
    have hAt := congrArg (fun d : Fin 2 →₀ ℕ => d (0 : Fin 2)) hEq
    simp [u, v] at hAt
  have hUU : u + u ≠ u := by
    intro hEq
    have hAt := congrArg (fun d : Fin 2 →₀ ℕ => d (0 : Fin 2)) hEq
    simp [u] at hAt
  have hUV : u + v ≠ u := by
    intro hEq
    have hAt := congrArg (fun d : Fin 2 →₀ ℕ => d (1 : Fin 2)) hEq
    simp [u, v] at hAt
  have hVV : v + v ≠ u := by
    intro hEq
    have hAt := congrArg (fun d : Fin 2 →₀ ℕ => d (0 : Fin 2)) hEq
    simp [u, v] at hAt
  have hAffine (a b c : R) : affineTwo a b c =
      monomial 0 a + monomial u b + monomial v c := by
    unfold affineTwo
    rw [C_mul_X_eq_monomial, C_mul_X_eq_monomial, C_apply]
  have hCoeffAdd (p q : MvPolynomial (Fin 2) R) :
      (p + q).coeff u = p.coeff u + q.coeff u := map_add (lcoeff R u) p q
  change ((affineTwo a b c) * (affineTwo d e f)).coeff u = _
  rw [hAffine, hAffine]
  simp only [add_mul, mul_add, monomial_mul_monomial, zero_add, add_zero]
  simp only [hCoeffAdd, coeff_monomial]
  simp [hZero, hV, hUU, hUV, hVV, add_comm v u]
  exact add_comm (b * d) (a * e)

theorem affineTwo_first_coeff (a b c : R) :
    (affineTwo a b c).coeff firstExponent = b := by
  have hOne : affineTwo (1 : R) 0 0 = (1 : MvPolynomial (Fin 2) R) := by
    simp only [affineTwo, map_one, map_zero, zero_mul, add_zero]
  simpa only [hOne, mul_one, mul_zero, zero_add] using
    (affineTwo_mul_first_coeff a b c (1 : R) 0 0)

theorem first_coeff_const (a : R) :
    (C a : MvPolynomial (Fin 2) R).coeff firstExponent = 0 :=
  coeff_C_of_ne_zero firstExponent_ne_zero a

end PolynomialJets.AffineMixedCoefficients

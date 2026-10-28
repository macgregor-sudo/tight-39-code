module

public import Mathlib.Algebra.MvPolynomial.Basic

@[expose] public section

/-!
# A mixed coefficient through explicit monomial products

Affine inputs are converted to three monomials before multiplication.
Nine distributive products then have known exponents; the coefficient map
only sees addition and single monomials. No convolution enumeration is used.
This is the scalar step for the actual coordinate-product contractions,
not a native row or numerical certificate binding.

The proof script is first-party elementary polynomial arithmetic, with no
novelty claim. Mathlib at065356127b1dc0016f66b7283ce0ce2c4055aa55 supplies
Basic.lean's C_mul_X_eq_monomial, monomial_mul_monomial, lcoeff and
coeff_monomial. The Apache-2.0 implementation is imported, not copied.
Thanks to the Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace PolynomialJets.AffineMixedCoefficients

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- The exponent of the literal mixed monomial z0*z1. -/
def mixedExponent : Fin 2 →₀ ℕ :=
  Finsupp.single 0 1 + Finsupp.single 1 1

/-- A scalar affine input with two independent polynomial variables. -/
def affineTwo (a b c : R) : MvPolynomial (Fin 2) R :=
  C a + C b * X 0 + C c * X 1

/-- Scalar bilinearity contributes b*f+c*e to the mixed coefficient. -/
theorem affineTwo_mul_mixed_coeff (a b c d e f : R) :
    ((affineTwo a b c) * (affineTwo d e f)).coeff mixedExponent =
      b * f + c * e := by
  classical
  let u : Fin 2 →₀ ℕ := Finsupp.single 0 1
  let v : Fin 2 →₀ ℕ := Finsupp.single 1 1
  have hZero : (0 : Fin 2 →₀ ℕ) ≠ u + v := by
    intro hEq
    have hAt := congrArg (fun d : Fin 2 →₀ ℕ => d (0 : Fin 2)) hEq
    simp [u, v] at hAt
  have hU : u ≠ u + v := by
    intro hEq
    have hAt := congrArg (fun d : Fin 2 →₀ ℕ => d (1 : Fin 2)) hEq
    simp [u, v] at hAt
  have hV : v ≠ u + v := by
    intro hEq
    have hAt := congrArg (fun d : Fin 2 →₀ ℕ => d (0 : Fin 2)) hEq
    simp [u, v] at hAt
  have hUU : u + u ≠ u + v := by
    intro hEq
    have hAt := congrArg (fun d : Fin 2 →₀ ℕ => d (1 : Fin 2)) hEq
    simp [u, v] at hAt
  have hVV : v + v ≠ u + v := by
    intro hEq
    have hAt := congrArg (fun d : Fin 2 →₀ ℕ => d (0 : Fin 2)) hEq
    simp [u, v] at hAt
  have hAffine (a b c : R) : affineTwo a b c =
      monomial 0 a + monomial u b + monomial v c := by
    unfold affineTwo
    rw [C_mul_X_eq_monomial, C_mul_X_eq_monomial, C_apply]
  have hCoeffAdd (p q : MvPolynomial (Fin 2) R) :
      (p + q).coeff (u+v) = p.coeff (u+v) + q.coeff (u+v) :=
    map_add (lcoeff R (u+v)) p q
  change ((affineTwo a b c) * (affineTwo d e f)).coeff (u+v) = _
  rw [hAffine, hAffine]
  simp only [add_mul, mul_add, monomial_mul_monomial, zero_add, add_zero]
  simp only [hCoeffAdd, coeff_monomial]
  simp [hZero, hU, hV, hUU, hVV, add_comm v u]
  exact add_comm (c * e) (b * f)

end PolynomialJets.AffineMixedCoefficients


#check @PolynomialJets.AffineMixedCoefficients.affineTwo_mul_mixed_coeff
#print axioms PolynomialJets.AffineMixedCoefficients.affineTwo_mul_mixed_coeff

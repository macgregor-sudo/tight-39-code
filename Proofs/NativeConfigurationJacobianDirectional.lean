module

public import NativeConfigurationFirstCoefficients
public import CenteredFirstCoefficient

@[expose] public section

/-!
# The actual centered linear matrix acts by the derived first-row formula

The matrix entries are exactly the existing equationLinearMatrix applied
to the existing translate of each existing numbered gRow. The coefficient
composition theorem binds its tangent action to firstRow and binds the
weighted coefficient to the full annihilator action. There is no supplied
Jacobian table, sparse support or numerical vanishing hypothesis.

First-party composition of imported coefficient and finite-sum identities;
no novelty claim and no copied upstream proof body. Lean4.35.0-rc2 and
mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55, with retained native and
Apache-2.0 provenance in ../THIRD_PARTY_NOTICES.md#native-albert-code and imports.
Thanks to the native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke,1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace NativePolynomial.ConfigurationResiduals.FirstCoefficients

open scoped BigOperators
open PolynomialJets PolynomialJets.AffineMixedCoefficients
open NativePolynomial.ConfigurationResiduals.MixedCoefficients

variable {R : Type*} [CommRing R]

/-- This is the actual centered coefficient matrix, with all1053 columns. -/
theorem actual_linearMatrix_action (h t : R) (p u : Fin 1053 → R) (r : Fin 3159) :
    (∑ k : Fin 1053,
      equationLinearMatrix (fun s : Fin 3159 => translate p (gRow h t s)) r k * u k) =
      firstRow h p u r := by
  change (∑ k : Fin 1053, (translate p (gRow h t r)).coeff (Finsupp.single k 1) * u k) = _
  rw [← first_coeff_affine_eq_centered_linear p u (0 : Fin 1053 → R) (gRow h t r)]
  exact gRow_first_coeff h t p u (0 : Fin 1053 → R) r

/-- The same weighted actual coefficient is the action of all annihilator columns. -/
theorem weighted_first_coeff_eq_annihilator_action (h t : R) (p u v : Fin 1053 → R)
    (weights : Fin 3159 → R) :
    (∑ r : Fin 3159, weights r • affineSubstitution p u v (gRow h t r)).coeff
        firstExponent =
      ∑ k : Fin 1053,
        (∑ r : Fin 3159, weights r *
          equationLinearMatrix (fun s : Fin 3159 => translate p (gRow h t s)) r k) * u k := by
  rw [weighted_gRow_first_coeff]
  simp_rw [← actual_linearMatrix_action h t p u]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

end NativePolynomial.ConfigurationResiduals.FirstCoefficients

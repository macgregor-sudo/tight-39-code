module

public import AffineFirstMonomialCoefficient
public import PolynomialJetPrerequisitesModule

@[expose] public section

/-!
# First affine coefficients from the actual centered linear matrix

This generic coefficient identity uses ordinary polynomial substitution.
The first coefficient of a linear substitution receives contributions
only from the original degree-one monomials. Composing with translation
then binds the first affine coefficient to the centered linear matrix.
The existing PolynomialJets.translate is consumed unchanged; no second
centering operation is introduced.
No derivative table, degree bound, characteristic or vanishing hypothesis
is supplied. The polynomial and every coordinate remain explicit.

First-party elementary polynomial proof; no novelty claim. Imported
mathlib Basic/Eval APIs are Apache-2.0 at
065356127b1dc0016f66b7283ce0ce2c4055aa55, Lean4.35.0-rc2. Upstream
implementations are not copied. Thanks to the Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke,1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace PolynomialJets.AffineMixedCoefficients

open scoped BigOperators
open MvPolynomial

variable {R σ : Type*} [CommRing R]

private theorem coeff_add_apply (m : σ →₀ ℕ) (f g : MvPolynomial σ R) :
    (f + g).coeff m = f.coeff m + g.coeff m := map_add (lcoeff R m) f g

private theorem linear_substitution_constant (u v : σ → R) (f : MvPolynomial σ R) :
    (eval₂Hom C (fun k => affineTwo 0 (u k) (v k)) f).coeff 0 = f.coeff 0 := by
  have hHom : (constantCoeff : MvPolynomial (Fin 2) R →+* R).comp
      (eval₂Hom C (fun k => affineTwo 0 (u k) (v k))) = constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro k
      simp [affineTwo]
  simpa only [RingHom.comp_apply, constantCoeff_eq] using RingHom.congr_fun hHom f

private theorem coeff_mul_affine_zero (f : MvPolynomial (Fin 2) R) (a b : R) :
    (f * affineTwo 0 a b).coeff firstExponent = f.coeff 0 * a := by
  classical
  have hCoeffMulC (q : MvPolynomial (Fin 2) R) (r : R) (m : Fin 2 →₀ ℕ) :
      (q * C r).coeff m = q.coeff m * r := by
    rw [mul_comm, coeff_C_mul, mul_comm]
  simp only [affineTwo, map_zero, zero_add, mul_add, ← mul_assoc, coeff_add_apply]
  rw [coeff_mul_X', coeff_mul_X']
  simp [firstExponent, hCoeffMulC]

/-- All and only the original linear coefficients contribute after a linear substitution. -/
theorem first_coeff_linear_substitution [Fintype σ]
    (u v : σ → R) (f : MvPolynomial σ R) :
    (eval₂Hom C (fun k => affineTwo 0 (u k) (v k)) f).coeff firstExponent =
      ∑ k : σ, f.coeff (Finsupp.single k 1) * u k := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
      simp [firstExponent, eq_comm]
  | add f g hf hg =>
      simp only [map_add, coeff_add_apply, hf, hg, add_mul, Finset.sum_add_distrib]
  | mul_X f k _ =>
      rw [map_mul, eval₂Hom_X', coeff_mul_affine_zero, linear_substitution_constant]
      have hCoeff (j : σ) :
          (f * X k).coeff (Finsupp.single j 1) = if j = k then f.coeff 0 else 0 := by
        by_cases h : j = k
        · subst j
          simpa only [zero_add, ite_true] using
            (coeff_mul_X (0 : σ →₀ ℕ) k f)
        · rw [coeff_mul_X']
          simp [h, Ne.symm h]
      simp_rw [hCoeff]
      simp

/-- Composition with translation identifies the actual centered first coefficients. -/
theorem first_coeff_affine_eq_centered_linear [Fintype σ]
    (p u v : σ → R) (f : MvPolynomial σ R) :
    (eval₂Hom C (fun k => affineTwo (p k) (u k) (v k)) f).coeff firstExponent =
      ∑ k : σ, (PolynomialJets.translate p f).coeff (Finsupp.single k 1) * u k := by
  let τ : MvPolynomial σ R →+* MvPolynomial σ R :=
    eval₂Hom C (fun k => X k + C (p k))
  have hApply (q : MvPolynomial σ R) : τ q = PolynomialJets.translate p q := rfl
  have hCompose : (eval₂Hom C (fun k => affineTwo 0 (u k) (v k))).comp τ =
      eval₂Hom C (fun k => affineTwo (p k) (u k) (v k)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [τ]
    · intro k
      simp [τ, affineTwo, add_assoc, add_comm]
  rw [← RingHom.congr_fun hCompose f]
  change (eval₂Hom C (fun k => affineTwo 0 (u k) (v k)) (τ f)).coeff firstExponent = _
  rw [hApply]
  exact first_coeff_linear_substitution u v (PolynomialJets.translate p f)

end PolynomialJets.AffineMixedCoefficients

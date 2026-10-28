module

public import ConvergentGermPolynomialRepresentatives
public import PolynomialJetPrerequisitesModule

@[expose] public section

/-!
# Finite-dimensional analytic jets and transfer of polynomial upper bounds

Finite polynomial truncation presents the existing polynomial ideal quotient.
The canonical surjection to analytic jets therefore proves finite dimension
and transfers every polynomial upper bound for the same residual ideal.
Mathlib's restriction-of-scalars quotient equivalence identifies the existing
polynomial module presentation without changing any representative.

This is standard linear algebra, with no geometric dimension or full jet
equivalence claim. First-party proof scripts call imported APIs by name; no
upstream source body is copied. At mathlib commit
065356127b1dc0016f66b7283ce0ce2c4055aa55, Lean v4.35.0-rc2,
`Module.Finite.of_surjective` is in RingTheory/Finiteness/Basic.lean
(file-header author Johan Commelin), `LinearMap.finrank_le_finrank_of_surjective`
in LinearAlgebra/Dimension/StrongRankCondition.lean (Kim Morrison), and
`Submodule.Quotient.restrictScalarsEquiv` in LinearAlgebra/Quotient/Basic.lean
(Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov). Repository:
https://github.com/leanprover-community/mathlib4, Apache-2.0.
Thank you to these authors and the Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

noncomputable section

namespace ConvergentJetDimensionTransfer

open ConvergentResidualJets ConvergentGermPolynomialRepresentatives PolynomialJets

/-- Finite monomial coefficients map to the existing polynomial jet quotient. -/
def polynomialJetCoefficientMap {n : ℕ} (Q : Ideal (Poly n)) (N : ℕ) :
    (MonomialsUpTo (Fin n) N → ℂ) →ₗ[ℂ] (Poly n ⧸ polynomialJetIdeal Q N) :=
  (Ideal.Quotient.mkₐ ℂ (polynomialJetIdeal Q N)).toLinearMap.comp (monomialSection N)

theorem polynomialJetCoefficientMap_surjective {n : ℕ} (Q : Ideal (Poly n)) (N : ℕ) :
    Function.Surjective (polynomialJetCoefficientMap Q N) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨lowCoeff N p, ?_⟩
  change Ideal.Quotient.mk (polynomialJetIdeal Q N) (monomialSection N (lowCoeff N p)) =
    Ideal.Quotient.mk (polynomialJetIdeal Q N) p
  symm
  apply Ideal.Quotient.eq.mpr
  exact (show variableIdeal n ^ (N+1) ≤ polynomialJetIdeal Q N from le_sup_right)
    (truncation_difference_mem_variableIdeal_pow N p)

instance polynomialJet_finite {n : ℕ} (Q : Ideal (Poly n)) (N : ℕ) :
    Module.Finite ℂ (Poly n ⧸ polynomialJetIdeal Q N) :=
  Module.Finite.of_surjective (polynomialJetCoefficientMap Q N)
    (polynomialJetCoefficientMap_surjective Q N)

instance analyticJet_finite {n : ℕ} (Q : Ideal (Poly n)) (N : ℕ) :
    Module.Finite ℂ (GermRing n ⧸ analyticJetIdeal Q N) :=
  Module.Finite.of_surjective (jetMap Q N).toLinearMap (jetMap_surjective Q N)

/-- Analytic jet dimension is at most the dimension of the same polynomial jet. -/
theorem analyticJet_finrank_le {n : ℕ} (Q : Ideal (Poly n)) (N : ℕ) :
    Module.finrank ℂ (GermRing n ⧸ analyticJetIdeal Q N) ≤
      Module.finrank ℂ (Poly n ⧸ polynomialJetIdeal Q N) :=
  LinearMap.finrank_le_finrank_of_surjective
    (f := (jetMap Q N).toLinearMap) (jetMap_surjective Q N)

/-- The existing scalar-restricted equation jet gives the same upper bound. -/
theorem analyticJet_finrank_le_equationJet {n : ℕ} {ι : Type*}
    (g : ι → Poly n) (N : ℕ) :
    Module.finrank ℂ (GermRing n ⧸ analyticJetIdeal (Ideal.span (Set.range g)) N) ≤
      Module.finrank ℂ (Poly n ⧸ equationJetSubmodule g N) := by
  let e := Submodule.Quotient.restrictScalarsEquiv ℂ
    (polynomialJetIdeal (Ideal.span (Set.range g)) N)
  exact (analyticJet_finrank_le (Ideal.span (Set.range g)) N).trans_eq e.finrank_eq.symm

end ConvergentJetDimensionTransfer

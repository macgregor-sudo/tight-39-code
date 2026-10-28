module

/-
First-party composition and proof scripts; no upstream source body is copied
or adapted. The mathematics is standard: a surjective finite-dimensional
linear map decreases dimension, finite-filtration dimensions add, and the
proved right-exact cut recurrence sums by the binomial identity.
No novelty, concrete terminal-plane or configuration-dimension claim.

Import-only provenance at mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55,
Lean v4.35.0-rc2: Dimension/StrongRankCondition.lean supplies
LinearMap.finrank_le_finrank_of_surjective (file-header author Kim Morrison).
The actual ideal-member, filtered-layer, first-isomorphism, finite-module and
binomial-summation provenance remains in the unchanged passed predecessors.
Inspected upstream headers and root LICENSE specify Apache-2.0; no upstream
source is modified. Thank you to these authors and all Lean/mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

public import PolynomialJetFiltrationModule

@[expose] public section

/-!
# Sharp bounds for the actual polynomial jets from finite terminal inputs

The same actual g generates the ideal, its linear parts, annihilator quadrics,
covering degree relations and finite jets. Quadratic degree, zero constant
term and full coefficient-level annihilation are explicit primitive inputs.
The degree-two relation equality is still required; no restricted table or
unverified plane identification is substituted for it.

This closes a generic polynomial implication for every N. It does not prove
the native data hypotheses, a terminal plane, an analytic bridge or a geometric
dimension bound for the original configuration problem.
-/

namespace PolynomialJets

open MvPolynomial
open HilbertFunctions.JetBounds
open scoped BigOperators

noncomputable section

variable {σ ι ε κ K : Type*} [Field K] [Finite σ] [Fintype ι]

/-- Genuine primitive polynomial identities give a surjection from the actual
uncut covering quotient to the actual degree layer, hence this inequality. -/
theorem equationDegreeLayer_finrank_le_relations
    (g : ι → MvPolynomial σ K) (E : ε → ι) (weights : κ → ι → K) (d : ℕ)
    (hQuadratic : ∀ i, (g i).totalDegree ≤ 2) (hConstant : ∀ i, (g i).coeff 0 = 0)
    (hAnnihilates : ∀ s j, ∑ i, weights s i * equationLinearMatrix g i j = 0) :
    Module.finrank K (equationDegreeLayer g d) ≤
      Module.finrank K (equationCutPiece g E weights [] d) := by
  let f : equationCutPiece g E weights [] d →ₗ[K] equationDegreeLayer g d :=
    factoredHomogeneousToEquationLayer g E weights d hQuadratic hConstant hAnnihilates
  have hf : Function.Surjective f :=
    factoredHomogeneousToEquationLayer_surjective g E weights d
      hQuadratic hConstant hAnnihilates
  exact LinearMap.finrank_le_finrank_of_surjective hf

/-- The actual finite-jet dimension is bounded by the cumulative dimensions
of the actual uncut relation quotients. All ideal provenance is derived by
the preceding passed factor maps and actual filtration equality. -/
theorem equationJet_finrank_le_cumulative_relations
    (g : ι → MvPolynomial σ K) (E : ε → ι) (weights : κ → ι → K) (N : ℕ)
    (hQuadratic : ∀ i, (g i).totalDegree ≤ 2) (hConstant : ∀ i, (g i).coeff 0 = 0)
    (hAnnihilates : ∀ s j, ∑ i, weights s i * equationLinearMatrix g i j = 0) :
    Module.finrank K (equationJet g N) ≤
      cumulative (fun d => Module.finrank K (equationCutPiece g E weights [] d)) N := by
  rw [equationJet_finrank_eq_sum_layers]
  change (∑ d ∈ Finset.range (N+1), Module.finrank K (equationDegreeLayer g d)) ≤
    ∑ d ∈ Finset.range (N+1), Module.finrank K (equationCutPiece g E weights [] d)
  exact Finset.sum_le_sum fun d _ =>
    equationDegreeLayer_finrank_le_relations g E weights d hQuadratic hConstant hAnnihilates

/-- Exact sharp bound for the actual polynomial-ideal jets, conditional on
explicit primitive equation identities and finite terminal h0/h1/h2 inputs.
The infinite homogeneous tail is derived from actual degree-two fullness. -/
theorem equationJet_finrank_sharp_bound_of_degree_two
    (g : ι → MvPolynomial σ K) (E : ε → ι) (weights : κ → ι → K)
    (cuts : List (homogeneousSubmodule σ K 1)) (u N : ℕ)
    (hQuadratic : ∀ i, (g i).totalDegree ≤ 2) (hConstant : ∀ i, (g i).coeff 0 = 0)
    (hAnnihilates : ∀ s j, ∑ i, weights s i * equationLinearMatrix g i j = 0)
    (hTerminalZero : Module.finrank K (equationCutPiece g E weights cuts 0) ≤ 1)
    (hTerminalOne : Module.finrank K (equationCutPiece g E weights cuts 1) ≤ u)
    (hTerminalTwo : equationIteratedCutRelations g E weights cuts 2 = ⊤) :
    Module.finrank K (equationJet g N) ≤
      (N+cuts.length).choose cuts.length +
        (if N=0 then 0 else u * (N+cuts.length-1).choose cuts.length) :=
  (equationJet_finrank_le_cumulative_relations g E weights N
    hQuadratic hConstant hAnnihilates).trans
    (equation_relation_cumulative_sharp_bound_of_degree_two g E weights cuts u N
      hTerminalZero hTerminalOne hTerminalTwo)

end
end PolynomialJets

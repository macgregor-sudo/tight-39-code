module

public import ConvergentGermAmbientJets
public import ConvergentGermPolynomialRepresentatives

@[expose] public section

/-!
# The canonical ambient finite-jet equivalence

First-party composition, 2026-10-23. No outgoing project license is selected.
The kernel theorem is proved from actual germ derivatives in the imported module;
surjectivity is the accepted Hadamard proof. This file keeps the original quotient
definitions and exposes the existing jet map as an equivalence. No additional
analytic, Noetherian, branch-existence or Taylor-equivalence premise is introduced.
-/

noncomputable section

namespace ConvergentGermAmbientJetEquiv

open ConvergentResidualJets ConvergentGermAmbientJets
open ConvergentGermPolynomialRepresentatives

theorem ker_representativeMap_bot (n N : ℕ) :
    RingHom.ker (representativeMap (⊥ : Ideal (Poly n)) N).toRingHom =
      variableIdeal n ^ (N + 1) := by
  ext p
  change Ideal.Quotient.mk (analyticJetIdeal (⊥ : Ideal (Poly n)) N)
    (polynomialGerm n p) = 0 ↔ p ∈ variableIdeal n ^ (N + 1)
  rw [Ideal.Quotient.eq_zero_iff_mem]
  simp only [analyticJetIdeal, Ideal.map_bot, bot_sup_eq]
  exact polynomialGerm_mem_vanishingIdeal_pow_iff p (N + 1)

theorem jetMap_bot_injective (n N : ℕ) :
    Function.Injective (jetMap (⊥ : Ideal (Poly n)) N) := by
  intro x y hxy
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [jetMap_mk, jetMap_mk, Ideal.Quotient.eq] at hxy
  have hm : polynomialGerm n (p - q) ∈ vanishingIdeal n ^ (N + 1) := by
    simpa only [map_sub, analyticJetIdeal, Ideal.map_bot, bot_sup_eq] using hxy
  apply Ideal.Quotient.eq.mpr
  simpa only [polynomialJetIdeal, bot_sup_eq] using
    (polynomialGerm_mem_vanishingIdeal_pow_iff (p - q) (N + 1)).mp hm

/-- The equivalence is the existing canonical jet map, not a chosen isomorphism
of spaces of the same dimension. -/
def ambientJetEquiv (n N : ℕ) :
    (Poly n ⧸ polynomialJetIdeal (⊥ : Ideal (Poly n)) N) ≃ₐ[ℂ]
      (GermRing n ⧸ analyticJetIdeal (⊥ : Ideal (Poly n)) N) :=
  AlgEquiv.ofBijective (jetMap (⊥ : Ideal (Poly n)) N)
    ⟨jetMap_bot_injective n N, jetMap_surjective _ _⟩

theorem ambientJetEquiv_mk (n N : ℕ) (p : Poly n) :
    ambientJetEquiv n N (Ideal.Quotient.mk (polynomialJetIdeal (⊥ : Ideal (Poly n)) N) p) =
      Ideal.Quotient.mk (analyticJetIdeal (⊥ : Ideal (Poly n)) N) (polynomialGerm n p) := rfl

end ConvergentGermAmbientJetEquiv

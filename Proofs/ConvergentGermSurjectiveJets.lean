module

public import ConvergentGermLocalRing
public import ConvergentGermAmbientJetEquiv
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

@[expose] public section

/-!
# Jets of a quotient given by a surjective actual-germ map

First-party composition, 2026-10-23. No outgoing project license is selected.
The map and its surjectivity are explicit inputs; this does not construct a
project branch or assume an unnamed chart. The actual analytic carriers and
their existing maximal ideals are unchanged. No Noetherian premise is needed.

Imported APIs, with no upstream proof copied: IsLocalRing.map_maximalIdeal_of_surjective
(Mathlib/RingTheory/LocalRing/RingHom/Basic.lean, header authors Kenny Lau,
Chris Hughes, Mario Carneiro); Ideal.map_pow, comap_map_of_surjective, and
quotientMap_injective'/surjective (Ideal/Maps.lean and Ideal/Quotient/Operations.lean).
Mathlib4 https://github.com/leanprover-community/mathlib4 at
065356127b1dc0016f66b7283ce0ce2c4055aa55, Apache-2.0. Thank you to the
Mathlib, SCV and accepted analytic-germ contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

noncomputable section

namespace ConvergentGermSurjectiveJets

open ConvergentResidualJets ConvergentGermLocalRing ConvergentGermAmbientJetEquiv

theorem map_vanishingIdeal {n d : ℕ}
    (ρ : GermRing n →ₐ[ℂ] GermRing d) (hρ : Function.Surjective ρ) :
    Ideal.map ρ.toRingHom (vanishingIdeal n) = vanishingIdeal d := by
  simpa only [maximalIdeal_eq_vanishingIdeal] using
    IsLocalRing.map_maximalIdeal_of_surjective ρ.toRingHom hρ

theorem comap_vanishingIdeal_pow {n d : ℕ}
    (ρ : GermRing n →ₐ[ℂ] GermRing d) (hρ : Function.Surjective ρ) (k : ℕ) :
    Ideal.comap ρ.toRingHom (vanishingIdeal d ^ k) =
      RingHom.ker ρ.toRingHom ⊔ vanishingIdeal n ^ k := by
  rw [← map_vanishingIdeal ρ hρ, ← Ideal.map_pow,
    Ideal.comap_map_of_surjective ρ.toRingHom hρ]
  change vanishingIdeal n ^ k ⊔ RingHom.ker ρ.toRingHom =
    RingHom.ker ρ.toRingHom ⊔ vanishingIdeal n ^ k
  exact sup_comm _ _

/-- The quotient equivalence is induced by the supplied map ρ. Surjectivity is
an explicit mathematical obligation, not a branch-existence assertion. -/
def quotientJetEquiv {n d : ℕ}
    (ρ : GermRing n →ₐ[ℂ] GermRing d) (hρ : Function.Surjective ρ) (N : ℕ) :
    (GermRing n ⧸ (RingHom.ker ρ.toRingHom ⊔ vanishingIdeal n ^ (N + 1))) ≃ₐ[ℂ]
      (GermRing d ⧸ vanishingIdeal d ^ (N + 1)) :=
  AlgEquiv.ofBijective
    (Ideal.quotientMapₐ (vanishingIdeal d ^ (N + 1)) ρ
      (comap_vanishingIdeal_pow ρ hρ (N + 1)).ge)
    ⟨Ideal.quotientMap_injective'
        (H := (comap_vanishingIdeal_pow ρ hρ (N + 1)).ge)
        (comap_vanishingIdeal_pow ρ hρ (N + 1)).le,
      Ideal.quotientMap_surjective
        (H := (comap_vanishingIdeal_pow ρ hρ (N + 1)).ge) hρ⟩

theorem quotientJetEquiv_mk {n d : ℕ}
    (ρ : GermRing n →ₐ[ℂ] GermRing d) (hρ : Function.Surjective ρ)
    (N : ℕ) (u : GermRing n) :
    quotientJetEquiv ρ hρ N
        (Ideal.Quotient.mk (RingHom.ker ρ.toRingHom ⊔ vanishingIdeal n ^ (N + 1)) u) =
      Ideal.Quotient.mk (vanishingIdeal d ^ (N + 1)) (ρ u) := rfl

/-- Exact truncated-polynomial jets of the supplied quotient, using the
independently proved ambient equivalence. -/
def quotientJetPolynomialEquiv {n d : ℕ}
    (ρ : GermRing n →ₐ[ℂ] GermRing d) (hρ : Function.Surjective ρ) (N : ℕ) :
    (GermRing n ⧸ (RingHom.ker ρ.toRingHom ⊔ vanishingIdeal n ^ (N + 1))) ≃ₐ[ℂ]
      (Poly d ⧸ polynomialJetIdeal (⊥ : Ideal (Poly d)) N) :=
  (quotientJetEquiv ρ hρ N).trans
    ((Ideal.quotientEquivAlgOfEq ℂ
      (show vanishingIdeal d ^ (N + 1) = analyticJetIdeal (⊥ : Ideal (Poly d)) N by
        simp only [analyticJetIdeal, Ideal.map_bot, bot_sup_eq])).trans
      (ambientJetEquiv d N).symm)

end ConvergentGermSurjectiveJets


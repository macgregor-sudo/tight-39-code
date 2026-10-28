module

public import ConvergentGermSurjectiveJets
public import PolynomialJetPrerequisitesModule
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-!
# Exact dimensions of actual smooth germ jets

First-party composition and elementary monomial count, 2026-10-23; no outgoing
project license selected. The polynomial kernel and actual germ equivalence are
already proved inputs. Exact-degree exponent vectors are counted by symmetric
powers, then summed using the stars-and-bars identity, including zero variables.
No actual project chart is constructed.

Import-only API provenance (no proof copied): Sym.equivNatSum in Data/Finsupp/Multiset;
Sym.card_sym_eq_multichoose in Data/Sym/Card; Nat.sum_range_multichoose in
Data/Nat/Choose/Sum; LinearMap.quotKerEquivOfSurjective, Submodule.quotEquivOfEq,
Submodule.Quotient.restrictScalarsEquiv and Module.finrank_pi in their standard
Mathlib files, https://github.com/leanprover-community/mathlib4 at
065356127b1dc0016f66b7283ce0ce2c4055aa55, Apache-2.0.
Thank you to the Mathlib and accepted polynomial/analytic-jet contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

noncomputable section

namespace ConvergentGermJetDimensions

open ConvergentResidualJets ConvergentGermAmbientJetEquiv
open ConvergentGermSurjectiveJets PolynomialJets

/-- Bounded-degree monomials, counted by their exact degree. -/
theorem card_monomialsUpTo (n N : ℕ) :
    Fintype.card (MonomialsUpTo (Fin n) N) = (N + n).choose n := by
  classical
  let e₁ : MonomialsUpTo (Fin n) N ≃
      (Σ k : Fin (N + 1), {a : Fin n →₀ ℕ // Finsupp.degree a = k.val}) :=
    { toFun := fun a => ⟨⟨Finsupp.degree a.val, Nat.lt_succ_of_le a.property⟩,
          ⟨a.val, rfl⟩⟩
      invFun := fun b => ⟨b.2.val, by
        rw [b.2.property]
        exact Nat.le_of_lt_succ b.1.isLt⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨k, hk⟩, ⟨a, ha⟩⟩
        cases ha
        rfl }
  let e₂ : (Σ k : Fin (N + 1), {a : Fin n →₀ ℕ // Finsupp.degree a = k.val}) ≃
      (Σ k : Fin (N + 1), Sym (Fin n) k.val) :=
    Equiv.sigmaCongrRight fun k => (Sym.equivNatSum (Fin n) k.val).symm
  calc
    _ = Fintype.card (Σ k : Fin (N + 1), Sym (Fin n) k.val) :=
      Fintype.card_congr (e₁.trans e₂)
    _ = ∑ k : Fin (N + 1), n.multichoose k.val := by
      simp only [Fintype.card_sigma, Sym.card_sym_eq_multichoose, Fintype.card_fin]
    _ = (N + n).choose n := by
      rw [Fin.sum_univ_eq_sum_range]
      exact Nat.sum_range_multichoose N n

/-- The coefficient map is the accepted lowCoeff map on representatives. -/
def polynomialJetCoefficientEquiv (n N : ℕ) :
    (Poly n ⧸ polynomialJetIdeal (⊥ : Ideal (Poly n)) N) ≃ₗ[ℂ]
      (MonomialsUpTo (Fin n) N → ℂ) := by
  let I := variableIdeal n ^ (N + 1)
  let L : Poly n →ₗ[ℂ] (MonomialsUpTo (Fin n) N → ℂ) := lowCoeff N
  have hker : LinearMap.ker L = I.restrictScalars ℂ :=
    lowCoeff_ker_eq_variableIdeal_pow N
  exact (Ideal.quotientEquivAlgOfEq ℂ
      (show polynomialJetIdeal (⊥ : Ideal (Poly n)) N = I by
        simp only [polynomialJetIdeal, bot_sup_eq, I])).toLinearEquiv.trans
    ((Submodule.Quotient.restrictScalarsEquiv ℂ I).symm.trans
      ((Submodule.quotEquivOfEq (I.restrictScalars ℂ) (LinearMap.ker L) hker.symm).trans
        (L.quotKerEquivOfSurjective (lowCoeff_surjective N))))

theorem polynomialJet_finrank (n N : ℕ) :
    Module.finrank ℂ (Poly n ⧸ polynomialJetIdeal (⊥ : Ideal (Poly n)) N) =
      (N + n).choose n := by
  rw [(polynomialJetCoefficientEquiv n N).finrank_eq, Module.finrank_pi,
    card_monomialsUpTo]

theorem germJet_finrank (n N : ℕ) :
    Module.finrank ℂ (GermRing n ⧸ vanishingIdeal n ^ (N + 1)) =
      (N + n).choose n := by
  let e : (GermRing n ⧸ vanishingIdeal n ^ (N + 1)) ≃ₐ[ℂ]
      (GermRing n ⧸ analyticJetIdeal (⊥ : Ideal (Poly n)) N) :=
    Ideal.quotientEquivAlgOfEq ℂ (by
      simp only [analyticJetIdeal, Ideal.map_bot, bot_sup_eq])
  exact e.toLinearEquiv.finrank_eq.trans
    ((ambientJetEquiv n N).toLinearEquiv.finrank_eq.symm.trans
      (polynomialJet_finrank n N))

/-- The explicit supplied surjection identifies its quotient jets exactly. -/
theorem surjective_quotientJet_finrank {n d : ℕ}
    (ρ : GermRing n →ₐ[ℂ] GermRing d) (hρ : Function.Surjective ρ) (N : ℕ) :
    Module.finrank ℂ
      (GermRing n ⧸ (RingHom.ker ρ.toRingHom ⊔ vanishingIdeal n ^ (N + 1))) =
      (N + d).choose d :=
  (quotientJetPolynomialEquiv ρ hρ N).toLinearEquiv.finrank_eq.trans
    (polynomialJet_finrank d N)

end ConvergentGermJetDimensions


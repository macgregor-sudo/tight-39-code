module

public import ConvergentResidualJetLength
public import NativeConfigurationConvergentJets

@[expose] public section

/-!
# Actual configuration residual lengths and the polynomial G jet

This specializes the existing scalar-restriction and Artin–Rees comparisons
to the literal native F2184 and G3159 row families at the same complex point.
The lower analytic ideal remains the translated F ideal; the polynomial
upper bound uses the equal translated G ideal. Noetherianity remains an
explicit instance, and no point solution or numerical bound is asserted.

First-party composition of named APIs; no copied proof body. The unchanged
generic Artin–Rees result is imported separately; the
length restriction and finite-dimensional length facts are Mathlib APIs
at 065356127b1dc0016f66b7283ce0ce2c4055aa55, Lean v4.35.0-rc2.
Thank you to the Artin–Rees proof author and the Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

noncomputable section

namespace NativePolynomial.ConfigurationResiduals

open ConvergentResidualJets ConvergentResidualJetLength PolynomialJets

/-- The actual analytic F jet has length bounded by the polynomial G jet dimension. -/
theorem translated_f_analyticJet_length_le_g_polynomialJet
    (h t : ℂ) (hHalf : (2 : ℂ) * h = 1) (hThird : (3 : ℂ) * t = 1)
    (P : Fin 1053 → ℂ) (N : ℕ) :
    Module.length (GermRing 1053) (GermRing 1053 ⧸ analyticJetIdeal
        (Ideal.span (Set.range (fun r : Fin 2184 => translate P (fRow h t r)))) N) ≤
      (Module.finrank ℂ (Poly 1053 ⧸ equationJetSubmodule
        (fun r : Fin 3159 => translate P (gRow h t r)) N) : ℕ∞) :=
  (analyticJet_length_le_finrank _ N).trans
    (ENat.natCast_le_natCast.mpr
      (translated_f_analyticJet_finrank_le_g_polynomialJet h t hHalf hThird P N))

/-- The full shifted Artin–Rees comparison for actual F is bounded by the G jet.
The same shift works for every order, and the containing analytic ideal J is
kept literal throughout the two-term length expression. -/
theorem exists_shifted_f_length_le_g_polynomialJet
    [IsNoetherianRing (GermRing 1053)]
    (h t : ℂ) (hHalf : (2 : ℂ) * h = 1) (hThird : (3 : ℂ) * t = 1)
    (P : Fin 1053 → ℂ) (J : Ideal (GermRing 1053))
    (hIJ : Ideal.map (polynomialGerm 1053).toRingHom
      (Ideal.span (Set.range (fun r : Fin 2184 => translate P (fRow h t r)))) ≤ J) :
    ∃ c : ℕ, ∀ N : ℕ,
      Module.length (GermRing 1053)
          (ShiftedJetLength.QuotientIdealModule
              (Ideal.map (polynomialGerm 1053).toRingHom
                (Ideal.span (Set.range (fun r : Fin 2184 => translate P (fRow h t r))))) J ⧸
            ((vanishingIdeal 1053 ^ (N + 1)) •
              (⊤ : Submodule (GermRing 1053) (ShiftedJetLength.QuotientIdealModule
                (Ideal.map (polynomialGerm 1053).toRingHom
                  (Ideal.span (Set.range (fun r : Fin 2184 => translate P (fRow h t r))))) J)))) +
        Module.length (GermRing 1053)
          (GermRing 1053 ⧸ (J ⊔ vanishingIdeal 1053 ^ (N + c + 1))) ≤
      (Module.finrank ℂ (Poly 1053 ⧸ equationJetSubmodule
        (fun r : Fin 3159 => translate P (gRow h t r)) (N + c)) : ℕ∞) := by
  obtain ⟨c, hc⟩ := ShiftedJetLength.exists_shifted_jet_length_comparison
    (vanishingIdeal 1053)
    (Ideal.map (polynomialGerm 1053).toRingHom
      (Ideal.span (Set.range (fun r : Fin 2184 => translate P (fRow h t r))))) J hIJ
  refine ⟨c, fun N => ?_⟩
  exact (hc N).trans
    (translated_f_analyticJet_length_le_g_polynomialJet h t hHalf hThird P (N + c))

end NativePolynomial.ConfigurationResiduals

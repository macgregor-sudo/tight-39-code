module

public import ConvergentJetDimensionTransfer
public import ConvergentResidualPointBinding
public import NativeConfigurationTranslatedIdeal

@[expose] public section

/-!
# The same complex point and actual native residuals in convergent jets

The existing native F2184 and G3159 rows are translated by the same arbitrary
complex point. Their checked ideal equality passes through the unchanged
polynomial germ map. The analytic F jet is bounded by the literal polynomial
G jet at every order. The separate pointed criterion retains explicit
vanishing of the actual F rows at that same point; no solution is fabricated.

First-party composition of accepted native ideal equality, polynomial/germ
evaluation and analytic dimension-transfer APIs. No upstream proof code is
copied. This is ordinary ideal transport and a surjective-map dimension
inequality, not a concrete numerical bound or a geometric theorem.
Lean v4.35.0-rc2, mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55.
-/

noncomputable section

namespace NativePolynomial.ConfigurationResiduals

open ConvergentResidualJets ConvergentJetDimensionTransfer
open ConvergentResidualPointBinding PolynomialJets

/-- The actual translated F residuals define a pointed ideal precisely at F solutions. -/
theorem translated_fSpan_germ_le_vanishingIdeal_iff
    (h t : ℂ) (P : Fin 1053 → ℂ) :
    Ideal.map (polynomialGerm 1053).toRingHom
        (Ideal.span (Set.range (fun r : Fin 2184 => translate P (fRow h t r)))) ≤
        vanishingIdeal 1053 ↔
      ∀ r : Fin 2184, MvPolynomial.eval P (fRow h t r) = 0 :=
  map_translated_span_le_vanishingIdeal_iff (fRow h t) P

/-- The actual F and G analytic generator ideals agree after the same translation. -/
theorem translated_fSpan_germ_eq_translated_gSpan_germ
    (h t : ℂ) (hHalf : (2 : ℂ) * h = 1) (hThird : (3 : ℂ) * t = 1)
    (P : Fin 1053 → ℂ) :
    Ideal.map (polynomialGerm 1053).toRingHom
        (Ideal.span (Set.range (fun r : Fin 2184 => translate P (fRow h t r)))) =
      Ideal.map (polynomialGerm 1053).toRingHom
        (Ideal.span (Set.range (fun r : Fin 3159 => translate P (gRow h t r)))) :=
  congrArg (Ideal.map (polynomialGerm 1053).toRingHom)
    (translated_fSpan_eq_translated_gSpan h t hHalf hThird P)

/-- At every order the actual analytic F jet inherits the actual polynomial G upper bound. -/
theorem translated_f_analyticJet_finrank_le_g_polynomialJet
    (h t : ℂ) (hHalf : (2 : ℂ) * h = 1) (hThird : (3 : ℂ) * t = 1)
    (P : Fin 1053 → ℂ) (N : ℕ) :
    Module.finrank ℂ (GermRing 1053 ⧸ analyticJetIdeal
        (Ideal.span (Set.range (fun r : Fin 2184 => translate P (fRow h t r)))) N) ≤
      Module.finrank ℂ (Poly 1053 ⧸ equationJetSubmodule
        (fun r : Fin 3159 => translate P (gRow h t r)) N) := by
  rw [translated_fSpan_eq_translated_gSpan h t hHalf hThird P]
  exact analyticJet_finrank_le_equationJet
    (fun r : Fin 3159 => translate P (gRow h t r)) N

end NativePolynomial.ConfigurationResiduals

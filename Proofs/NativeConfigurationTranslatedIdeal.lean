module

public import NativeConfigurationIdealEquality
public import PolynomialJetPrerequisitesModule

@[expose] public section

/-!
# Equality of the actual configuration ideals after a common translation

The same substitution Xj ↦ Xj + C(Pj) is applied to every original F and G
row. Mapping the actual ideal equality identifies the two translated generator
ideals for every point P, without assuming that P is a solution.

First-party dependencies: NativeConfigurationIdealEquality source
b490a0e741592832345d2000f936d2b0e6e4f18f3c6e4ca1be84461e29756923;
PolynomialJetPrerequisitesModule source
6c33cbe04813285f8e1bf6775b5dca300a58b642117fd3768844513423c25588.
Mathlib at 065356127b1dc0016f66b7283ce0ce2c4055aa55, Lean v4.35.0-rc2,
supplies MvPolynomial.eval₂Hom, Ideal.map_span and Set.range_comp'. Those
sources use Apache-2.0; no upstream implementation is copied here. This is
standard ideal-map composition, with no novelty or local dimension claim.
Thank you to the native-model, Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

namespace NativePolynomial.ConfigurationResiduals

variable {R : Type*} [CommRing R]

/-- The literal F and G generator ideals agree after translation by the same
arbitrary P. No solution-point premise is needed for this ideal equality. -/
theorem translated_fSpan_eq_translated_gSpan
    (h t : R) (hHalf : (2 : R) * h = 1) (hThird : (3 : R) * t = 1)
    (P : Fin 1053 → R) :
    Ideal.span (Set.range (fun r : Fin 2184 =>
      PolynomialJets.translate P (fRow h t r))) =
    Ideal.span (Set.range (fun r : Fin 3159 =>
      PolynomialJets.translate P (gRow h t r))) := by
  let τ : MvPolynomial (Fin 1053) R →+* MvPolynomial (Fin 1053) R :=
    MvPolynomial.eval₂Hom MvPolynomial.C
      (fun j => MvPolynomial.X j + MvPolynomial.C (P j))
  have hApply (q : MvPolynomial (Fin 1053) R) :
      τ q = PolynomialJets.translate P q := rfl
  have hMapped :
      Ideal.map τ (Ideal.span (Set.range (fRow h t))) =
        Ideal.map τ (Ideal.span (Set.range (gRow h t))) :=
    congrArg (Ideal.map τ) (fIdeal_eq_gSpan h t hHalf hThird)
  simpa only [Ideal.map_span, ← Set.range_comp', hApply] using hMapped

end NativePolynomial.ConfigurationResiduals

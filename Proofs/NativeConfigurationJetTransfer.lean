module

public import NativeConfigurationTranslatedIdeal

@[expose] public section

/-!
# Canonical finite-jet transfer between the actual translated F and G rows

The same origin-variable ideal power is added to the already equal translated
generator ideals. Their literal submodules are equal, so the standard quotient
equivalence keeps every polynomial representative unchanged. The translation
point is arbitrary; no solution, terminal bound or analytic claim enters.

First-party dependency NativeConfigurationTranslatedIdeal has source hash
60e7bbf8a765481b2c0f438ef3a060bd05258262c32b9fbb394c18519742bf08.
Mathlib at 065356127b1dc0016f66b7283ce0ce2c4055aa55, Lean v4.35.0-rc2,
owns Submodule.quotEquivOfEq in LinearAlgebra/Quotient/Defs.lean. Its source
uses Apache-2.0; no upstream implementation is copied here. This is standard
quotient transport, not a new mathematical result. Thank you to the native,
Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

namespace NativePolynomial.ConfigurationResiduals

open PolynomialJets

variable {R : Type*} [CommRing R]

/-- The actual jet relation submodules agree at each order after the same
arbitrary translation. The origin-variable power is retained on both sides. -/
theorem translated_equationJetSubmodule_eq
    (h t : R) (hHalf : (2 : R) * h = 1) (hThird : (3 : R) * t = 1)
    (P : Fin 1053 → R) (N : ℕ) :
    equationJetSubmodule
      (fun r : Fin 2184 => translate P (fRow h t r)) N =
    equationJetSubmodule
      (fun r : Fin 3159 => translate P (gRow h t r)) N := by
  unfold equationJetSubmodule
  rw [translated_fSpan_eq_translated_gSpan h t hHalf hThird P]

/-- Canonical transfer of the literal finite polynomial jets, induced by the
identity on polynomial representatives and the proved submodule equality. -/
noncomputable def translated_equationJetEquiv
    (h t : R) (hHalf : (2 : R) * h = 1) (hThird : (3 : R) * t = 1)
    (P : Fin 1053 → R) (N : ℕ) :
    (MvPolynomial (Fin 1053) R ⧸ equationJetSubmodule
      (fun r : Fin 2184 => translate P (fRow h t r)) N) ≃ₗ[R]
    (MvPolynomial (Fin 1053) R ⧸ equationJetSubmodule
      (fun r : Fin 3159 => translate P (gRow h t r)) N) :=
  Submodule.quotEquivOfEq _ _
    (translated_equationJetSubmodule_eq h t hHalf hThird P N)

end NativePolynomial.ConfigurationResiduals

module

public import ConvergentJetDimensionTransfer
public import ArtinReesJetLength

@[expose] public section

/-!
# Residual analytic jet lengths bounded by polynomial jet dimensions

The actual analytic-representative germ ring acts on its finite complex jet
quotients. Restricting scalars to the constants bounds germ-module length by
complex dimension. The existing canonical jet surjection then bounds length
by the dimension of the same polynomial equation jet.

The final theorem consumes the exact generic Artin–Rees comparison supplied
by `ShiftedJetLength.exists_shifted_jet_length_comparison`, preserving its
two-term left side and its uniform shift. Noetherianity of the actual germ
ring is an explicit instance argument; this file does not establish it.

First-party composition, with no copied upstream proof body. The consumed
ArtinReesJetLength.lean is an AI-assisted first-party module, whose source
notice and attribution remain unchanged. Mathlib's length restriction and
finite-dimensional length APIs are from RingTheory/Length.lean, copyright
2025 Andrew Yang, Apache-2.0; https://github.com/leanprover-community/mathlib4,
commit 065356127b1dc0016f66b7283ce0ce2c4055aa55, Lean v4.35.0-rc2.
Thank you to the Artin–Rees proof author and the Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

noncomputable section

namespace ConvergentResidualJetLength

open ConvergentResidualJets ConvergentJetDimensionTransfer PolynomialJets

/-- The constants give an upper bound on the length of an analytic jet. -/
theorem analyticJet_length_le_finrank {n : ℕ} (Q : Ideal (Poly n)) (N : ℕ) :
    Module.length (GermRing n) (GermRing n ⧸ analyticJetIdeal Q N) ≤
      (Module.finrank ℂ (GermRing n ⧸ analyticJetIdeal Q N) : ℕ∞) := by
  let p : Submodule (GermRing n) (GermRing n ⧸ analyticJetIdeal Q N) := ⊤
  let e : p.restrictScalars ℂ ≃ₗ[ℂ] (GermRing n ⧸ analyticJetIdeal Q N) :=
    ((Submodule.restrictScalarsEquiv ℂ (GermRing n)
      (GermRing n ⧸ analyticJetIdeal Q N) p).trans Submodule.topEquiv).restrictScalars ℂ
  calc
    Module.length (GermRing n) (GermRing n ⧸ analyticJetIdeal Q N) =
        Module.length (GermRing n) p := Module.length_top.symm
    _ ≤ Module.length ℂ (p.restrictScalars ℂ) :=
      Submodule.length_le_length_restrictScalars ℂ p
    _ = Module.length ℂ (GermRing n ⧸ analyticJetIdeal Q N) := e.length_eq
    _ = _ := Module.length_eq_finrank ℂ (GermRing n ⧸ analyticJetIdeal Q N)

/-- The existing polynomial equation jet bounds actual analytic module length. -/
theorem analyticJet_length_le_equationJet_finrank {n : ℕ} {ι : Type*}
    (g : ι → Poly n) (N : ℕ) :
    Module.length (GermRing n)
        (GermRing n ⧸ analyticJetIdeal (Ideal.span (Set.range g)) N) ≤
      (Module.finrank ℂ (Poly n ⧸ equationJetSubmodule g N) : ℕ∞) :=
  (analyticJet_length_le_finrank (Ideal.span (Set.range g)) N).trans
    (ENat.natCast_le_natCast.mpr (analyticJet_finrank_le_equationJet g N))

/-- Artin–Rees and the canonical jet map give a uniform polynomial upper bound.
The carrier is the actual germ ring and the lower ideal is the image of the
specified polynomial residual ideal. The containing ideal remains arbitrary. -/
theorem exists_shifted_length_le_equationJet_finrank {n : ℕ} {ι : Type*}
    [IsNoetherianRing (GermRing n)] (g : ι → Poly n) (J : Ideal (GermRing n))
    (hIJ : Ideal.map (polynomialGerm n).toRingHom (Ideal.span (Set.range g)) ≤ J) :
    ∃ c : ℕ, ∀ N : ℕ,
      Module.length (GermRing n)
          (ShiftedJetLength.QuotientIdealModule
              (Ideal.map (polynomialGerm n).toRingHom (Ideal.span (Set.range g))) J ⧸
            ((vanishingIdeal n ^ (N + 1)) •
              (⊤ : Submodule (GermRing n) (ShiftedJetLength.QuotientIdealModule
                (Ideal.map (polynomialGerm n).toRingHom (Ideal.span (Set.range g))) J)))) +
        Module.length (GermRing n)
          (GermRing n ⧸ (J ⊔ vanishingIdeal n ^ (N + c + 1))) ≤
      (Module.finrank ℂ (Poly n ⧸ equationJetSubmodule g (N + c)) : ℕ∞) := by
  obtain ⟨c, hc⟩ := ShiftedJetLength.exists_shifted_jet_length_comparison
    (vanishingIdeal n)
    (Ideal.map (polynomialGerm n).toRingHom (Ideal.span (Set.range g))) J hIJ
  refine ⟨c, fun N => ?_⟩
  exact (hc N).trans (analyticJet_length_le_equationJet_finrank g (N + c))

end ConvergentResidualJetLength

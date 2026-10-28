module

public import AnnihilatorLengthBound
public import ConvergentGermSCVNoetherian
public import Mathlib.RingTheory.Ideal.Colon

@[expose] public section

/-!
# Annihilator lengths for actual analytic ideal quotients

The carrier is the unchanged ring of analytic-representative germs. The
existing quotient module is J modulo the preimage of I under its inclusion;
its annihilator is exactly the literal colon ideal (I : J). In the intended
application I is contained in J, so this is the module J/I.

The separately proved SCV Noetherian theorem makes J and its quotient finite.
The exact annihilator-length theorem then applies without a new length,
growth or finiteness hypothesis.

First-party composition of named APIs; no upstream proof body is copied.
Mathlib's Submodule.annihilator_quotient and mem_colon are from
RingTheory/Ideal/Colon.lean at 065356127b1dc0016f66b7283ce0ce2c4055aa55,
Lean v4.35.0-rc2. Imported licenses and attributions remain with the unchanged
producers. Thank you to the annihilator, Artin–Rees, SCV, Lean and Mathlib
contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

noncomputable section

namespace ConvergentResidualAnnihilatorLength

open ConvergentResidualJets

/-- The annihilator of the actual ideal quotient is the literal ideal colon. -/
theorem quotientIdealModule_annihilator_eq_colon {n : ℕ}
    (I J : Ideal (GermRing n)) :
    Module.annihilator (GermRing n) (ShiftedJetLength.QuotientIdealModule I J) =
      (I : Submodule (GermRing n) (GermRing n)).colon (J : Set (GermRing n)) := by
  change Module.annihilator (GermRing n)
    (J ⧸ Submodule.comap (Submodule.subtype (J : Submodule (GermRing n) (GermRing n)))
      (I : Submodule (GermRing n) (GermRing n))) = _
  rw [Submodule.annihilator_quotient]
  ext a
  rw [Submodule.mem_colon, Submodule.mem_colon]
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩ (Set.mem_univ _)
  · intro h x _
    exact h x.val x.property

/-- The actual germ ring satisfies the uniform colon-length comparison.
Containment is retained explicitly for the intended J/I interpretation. -/
theorem exists_colon_length_bound {n : ℕ} (I J : Ideal (GermRing n))
    (_hIJ : I ≤ J) :
    ∃ c r : ℕ, ∀ N : ℕ,
      Module.length (GermRing n)
        (GermRing n ⧸ ((I : Submodule (GermRing n) (GermRing n)).colon
          (J : Set (GermRing n)) ⊔ vanishingIdeal n ^ (N + 1))) ≤
      (r : ℕ∞) * Module.length (GermRing n)
        (ShiftedJetLength.QuotientIdealModule I J ⧸
          ((vanishingIdeal n ^ (N + c + 1)) •
            (⊤ : Submodule (GermRing n) (ShiftedJetLength.QuotientIdealModule I J)))) := by
  letI := ConvergentGermSCVBridge.germRing_isNoetherianRing n
  have h := AnnihilatorLengthBound.exists_length_quotient_annihilator_sup_pow_le
    (M := ShiftedJetLength.QuotientIdealModule I J) (vanishingIdeal n)
  rwa [quotientIdealModule_annihilator_eq_colon I J] at h

end ConvergentResidualAnnihilatorLength

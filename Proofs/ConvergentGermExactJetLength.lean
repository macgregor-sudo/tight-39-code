module

public import ConvergentGermJetDimensions
public import Mathlib.RingTheory.LocalRing.Length

@[expose] public section

/-!
# Exact module lengths of actual convergent-germ jets

First-party composition, 2026-10-23. The accepted complex-algebra residue
identification makes restriction of scalars preserve length. Noetherianity,
branch existence, and a general Taylor interface are not premises.

Import-only API provenance (no proof body copied):
IsLocalRing.length_restrictScalars, Mathlib/RingTheory/LocalRing/Length.lean,
Thomas Browning; Module.length_eq_of_surjective and Module.length_eq_finrank,
Mathlib/RingTheory/Length.lean, Andrew Yang; Module.Finite.equiv,
Mathlib/RingTheory/Finiteness/Basic.lean, Johan Commelin.
https://github.com/leanprover-community/mathlib4 at
065356127b1dc0016f66b7283ce0ce2c4055aa55, Apache-2.0.
Thank you to these authors and the accepted germ and polynomial contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

noncomputable section

namespace ConvergentGermExactJetLength

open ConvergentResidualJets ConvergentGermLocalRing ConvergentGermAmbientJetEquiv
open ConvergentGermSurjectiveJets ConvergentGermJetDimensions

/-- The residue degree is one for the actual complex scalar algebra. -/
theorem residue_length (n : ℕ) :
    Module.length (IsLocalRing.ResidueField ℂ)
      (IsLocalRing.ResidueField (GermRing n)) = 1 := by
  rw [← Module.length_eq_of_surjective
    (M := IsLocalRing.ResidueField (GermRing n))
    (IsLocalRing.residue_surjective (R := ℂ))]
  exact (quotientMaximalIdealEquiv n).toLinearEquiv.length_eq.trans
    (Module.length_eq_one ℂ ℂ)

/-- This equality holds also for infinite length; no finiteness is assumed. -/
theorem length_eq_complex_length {n : ℕ} (M : Type*)
    [AddCommGroup M] [Module (GermRing n) M] [Module ℂ M]
    [IsScalarTower ℂ (GermRing n) M] :
    Module.length (GermRing n) M = Module.length ℂ M := by
  have h := IsLocalRing.length_restrictScalars ℂ (GermRing n) M
  simpa only [residue_length, mul_one] using h.symm

theorem germJet_finite (n N : ℕ) :
    Module.Finite ℂ (GermRing n ⧸ vanishingIdeal n ^ (N + 1)) := by
  letI : Module.Finite ℂ (Poly n ⧸ polynomialJetIdeal (⊥ : Ideal (Poly n)) N) :=
    Module.Finite.equiv (polynomialJetCoefficientEquiv n N).symm
  letI := Module.Finite.equiv (ambientJetEquiv n N).toLinearEquiv
  let e : (GermRing n ⧸ vanishingIdeal n ^ (N + 1)) ≃ₐ[ℂ]
      (GermRing n ⧸ analyticJetIdeal (⊥ : Ideal (Poly n)) N) :=
    Ideal.quotientEquivAlgOfEq ℂ (by
      simp only [analyticJetIdeal, Ideal.map_bot, bot_sup_eq])
  exact Module.Finite.equiv e.toLinearEquiv.symm

theorem germJet_length (n N : ℕ) :
    Module.length (GermRing n) (GermRing n ⧸ vanishingIdeal n ^ (N + 1)) =
      ((N + n).choose n : ℕ∞) := by
  letI := germJet_finite n N
  rw [length_eq_complex_length, Module.length_eq_finrank, germJet_finrank]

/-- The explicit supplied surjection is the only branch input in this theorem. -/
theorem surjective_quotientJet_length {n d : ℕ}
    (ρ : GermRing n →ₐ[ℂ] GermRing d) (hρ : Function.Surjective ρ) (N : ℕ) :
    Module.length (GermRing n)
      (GermRing n ⧸ (RingHom.ker ρ.toRingHom ⊔ vanishingIdeal n ^ (N + 1))) =
      ((N + d).choose d : ℕ∞) := by
  letI : Module.Finite ℂ (Poly d ⧸ polynomialJetIdeal (⊥ : Ideal (Poly d)) N) :=
    Module.Finite.equiv (polynomialJetCoefficientEquiv d N).symm
  letI := Module.Finite.equiv (quotientJetPolynomialEquiv ρ hρ N).toLinearEquiv.symm
  rw [length_eq_complex_length, Module.length_eq_finrank,
    surjective_quotientJet_finrank ρ hρ N]

end ConvergentGermExactJetLength

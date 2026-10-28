module

public import ConvergentResidualAnnihilatorLength
public import ConvergentGermLocalRing
public import GrowthDimension.Consumer
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

@[expose] public section

/-!
# Dimension of a proper analytic colon quotient from its jet lengths

The ring is the unchanged analytic-representative germ ring. The quotient by
an explicit proper colon ideal is local and Noetherian. Its maximal-ideal
jets have exactly the lengths, over the original germ ring, of the quotients
by the colon plus the corresponding vanishing-ideal powers. The comparison
uses the surjective scalar map and the standard double-quotient equivalence.

The accepted GrowthDimension.Consumer then converts an explicit polynomial
length bound into a Krull-dimension bound. Properness and the bound remain
hypotheses; no branch, numerical growth or geometric claim is discharged.

First-party composition of named APIs; no upstream proof body is copied.
The generic dimension theorem is the separately accepted FLT port from
https://github.com/ImperialCollegeLondon/FLT at
923d45174c500aa1d994ba973bac38ea39eacbf7, original
FLT/Slop/DimensionTheorem/{Numeric,Defs,DimLeGrowth}.lean, Akhil Mathew,
Apache-2.0, with its unchanged notices and adaptation ledger. The index-shift
consumer is the AI-assisted first-party module. Mathlib is pinned to
065356127b1dc0016f66b7283ce0ce2c4055aa55, Lean v4.35.0-rc2.
Thank you to the FLT, analytic-germ, Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

noncomputable section

namespace ConvergentResidualColonDimension

open ConvergentResidualJets

/-- Maximal-ideal jet lengths in a proper germ quotient are the corresponding
colengths over the original germ ring, with the same order. -/
theorem quotientJet_length_eq {n : ℕ} (K : Ideal (GermRing n))
    [Nontrivial (GermRing n ⧸ K)] (N : ℕ) :
    Module.length (GermRing n ⧸ K)
        ((GermRing n ⧸ K) ⧸ IsLocalRing.maximalIdeal (GermRing n ⧸ K) ^ (N + 1)) =
      Module.length (GermRing n) (GermRing n ⧸ (K ⊔ vanishingIdeal n ^ (N + 1))) := by
  have hMax := IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  rw [ConvergentGermLocalRing.maximalIdeal_eq_vanishingIdeal] at hMax
  rw [← hMax, ← Ideal.map_pow]
  rw [← Module.length_eq_of_surjective (S := GermRing n) (R := GermRing n ⧸ K)
    (M := (GermRing n ⧸ K) ⧸ (vanishingIdeal n ^ (N + 1)).map (Ideal.Quotient.mk K))
    (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ (GermRing n) K
    (vanishingIdeal n ^ (N + 1))).toLinearEquiv.length_eq

/-- An explicit uniform polynomial jet-length bound controls the dimension
of the literal proper colon quotient of the actual analytic germ ring. -/
theorem colon_krullDim_le_of_jet_length_bound {n d C : ℕ}
    (I J : Ideal (GermRing n))
    (hProper : (I : Submodule (GermRing n) (GermRing n)).colon
      (J : Set (GermRing n)) ≠ ⊤)
    (hGrowth : ∀ N : ℕ, Module.length (GermRing n)
      (GermRing n ⧸ ((I : Submodule (GermRing n) (GermRing n)).colon
        (J : Set (GermRing n)) ⊔ vanishingIdeal n ^ (N + 1))) ≤
      ((C * (N + 1) ^ d : ℕ) : ℕ∞)) :
    ringKrullDim (GermRing n ⧸ (I : Submodule (GermRing n) (GermRing n)).colon
      (J : Set (GermRing n))) ≤ (d : WithBot ℕ∞) := by
  let K := (I : Submodule (GermRing n) (GermRing n)).colon (J : Set (GermRing n))
  letI : Nontrivial (GermRing n ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hProper
  letI := ConvergentGermSCVBridge.germRing_isNoetherianRing n
  apply GrowthDimension.ringKrullDim_le_of_shifted_bound
    (R := GermRing n ⧸ K) (e := d) (C := C)
  intro N
  rw [quotientJet_length_eq]
  exact hGrowth N

/-- An eventual polynomial jet-length bound gives the same conclusion; the
generic consumer absorbs only the finitely many initial orders. -/
theorem colon_krullDim_le_of_eventually_jet_length_bound {n d C : ℕ}
    (I J : Ideal (GermRing n))
    (hProper : (I : Submodule (GermRing n) (GermRing n)).colon
      (J : Set (GermRing n)) ≠ ⊤)
    (hGrowth : ∀ᶠ N : ℕ in Filter.atTop, Module.length (GermRing n)
      (GermRing n ⧸ ((I : Submodule (GermRing n) (GermRing n)).colon
        (J : Set (GermRing n)) ⊔ vanishingIdeal n ^ (N + 1))) ≤
      ((C * (N + 1) ^ d : ℕ) : ℕ∞)) :
    ringKrullDim (GermRing n ⧸ (I : Submodule (GermRing n) (GermRing n)).colon
      (J : Set (GermRing n))) ≤ (d : WithBot ℕ∞) := by
  let K := (I : Submodule (GermRing n) (GermRing n)).colon (J : Set (GermRing n))
  letI : Nontrivial (GermRing n ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hProper
  letI := ConvergentGermSCVBridge.germRing_isNoetherianRing n
  apply GrowthDimension.ringKrullDim_le_of_eventually_shifted_bound
    (R := GermRing n ⧸ K) (e := d) (C := C)
  filter_upwards [hGrowth] with N hN
  rw [quotientJet_length_eq]
  exact hN

end ConvergentResidualColonDimension

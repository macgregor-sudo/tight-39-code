module

public import BranchJetLower
public import ConvergentGermSCVDomain
public import ConvergentGermExactJetLength
public import ConvergentResidualColonGrowth

@[expose] public section

/-!
# Four supplied analytic quotient maps and the colon-dimension bound

Each supplied surjective complex-algebra map from the actual n-variable germ
ring to the actual 62-variable germ ring has prime kernel and the exact
binomial jet lengths. Pairwise kernel incomparability is retained explicitly.
The accepted finite-branch Artin–Rees theorem then supplies one shift for the
intersection of these four literal kernels.

The second theorem combines that lower bound with the explicit shifted upper
length envelope for J/I. It retains I contained in the kernel intersection,
properness of the colon, and the upper estimate. No map, surjectivity,
incomparability, actual finite quartic premise or branch chart is constructed.

First-party composition; no upstream proof body copied. Imports use the
AI-assisted first-party BranchJetLower theorem and the
SCV analytic-germ, exact-jet and native length proofs. Their original source,
licenses and attributions remain unchanged. Pin: Lean v4.35.0-rc2, Mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55. Thank you to those authors and the
Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

noncomputable section

namespace ConvergentFourBranchColonDimension

open ConvergentResidualJets

/-- Four supplied surjections with incomparable kernels give the literal
shifted coefficient-four lower bound; primality and jet lengths are proved. -/
theorem exists_shifted_jet_lower_bound {n : ℕ}
    (ρ : Fin 4 → GermRing n →ₐ[ℂ] GermRing 62)
    (hSurj : ∀ i, Function.Surjective (ρ i))
    (hInc : ∀ i j, i ≠ j → ¬ RingHom.ker (ρ i).toRingHom ≤ RingHom.ker (ρ j).toRingHom) :
    ∃ cl : ℕ, ∀ N : ℕ, ((4 * (N + 62).choose 62 : ℕ) : ℕ∞) ≤
      Module.length (GermRing n)
        (GermRing n ⧸ ((⨅ i, RingHom.ker (ρ i).toRingHom) ⊔
          vanishingIdeal n ^ (N + cl + 1))) := by
  letI := ConvergentGermSCVBridge.germRing_isNoetherianRing n
  obtain ⟨cl, hcl⟩ := BranchJetLower.exists_sum_length_quotient_le
    (vanishingIdeal n) (fun i => RingHom.ker (ρ i).toRingHom)
    (fun i => ConvergentGermSCVBridge.kernel_isPrime (ρ i)) hInc
  refine ⟨cl, fun N => ?_⟩
  have hSum : (∑ i : Fin 4, Module.length (GermRing n)
      (GermRing n ⧸ (RingHom.ker (ρ i).toRingHom ⊔ vanishingIdeal n ^ (N + 1)))) =
      ((4 * (N + 62).choose 62 : ℕ) : ℕ∞) := by
    calc
      _ = ∑ _i : Fin 4, ((N + 62).choose 62 : ℕ∞) :=
        Finset.sum_congr rfl (fun i _ =>
          ConvergentGermExactJetLength.surjective_quotientJet_length (ρ i) (hSurj i) N)
      _ = (4 : ℕ) • ((N + 62).choose 62 : ℕ∞) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ = _ := by rw [nsmul_eq_mul, ENat.natCast_mul]
  rw [← hSum]
  exact hcl N

/-- The literal four-kernel intersection and the supplied upper envelope
force the proper colon quotient to have dimension at most 61. -/
theorem colon_krullDim_le_sixty_one {n : ℕ} (I : Ideal (GermRing n))
    (ρ : Fin 4 → GermRing n →ₐ[ℂ] GermRing 62)
    (hSurj : ∀ i, Function.Surjective (ρ i))
    (hInc : ∀ i j, i ≠ j → ¬ RingHom.ker (ρ i).toRingHom ≤ RingHom.ker (ρ j).toRingHom) :
    let J : Ideal (GermRing n) := ⨅ i, RingHom.ker (ρ i).toRingHom
    I ≤ J →
    (I : Submodule (GermRing n) (GermRing n)).colon (J : Set (GermRing n)) ≠ ⊤ →
    ∀ cu : ℕ,
      (∀ N : ℕ,
        Module.length (GermRing n) (ShiftedJetLength.QuotientIdealModule I J ⧸
          ((vanishingIdeal n ^ (N + 1)) •
            (⊤ : Submodule (GermRing n) (ShiftedJetLength.QuotientIdealModule I J)))) +
        Module.length (GermRing n) (GermRing n ⧸ (J ⊔ vanishingIdeal n ^ (N + cu + 1))) ≤
        ((4 * (N + cu + 62).choose 62 + 1540 * (N + cu + 61).choose 61 : ℕ) : ℕ∞)) →
      ringKrullDim (GermRing n ⧸ (I : Submodule (GermRing n) (GermRing n)).colon
        (J : Set (GermRing n))) ≤ (61 : WithBot ℕ∞) := by
  dsimp only
  intro hIJ hProper cu hUpper
  obtain ⟨cl, hLower⟩ := exists_shifted_jet_lower_bound ρ hSurj hInc
  exact ConvergentResidualColonGrowth.colon_krullDim_le_sixty_one_of_shifted_bounds
    I (⨅ i, RingHom.ker (ρ i).toRingHom) hIJ hProper cu cl hUpper hLower

end ConvergentFourBranchColonDimension

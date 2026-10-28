module

public import ConvergentResidualColonDimension
public import ShiftedBinomialGrowth

@[expose] public section

/-!
# Actual analytic ideal-quotient growth and colon dimension

The length sequence is that of the literal J/I module, with I contained in J,
and the companion sequence is the colength of J in the same analytic germ
ring. The existing quotient-length monotonicity theorem applies to the powers
of the actual vanishing ideal. Thus the shifted quartic upper envelope and an
explicit shifted four-branch lower bound imply degree-61 growth of J/I jets.

The accepted annihilator/colon comparison transfers any explicit polynomial
bound on those module jets to the colon quotient. Its fixed shift is absorbed
into the constant. The accepted actual-germ growth-to-dimension consumer then
applies. No branch lower bound, actual finite quartic premise, or properness
hypothesis is synthesized here.

First-party composition of the AI-assisted first-party Artin–Rees and annihilator
producers, actual-germ adapters, and ShiftedBinomialGrowth. No upstream proof
body is copied. Imported FLT, SCV and Mathlib notices and licenses remain in
their accepted dependency graphs. Pin: Mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55, Lean v4.35.0-rc2.
Thank you to those authors and the Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

noncomputable section

namespace ConvergentResidualColonGrowth

open ConvergentResidualJets

/-- Higher jets of the actual ideal quotient have nondecreasing length. -/
theorem quotientIdealModule_jet_length_monotone {n : ℕ} (I J : Ideal (GermRing n)) :
    Monotone (fun N : ℕ => Module.length (GermRing n)
      (ShiftedJetLength.QuotientIdealModule I J ⧸
        ((vanishingIdeal n ^ (N + 1)) •
          (⊤ : Submodule (GermRing n) (ShiftedJetLength.QuotientIdealModule I J))))) := by
  intro N N' h
  exact ShiftedJetLength.length_quotient_le_of_le
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)))

/-- The shifted upper and four-branch lower bounds leave degree-61 growth
for the actual J/I module jets. Both length premises remain explicit. -/
theorem exists_quotientIdealModule_degree_sixty_one_bound {n : ℕ}
    (I J : Ideal (GermRing n)) (_hIJ : I ≤ J) (cu cl : ℕ)
    (hUpper : ∀ N : ℕ,
      Module.length (GermRing n) (ShiftedJetLength.QuotientIdealModule I J ⧸
        ((vanishingIdeal n ^ (N + 1)) •
          (⊤ : Submodule (GermRing n) (ShiftedJetLength.QuotientIdealModule I J)))) +
      Module.length (GermRing n) (GermRing n ⧸ (J ⊔ vanishingIdeal n ^ (N + cu + 1))) ≤
      ((4 * (N + cu + 62).choose 62 + 1540 * (N + cu + 61).choose 61 : ℕ) : ℕ∞))
    (hLower : ∀ N : ℕ, ((4 * (N + 62).choose 62 : ℕ) : ℕ∞) ≤
      Module.length (GermRing n) (GermRing n ⧸ (J ⊔ vanishingIdeal n ^ (N + cl + 1)))) :
    ∃ C : ℕ, ∀ N : ℕ,
      Module.length (GermRing n) (ShiftedJetLength.QuotientIdealModule I J ⧸
        ((vanishingIdeal n ^ (N + 1)) •
          (⊤ : Submodule (GermRing n) (ShiftedJetLength.QuotientIdealModule I J)))) ≤
      ((C * (N + 1) ^ 61 : ℕ) : ℕ∞) := by
  exact ShiftedBinomialGrowth.exists_degree_sixty_one_bound
    (fun N => Module.length (GermRing n) (ShiftedJetLength.QuotientIdealModule I J ⧸
      ((vanishingIdeal n ^ (N + 1)) •
        (⊤ : Submodule (GermRing n) (ShiftedJetLength.QuotientIdealModule I J)))))
    (fun N => Module.length (GermRing n) (GermRing n ⧸ (J ⊔ vanishingIdeal n ^ (N + 1))))
    cu cl (quotientIdealModule_jet_length_monotone I J) hUpper hLower

/-- A polynomial bound on the actual J/I module jets bounds the dimension
of its proper colon quotient, using the accepted annihilator comparison. -/
theorem colon_krullDim_le_of_quotientIdealModule_growth {n d C : ℕ}
    (I J : Ideal (GermRing n)) (hIJ : I ≤ J)
    (hProper : (I : Submodule (GermRing n) (GermRing n)).colon
      (J : Set (GermRing n)) ≠ ⊤)
    (hGrowth : ∀ N : ℕ,
      Module.length (GermRing n) (ShiftedJetLength.QuotientIdealModule I J ⧸
        ((vanishingIdeal n ^ (N + 1)) •
          (⊤ : Submodule (GermRing n) (ShiftedJetLength.QuotientIdealModule I J)))) ≤
      ((C * (N + 1) ^ d : ℕ) : ℕ∞)) :
    ringKrullDim (GermRing n ⧸ (I : Submodule (GermRing n) (GermRing n)).colon
      (J : Set (GermRing n))) ≤ (d : WithBot ℕ∞) := by
  obtain ⟨c, r, hc⟩ := ConvergentResidualAnnihilatorLength.exists_colon_length_bound I J hIJ
  apply ConvergentResidualColonDimension.colon_krullDim_le_of_jet_length_bound
    (C := r * C * (c + 1) ^ d) I J hProper
  intro N
  have hLin : N + c + 1 ≤ (c + 1) * (N + 1) := by
    have hN : N ≤ (c + 1) * N := Nat.le_mul_of_pos_left N (by omega)
    calc
      N + c + 1 ≤ (c + 1) * N + c + 1 := by omega
      _ = (c + 1) * (N + 1) := by ring
  have hNat : r * (C * (N + c + 1) ^ d) ≤
      r * C * (c + 1) ^ d * (N + 1) ^ d := by
    calc
      r * (C * (N + c + 1) ^ d) ≤ r * C * ((c + 1) * (N + 1)) ^ d := by
        simpa only [mul_assoc] using
          Nat.mul_le_mul_left (r * C) (Nat.pow_le_pow_left hLin d)
      _ = r * C * (c + 1) ^ d * (N + 1) ^ d := by simp only [mul_pow, mul_assoc]
  exact (hc N).trans ((mul_le_mul_of_nonneg_left (hGrowth (N + c)) (zero_le : (0 : ℕ∞) ≤ (r : ℕ∞))).trans
    (by simpa only [Nat.cast_mul] using ENat.natCast_le_natCast.mpr hNat))

/-- The two explicit shifted length estimates imply dimension at most 61
for the proper actual colon quotient. In particular, neither estimate is
replaced by the desired module-growth conclusion as a new assumption. -/
theorem colon_krullDim_le_sixty_one_of_shifted_bounds {n : ℕ}
    (I J : Ideal (GermRing n)) (hIJ : I ≤ J)
    (hProper : (I : Submodule (GermRing n) (GermRing n)).colon
      (J : Set (GermRing n)) ≠ ⊤) (cu cl : ℕ)
    (hUpper : ∀ N : ℕ,
      Module.length (GermRing n) (ShiftedJetLength.QuotientIdealModule I J ⧸
        ((vanishingIdeal n ^ (N + 1)) •
          (⊤ : Submodule (GermRing n) (ShiftedJetLength.QuotientIdealModule I J)))) +
      Module.length (GermRing n) (GermRing n ⧸ (J ⊔ vanishingIdeal n ^ (N + cu + 1))) ≤
      ((4 * (N + cu + 62).choose 62 + 1540 * (N + cu + 61).choose 61 : ℕ) : ℕ∞))
    (hLower : ∀ N : ℕ, ((4 * (N + 62).choose 62 : ℕ) : ℕ∞) ≤
      Module.length (GermRing n) (GermRing n ⧸ (J ⊔ vanishingIdeal n ^ (N + cl + 1)))) :
    ringKrullDim (GermRing n ⧸ (I : Submodule (GermRing n) (GermRing n)).colon
      (J : Set (GermRing n))) ≤ (61 : WithBot ℕ∞) := by
  obtain ⟨C, hC⟩ := exists_quotientIdealModule_degree_sixty_one_bound
    I J hIJ cu cl hUpper hLower
  exact colon_krullDim_le_of_quotientIdealModule_growth I J hIJ hProper hC

end ConvergentResidualColonGrowth

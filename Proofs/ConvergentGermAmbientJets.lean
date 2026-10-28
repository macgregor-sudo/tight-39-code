module

public import ConvergentGermDerivatives
public import ConvergentResidualPointBinding
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Ideal

@[expose] public section

/-!
# The ambient polynomial-to-analytic jet kernel

First-party isolated proof, 2026-10-23. No outgoing project license is selected.
The hard direction differentiates actual analytic representatives and extracts
polynomial coefficients in characteristic zero. There is no assumed Taylor map,
jet equivalence, Noetherian instance or analytic/formal comparison.

Pinned Mathlib APIs: Algebra/MvPolynomial/PDeriv.lean::coeff_pderiv and
RingTheory/MvPolynomial/Ideal.lean::mem_pow_idealOfVars_iff', Apache-2.0,
commit 065356127b1dc0016f66b7283ce0ce2c4055aa55, Lean v4.35.0-rc2.
No upstream proof body is copied. Thank you to the Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

noncomputable section

namespace ConvergentGermAmbientJets

open ConvergentResidualJets ConvergentGermDerivatives ConvergentResidualPointBinding

/-- Coordinate differentiation of the actual polynomial germ is formal partial
differentiation of its polynomial representative. -/
theorem directionalDerivative_polynomialGerm {n : ℕ} (i : Fin n) (p : Poly n) :
    directionalDerivative (Pi.single i 1) (polynomialGerm n p) =
      polynomialGerm n (MvPolynomial.pderiv i p) := by
  classical
  have hX (j : Fin n) :
      directionalDerivative (Pi.single i 1) (polynomialGerm n (MvPolynomial.X j)) =
        polynomialGerm n (MvPolynomial.pderiv i (MvPolynomial.X j)) := by
    by_cases hji : j = i
    · subst j
      rw [MvPolynomial.pderiv_X_self, map_one]
      rw [polynomialGerm, MvPolynomial.aeval_X, directionalDerivative_coordinate]
      simp
    · rw [MvPolynomial.pderiv_X_of_ne hji, map_zero]
      rw [polynomialGerm, MvPolynomial.aeval_X, directionalDerivative_coordinate]
      simp [Pi.single_eq_of_ne hji]
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [MvPolynomial.pderiv_C, map_zero]
      rw [polynomialGerm, MvPolynomial.aeval_C]
      exact directionalDerivative_constant _ _
  | add p q hp hq =>
      simp only [map_add, directionalDerivative_add, hp, hq]
  | mul_X p j hp =>
      rw [map_mul, directionalDerivative_mul, hp, hX]
      simp only [MvPolynomial.pderiv_mul, map_add, map_mul]

/-- Vanishing constant coefficient and one-lower-order partial derivatives
force every polynomial coefficient below the next order to vanish. -/
theorem mem_variableIdeal_pow_succ_of_pderiv {n : ℕ} (p : Poly n) (d : ℕ)
    (hzero : p.coeff 0 = 0)
    (hderiv : ∀ i : Fin n, MvPolynomial.pderiv i p ∈ variableIdeal n ^ d) :
    p ∈ variableIdeal n ^ (d + 1) := by
  classical
  change p ∈ MvPolynomial.idealOfVars (Fin n) ℂ ^ (d + 1)
  apply (MvPolynomial.mem_pow_idealOfVars_iff' (d + 1) p).mpr
  intro a ha
  by_cases haz : a = 0
  · simpa only [haz] using hzero
  have hex : ∃ i : Fin n, a i ≠ 0 := by
    by_contra! h
    apply haz
    ext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  let b := a - Finsupp.single i 1
  have hba : b + Finsupp.single i 1 = a := Finsupp.sub_add_single_one_cancel hi
  have hdegree : Finsupp.degree b + 1 = Finsupp.degree a := by
    simpa only [map_add, Finsupp.degree_single] using congrArg Finsupp.degree hba
  have hb : Finsupp.degree b < d := by omega
  have hc : (MvPolynomial.pderiv i p).coeff b = 0 :=
    (MvPolynomial.mem_pow_idealOfVars_iff' d (MvPolynomial.pderiv i p)).mp
      (hderiv i) b hb
  rw [MvPolynomial.coeff_pderiv, hba] at hc
  apply (mul_eq_zero.mp hc).resolve_right
  exact_mod_cast Nat.succ_ne_zero (b i)

/-- Exact ambient finite-order membership, on the unchanged actual analytic
carrier and the unchanged polynomial and vanishing ideals. -/
theorem polynomialGerm_mem_vanishingIdeal_pow_iff {n : ℕ} (p : Poly n) (d : ℕ) :
    polynomialGerm n p ∈ vanishingIdeal n ^ d ↔ p ∈ variableIdeal n ^ d := by
  constructor
  · intro hp
    induction d generalizing p with
    | zero => simp
    | succ d ih =>
        apply mem_variableIdeal_pow_succ_of_pderiv p d
        · have hz : polynomialGerm n p ∈ vanishingIdeal n :=
            (Ideal.pow_le_self (Nat.succ_ne_zero d)) hp
          change evalAtZero n (polynomialGerm n p) = 0 at hz
          rw [evalAtZero_polynomialGerm, MvPolynomial.eval_zero,
            MvPolynomial.constantCoeff_eq] at hz
          exact hz
        · intro i
          apply ih
          rw [← directionalDerivative_polynomialGerm]
          exact directionalDerivative_mem_pow (Pi.single i 1) (vanishingIdeal n) d hp
  · intro hp
    have hm := Ideal.mem_map_of_mem (polynomialGerm n).toRingHom hp
    rw [Ideal.map_pow] at hm
    exact (pow_le_pow_left' (map_variableIdeal_le n) d) hm

/-- Contraction of the analytic maximal-ideal filtration recovers the exact
polynomial variable-ideal filtration, including order zero. -/
theorem comap_vanishingIdeal_pow (n d : ℕ) :
    Ideal.comap (polynomialGerm n).toRingHom (vanishingIdeal n ^ d) =
      variableIdeal n ^ d := by
  ext p
  exact polynomialGerm_mem_vanishingIdeal_pow_iff p d

end ConvergentGermAmbientJets

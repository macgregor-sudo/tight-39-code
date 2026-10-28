module

public import ThreeCycleNormalForm
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Dimension and resonance count of the original derivative kernel

The dimension is transported through the existing, unchanged real-linear
NormalForm. Exactly two resonances are excluded by the actual product-one
PhaseTriple condition, not by genericity or an additional phase hypothesis.
First-party proof; imported mathlib provenance unchanged. No release license assigned.
-/

@[expose] public section
noncomputable section

namespace UnitaryErrorBases.ThreeCycleMatrix

open scoped BigOperators

theorem normalForm_finrank (d : PhaseTriple) :
    Module.finrank ℝ (NormalForm d) = 18 + 2 * resonanceCount d := by
  classical
  simp only [NormalForm, Module.finrank_prod, Module.finrank_pi,
    Module.finrank_pi_fintype, Complex.finrank_real_complex,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, resonanceCount]
  omega

theorem firstOrder_finrank (d : PhaseTriple) :
    Module.finrank ℝ (firstOrderSpace (monomialFamily d)) =
      18 + 2 * resonanceCount d := by
  classical
  letI : FiniteDimensional ℝ (firstOrderSpace (monomialFamily d)) :=
    (firstOrderNormalForm d).symm.finiteDimensional
  exact (firstOrderNormalForm d).finrank_eq.trans (normalForm_finrank d)

theorem resonanceCount_eq_three_indicators (d : PhaseTriple) :
    resonanceCount d =
      (if d.val 0 ^ 3 = 1 then 1 else 0) +
      (if d.val 1 ^ 3 = 1 then 1 else 0) +
      (if d.val 2 ^ 3 = 1 then 1 else 0) := by
  classical
  calc
    resonanceCount d = ∑ k : Index, if d.val k ^ 3 = 1 then (1 : ℕ) else 0 := by
      simp only [resonanceCount, Fintype.card_subtype, Finset.sum_boole]
      rfl
    _ = _ := Fin.sum_univ_three _

theorem resonanceCount_zero_one_three (d : PhaseTriple) :
    resonanceCount d = 0 ∨ resonanceCount d = 1 ∨ resonanceCount d = 3 := by
  classical
  have hp : d.val 0 * d.val 1 * d.val 2 = 1 :=
    (Fin.prod_univ_three d.val).symm.trans d.property.2
  have hc : d.val 0 ^ 3 * d.val 1 ^ 3 * d.val 2 ^ 3 = 1 := by
    calc
      _ = (d.val 0 * d.val 1 * d.val 2) ^ 3 := by ring
      _ = 1 := by rw [hp, one_pow]
  rw [resonanceCount_eq_three_indicators]
  by_cases h₀ : d.val 0 ^ 3 = 1 <;>
    by_cases h₁ : d.val 1 ^ 3 = 1 <;>
    by_cases h₂ : d.val 2 ^ 3 = 1 <;> simp_all

/-- Exact dimension-and-resonance conclusion from the original Challenge. -/
theorem firstOrder_dimension_and_resonance (d : PhaseTriple) :
    Module.finrank ℝ (firstOrderSpace (monomialFamily d)) =
      18 + 2 * resonanceCount d ∧
    (resonanceCount d = 0 ∨ resonanceCount d = 1 ∨ resonanceCount d = 3) :=
  ⟨firstOrder_finrank d, resonanceCount_zero_one_three d⟩

end UnitaryErrorBases.ThreeCycleMatrix

module

public import Mathlib.Analysis.Polynomial.Basic

@[expose] public section

/-! The leading coefficient of an eventual Hilbert polynomial is determined
by a nonzero normalized length limit. This is only the polynomial comparison;
existence of the ordinary Hilbert-Samuel polynomial is a separate obligation.
First-party composition of the pinned Mathlib polynomial ratio-limit APIs;
no external proof body is copied. -/

noncomputable section
namespace Option2.NativeStress.HilbertSamuelPolynomialCoefficient
open Filter Polynomial
open scoped Topology

/-- A finite nonzero polynomial/power limit fixes its exact degree and
leading coefficient. No Hilbert polynomial existence is assumed implicitly. -/
theorem degree_and_leadingCoeff_of_normalized_limit
    (P : ℝ[X]) (d : ℕ) (L : ℝ) (hL : L ≠ 0)
    (h : Tendsto (fun n : ℕ => P.eval (n : ℝ) / (n : ℝ) ^ d) atTop (𝓝 L)) :
    P.degree = (d : WithBot ℕ) ∧ P.leadingCoeff = L := by
  have hdegree : P.degree = (X ^ d : ℝ[X]).degree := by
    rcases lt_trichotomy P.degree (X ^ d : ℝ[X]).degree with hlt | heq | hgt
    · have hz : Tendsto (fun n : ℕ => P.eval (n : ℝ) / (n : ℝ) ^ d)
          atTop (𝓝 (0 : ℝ)) := by
        simpa only [Function.comp_def, eval_pow, eval_X] using
          (P.div_tendsto_atTop_zero_of_degree_lt (X ^ d) hlt).comp
            tendsto_natCast_atTop_atTop
      exact (hL (tendsto_nhds_unique h hz)).elim
    · exact heq
    · have ht : Tendsto (fun n : ℕ => |P.eval (n : ℝ) / (n : ℝ) ^ d|)
          atTop atTop := by
        simpa only [Function.comp_def, eval_pow, eval_X] using
          (P.abs_div_tendsto_atTop_atTop_of_degree_gt (X ^ d) hgt
            (pow_ne_zero d X_ne_zero)).comp tendsto_natCast_atTop_atTop
      exact (not_tendsto_atTop_of_tendsto_nhds h.abs ht).elim
  refine ⟨by simpa only [degree_X_pow] using hdegree, ?_⟩
  have hc : Tendsto (fun n : ℕ => P.eval (n : ℝ) / (n : ℝ) ^ d)
      atTop (𝓝 P.leadingCoeff) := by
    simpa only [Function.comp_def, eval_pow, eval_X, leadingCoeff_X_pow, div_one] using
      (P.div_tendsto_atTop_leadingCoeff_div_of_degree_eq (X ^ d) hdegree).comp
        tendsto_natCast_atTop_atTop
  exact tendsto_nhds_unique hc h

/-- Eventual agreement retains the same degree and coefficient conclusion.
The eventual polynomial is an explicit input, not a definition by a limit. -/
theorem degree_and_leadingCoeff_of_eventual_polynomial
    (f : ℕ → ℝ) (P : ℝ[X]) (d : ℕ) (L : ℝ) (hL : L ≠ 0)
    (hp : ∀ᶠ n in atTop, f n = P.eval (n : ℝ))
    (h : Tendsto (fun n : ℕ => f n / (n : ℝ) ^ d) atTop (𝓝 L)) :
    P.degree = (d : WithBot ℕ) ∧ P.leadingCoeff = L := by
  apply degree_and_leadingCoeff_of_normalized_limit P d L hL
  apply h.congr'
  filter_upwards [hp] with n hn
  rw [hn]

#print axioms degree_and_leadingCoeff_of_normalized_limit
#print axioms degree_and_leadingCoeff_of_eventual_polynomial
end Option2.NativeStress.HilbertSamuelPolynomialCoefficient


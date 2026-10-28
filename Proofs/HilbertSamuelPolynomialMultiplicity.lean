module

public import HilbertSamuelPolynomialCoefficient
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Order.Interval.Set.Infinite

@[expose] public section

/-! Standard polynomial-defined multiplicity comparison. The existence of an
eventual rational polynomial remains explicit; a limit is not substituted for
that definition. First-party composition of named Mathlib polynomial APIs. -/

noncomputable section
namespace Option2.NativeStress.HilbertSamuelPolynomialCoefficient
open Filter Polynomial
open scoped Topology

/-- Ordinary Hilbert-Samuel normalization: if the length polynomial exists,
the normalized nonzero growth fixes degree and factorial-scaled coefficient. -/
theorem degree_and_factorial_leadingCoeff_of_eventual_nat_polynomial
    (f : ℕ → ℕ) (p : ℚ[X]) (d : ℕ) (e : ℚ) (he : e ≠ 0)
    (hp : ∀ᶠ n in atTop, (f n : ℚ) = p.eval (n : ℚ))
    (h : Tendsto (fun n : ℕ =>
      (d.factorial : ℝ) * (f n : ℝ) / (n : ℝ) ^ d) atTop (𝓝 (e : ℝ))) :
    p.degree = (d : WithBot ℕ) ∧ (d.factorial : ℚ) * p.leadingCoeff = e := by
  let P : ℝ[X] := p.map (algebraMap ℚ ℝ)
  have hfac : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he
  have heval : ∀ᶠ n in atTop, (f n : ℝ) = P.eval (n : ℝ) := by
    filter_upwards [hp] with n hn
    have hc := congrArg (algebraMap ℚ ℝ) hn
    simpa only [map_natCast, ← eval₂_at_apply, ← Polynomial.eval_map] using hc
  have hratio : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ) ^ d)
      atTop (𝓝 ((e : ℝ) / (d.factorial : ℝ))) := by
    simpa only [mul_div_assoc, mul_div_cancel_left₀ _ hfac] using
      h.div_const (d.factorial : ℝ)
  obtain ⟨hd, hc⟩ := degree_and_leadingCoeff_of_eventual_polynomial
    (fun n => (f n : ℝ)) P d ((e : ℝ) / (d.factorial : ℝ))
    (div_ne_zero heR hfac) heval hratio
  refine ⟨?_, ?_⟩
  · simpa only [P, Polynomial.degree_map] using hd
  · have hc' : (p.leadingCoeff : ℝ) = (e : ℝ) / (d.factorial : ℝ) := by
      have hm : algebraMap ℚ ℝ p.leadingCoeff = (p.leadingCoeff : ℝ) := by
        simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ ℝ) p.leadingCoeff
      simpa only [P, Polynomial.leadingCoeff_map, hm] using hc
    have hs : (d.factorial : ℝ) * (p.leadingCoeff : ℝ) = (e : ℝ) := by
      rw [hc', mul_div_cancel₀ _ hfac]
    exact_mod_cast hs

/-- Eventual agreement uniquely specifies the ordinary polynomial. -/
theorem eventual_nat_polynomial_unique (f : ℕ → ℕ) (p q : ℚ[X])
    (hp : ∀ᶠ n in atTop, (f n : ℚ) = p.eval (n : ℚ))
    (hq : ∀ᶠ n in atTop, (f n : ℚ) = q.eval (n : ℚ)) : p = q := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hp.and hq)
  apply Polynomial.eq_of_infinite_eval_eq
  apply ((Set.Ici_infinite N).image (f := fun n : ℕ => (n : ℚ))
    Nat.cast_injective.injOn).mono
  rintro x ⟨n, hn, rfl⟩
  exact (hN n hn).1.symm.trans (hN n hn).2

#print axioms degree_and_factorial_leadingCoeff_of_eventual_nat_polynomial
#print axioms eventual_nat_polynomial_unique
end Option2.NativeStress.HilbertSamuelPolynomialCoefficient


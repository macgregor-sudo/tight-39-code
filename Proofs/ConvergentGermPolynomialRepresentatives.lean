/-
The private shifted_series_factor proof adapts the mathematical implementation
of analyticAt_exists_sub_eq_linear in AbelFormalization/AnalyticHadamard.lean,
https://github.com/archernikov/abel-formalization at
acf1a5a138aa966e1380e4af3100e6c286d00fe6 (Apache-2.0).
Evidenced source credit: the archernikov/abel-formalization project; that
upstream file specifies no individual author or copyright holder.
Modifications: specialize to finite complex coordinate spaces; retain the
given convergent series and the exact shifted series; pass the resulting
first-order factorization to actual neighborhood germs. The polynomial
representative induction and quotient surjectivity below are newly authored.
The adapted portion retains Apache-2.0; its unchanged license text is
preserved in LICENSE.
Thank you to the Abel project and Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/
module

public import ConvergentResidualJetMap
public import Mathlib.Analysis.Normed.Group.Constructions

@[expose] public section

/-!
# Polynomial representatives of convergent germs

The analytic Hadamard decomposition iterates to polynomial representatives
modulo every power of the ideal of germs vanishing at zero. Consequently the
canonical map on jets is surjective for every residual ideal, without any
canonical choice of Taylor coefficients. Injectivity is a separate theorem.
Mathlib pin: 065356127b1dc0016f66b7283ce0ce2c4055aa55.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace ConvergentGermPolynomialRepresentatives

open ConvergentResidualJets

private theorem shifted_series_factor
    {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    {p : FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ}
    (hp : HasFPowerSeriesAt f p 0) :
    HasFPowerSeriesAt p.shift.sum p.shift 0 ∧
      ∀ᶠ x in 𝓝 (0 : Fin n → ℂ), f x - f 0 = p.shift.sum x x := by
  obtain ⟨r, hr⟩ := hp
  have hpos : 0 < p.shift.radius := by
    rw [FormalMultilinearSeries.radius_shift]
    exact hr.radius_pos
  have hs := p.shift.hasFPowerSeriesOnBall hpos
  refine ⟨hs.hasFPowerSeriesAt, ?_⟩
  filter_upwards [Metric.eball_mem_nhds (0 : Fin n → ℂ) hr.r_pos] with x hx
  have htail := (hasSum_nat_add_iff' 1).mpr (hr.hasSum hx)
  have hxShift : x ∈ Metric.eball (0 : Fin n → ℂ) p.shift.radius := by
    rw [FormalMultilinearSeries.radius_shift]
    exact Metric.eball_subset_eball hr.r_le hx
  have heval := (ContinuousLinearMap.apply ℂ ℂ x).hasSum (hs.hasSum hxShift)
  have hterm (k : ℕ) : p.shift k (fun _ => x) x = p (k+1) (fun _ => x) := by
    simp only [FormalMultilinearSeries.shift, ContinuousMultilinearMap.curryRight_apply]
    congr 1
    ext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
  simp only [Finset.sum_range_one, hr.coeff_zero, zero_add] at htail
  change HasSum (fun k => p.shift k (fun _ => x) x) (p.shift.sum (0+x) x) at heval
  simp only [hterm, zero_add] at heval
  exact htail.unique heval

/-- Analytic Hadamard decomposition in the ring of actual neighborhood germs. -/
theorem exists_eq_constant_add_sum_coordinate_mul {n : ℕ} (u : GermRing n) :
    ∃ h : Fin n → GermRing n,
      u = constant n (evalAtZero n u) + ∑ i, coordinate n i * h i := by
  classical
  obtain ⟨f, hf, heq⟩ := u.property
  have hu : u = ofAnalyticAt f hf := Subtype.ext heq.symm
  subst u
  obtain ⟨p, hp⟩ := hf
  obtain ⟨hs, hfactor⟩ := shifted_series_factor hp
  let g : Fin n → (Fin n → ℂ) → ℂ :=
    fun i x => p.shift.sum x (Pi.single i 1)
  have hg (i : Fin n) : AnalyticAt ℂ (g i) 0 := by
    obtain ⟨s, hs⟩ := hs
    exact (ContinuousLinearMap.apply ℂ ℂ
      (Pi.single i 1 : Fin n → ℂ)).comp_hasFPowerSeriesOnBall hs |>.analyticAt
  refine ⟨fun i => ofAnalyticAt (g i) (hg i), ?_⟩
  have hlinear (x : Fin n → ℂ) : p.shift.sum x x = ∑ i, x i * g i x := by
    have hx : x = ∑ i, x i • Pi.single i (1 : ℂ) := by
      ext j
      simp [Pi.single_apply]
    calc
      p.shift.sum x x = p.shift.sum x (∑ i, x i • Pi.single i (1 : ℂ)) :=
        congrArg (p.shift.sum x) hx
      _ = ∑ i, x i * g i x := by
        simp only [map_sum, map_smul, smul_eq_mul]
        rfl
  apply Subtype.ext
  simp only [Subring.coe_add, AddSubmonoidClass.coe_finsetSum]
  change (Filter.Germ.coeRingHom (𝓝 (0 : Fin n → ℂ))) f =
    (Filter.Germ.coeRingHom (𝓝 (0 : Fin n → ℂ))) (fun _ => f 0) +
      ∑ i, (Filter.Germ.coeRingHom (𝓝 (0 : Fin n → ℂ))) (fun x => x i * g i x)
  rw [← map_sum, ← map_add]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hfactor] with x hx
  simp only [Pi.add_apply, Finset.sum_apply]
  exact (sub_eq_iff_eq_add.mp (hx.trans (hlinear x))).trans (add_comm _ _)

/-- Every convergent germ has a polynomial representative modulo any ideal power. -/
theorem exists_polynomial_representative {n : ℕ} (u : GermRing n) (d : ℕ) :
    ∃ p : Poly n, u - polynomialGerm n p ∈ vanishingIdeal n ^ d := by
  classical
  induction d generalizing u with
  | zero => exact ⟨0, by simp⟩
  | succ d ih =>
    obtain ⟨h, hu⟩ := exists_eq_constant_add_sum_coordinate_mul u
    choose p hp using fun i => ih (h i)
    refine ⟨MvPolynomial.C (evalAtZero n u) + ∑ i, MvPolynomial.X i * p i, ?_⟩
    have heq : u - polynomialGerm n
        (MvPolynomial.C (evalAtZero n u) + ∑ i, MvPolynomial.X i * p i) =
        ∑ i, coordinate n i * (h i - polynomialGerm n (p i)) := by
      conv_lhs => lhs; rw [hu]
      simp only [map_add, map_sum, map_mul, polynomialGerm, MvPolynomial.aeval_C,
        MvPolynomial.aeval_X, Finset.sum_sub_distrib, mul_sub]
      change constant n (evalAtZero n u) + _ -
        (constant n (evalAtZero n u) + _) = _
      abel
    rw [heq, pow_succ']
    apply (vanishingIdeal n * vanishingIdeal n ^ d).sum_mem
    intro i hi
    apply Ideal.mul_mem_mul
    · change evalAtZero n (coordinate n i) = 0
      rfl
    · exact hp i

/-- The canonical map to analytic jets is surjective for the same residual ideal. -/
theorem jetMap_surjective {n : ℕ} (Q : Ideal (Poly n)) (N : ℕ) :
    Function.Surjective (jetMap Q N) := by
  intro z
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨p, hp⟩ := exists_polynomial_representative u (N+1)
  refine ⟨Ideal.Quotient.mk (polynomialJetIdeal Q N) p, ?_⟩
  rw [jetMap_mk, Ideal.Quotient.eq]
  apply (analyticJetIdeal Q N).neg_mem_iff.mp
  simpa only [neg_sub] using
    (show u - polynomialGerm n p ∈ analyticJetIdeal Q N from
      (show vanishingIdeal n ^ (N+1) ≤ analyticJetIdeal Q N from le_sup_right) hp)

end ConvergentGermPolynomialRepresentatives

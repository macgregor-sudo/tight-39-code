module

public import NativePhaseRank

@[expose] public section

/-! Algebraic all-column native Jacobian annihilation gives the actual analytic
stress-covector annihilation. No phase or solution hypothesis is required. -/

noncomputable section
namespace Option2.NativeStress.PhaseStressAnnihilationA6
open PhasePivotA6 PhaseRankA6 CKM.NativeFirstOrder
open NativePolynomial.PartialAction
open AnalyticDerivative
open scoped BigOperators

private theorem fderiv_originalF_apply_row (ξ : Fin 4 → ℂ)
    (v : RealConfiguration) (r : Fin 2184) :
    (fderiv ℝ AnalyticDerivative.originalF (literalCfg ξ) v) r =
      ∑ j, realJ ξ r j * pack v j := by
  rw [(hasFDerivAt_originalF (literalCfg ξ)).fderiv]
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    packCLM_apply, realJ, Matrix.of_apply, PolynomialJets.equationLinearMatrix,
    PolyCalcReal.translate_coeff_single]

/-- The weights annihilate every actual native column; the conclusion is the
full continuous real-linear derivative, tested on unrestricted ambient directions. -/
theorem native_jacobian_annihilation (ξ : Fin 4 → ℂ) (w : Fin 2184 → ℂ)
    (hann : ∀ j : Fin 1053, ∑ r : Fin 2184, w r * nativeJ ξ r j = 0) :
    (stressCovector w).comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg ξ)) = 0 := by
  classical
  have hJ (r : Fin 2184) (j : Fin 1053) : (realJ ξ r j : ℂ) = nativeJ ξ r j :=
    congrArg (fun A => A r j) (realJ_map_complex ξ)
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, zero_apply,
    stressCovector_apply, fderiv_originalF_apply_row, Complex.ofReal_sum,
    Complex.ofReal_mul, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  simp only [← mul_assoc, ← Finset.sum_mul, hann j, zero_mul]

end Option2.NativeStress.PhaseStressAnnihilationA6

module

public import OriginalFAnalyticDerivativeV2
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-!
# Smoothness of the literal original 2184-row real residual

This module imports the exact existing native map; it neither redefines its
rows nor expands their coefficients. Mathlib's polynomial analyticity theorem
and the literal coordinate projections supply every regularity order.
Ambient
smoothness alone supplies no reduced chart, sheet, cone or robustness result.
-/

namespace Option2.NativeStress.AnalyticDerivative

open NativePolynomial.PartialAction

/-- The actual complete original residual is smooth at every configuration.
In particular `originalF_contDiff 2` supplies its ambient C2 regularity. -/
theorem originalF_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n originalF := by
  have hpack : ContDiff ℝ n (fun C : RealConfiguration => pack C) := by
    apply contDiff_pi.mpr
    intro v
    change ContDiff ℝ n (fun C : Fin 39 → Fin 27 → ℝ =>
      C (⟨v.val / 27, by omega⟩ : Fin 39) (⟨v.val % 27, by omega⟩ : Fin 27))
    exact contDiff_apply_apply ℝ ℝ _ _
  apply contDiff_pi.mpr
  intro r
  change ContDiff ℝ n (fun C : RealConfiguration => MvPolynomial.eval (pack C)
    (NativePolynomial.ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r))
  have heval : ContDiff ℝ n (fun x : Fin 1053 → ℝ => MvPolynomial.eval x
      (NativePolynomial.ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r)) :=
    (AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℝ)
      (NativePolynomial.ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r)).contDiff
  exact heval.comp hpack

end Option2.NativeStress.AnalyticDerivative

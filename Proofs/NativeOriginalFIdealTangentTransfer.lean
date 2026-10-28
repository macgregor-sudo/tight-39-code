module

public import PolynomialIdealDifferentialKernels
public import NativeConfigurationTranslatedIdeal
public import NativeOriginalGAllRowsDifferential

@[expose] public section

/-!
The exact original F2184/G3159 ideal equality transfers their full first-order
kernels at the same original real zero. The point hypothesis is literal F-row
vanishing and is retained explicitly; original G-row vanishing is derived.
The original all-column translated matrices and actual native operations are
unchanged. No actual base point, lift, chart or geometric tangent is supplied.
First-party composition of the accepted ideal equality and native G endpoint.
-/

noncomputable section

namespace NativePolynomial.ConfigurationResiduals.FirstCoefficients

open scoped BigOperators
open ConfigurationResidualIndices CoordinateMaps PolynomialJets
open NativePolynomial.ConfigurationResiduals.MixedCoefficients
open PolynomialIdealDifferentialKernels

/-- At the same actual original F zero, the full original F and G centered
linear matrices have equal kernels, with all 1053 columns retained. -/
theorem original_fRows_linearMatrix_zero_iff_gRows
    (p u : Fin 1053 → ℝ)
    (hPoint : ∀ r : Fin 2184, MvPolynomial.eval p (fRow (1/2 : ℝ) (1/3 : ℝ) r) = 0) :
    (∀ r : Fin 2184, (∑ n : Fin 1053,
      equationLinearMatrix
        (fun s : Fin 2184 => translate p (fRow (1/2 : ℝ) (1/3 : ℝ) s)) r n * u n) = 0) ↔
      (∀ r : Fin 3159, (∑ n : Fin 1053,
        equationLinearMatrix
          (fun s : Fin 3159 => translate p (gRow (1/2 : ℝ) (1/3 : ℝ) s)) r n * u n) = 0) := by
  have hIdeal : Ideal.span (Set.range (fRow (1/2 : ℝ) (1/3 : ℝ))) =
      Ideal.span (Set.range (gRow (1/2 : ℝ) (1/3 : ℝ))) :=
    fIdeal_eq_gSpan (1/2 : ℝ) (1/3 : ℝ) (by norm_num) (by norm_num)
  exact equal_span_linearMatrix_zero_iff
    (fRow (1/2 : ℝ) (1/3 : ℝ)) (gRow (1/2 : ℝ) (1/3 : ℝ)) hIdeal p u hPoint
    (eval_eq_zero_of_equal_span _ _ hIdeal p hPoint)

/-- Full original F tangent binding at its actual zero, obtained from exact
ideal equality rather than 2184 separate first-row calculations. -/
theorem original_all_fRows_linearMatrix_zero_iff_native
    (p u : Fin 1053 → ℝ)
    (hPoint : ∀ r : Fin 2184, MvPolynomial.eval p (fRow (1/2 : ℝ) (1/3 : ℝ) r) = 0) :
    (∀ r : Fin 2184, (∑ n : Fin 1053,
      equationLinearMatrix
        (fun s : Fin 2184 => translate p (fRow (1/2 : ℝ) (1/3 : ℝ) s)) r n * u n) = 0) ↔
      ((∀ i : Fin 39, (2 : ℝ) • Glennie.jordan
        (fromUpperCoordinates (pointValues p i))
        (fromUpperCoordinates (pointValues u i)) =
          fromUpperCoordinates (pointValues u i)) ∧
      (∀ (f : Fin 13) (s : Fin 3),
        let a : Fin 39 := framePointIndex f (withinPair s).val.1
        let b : Fin 39 := framePointIndex f (withinPair s).val.2
        Glennie.jordan (fromUpperCoordinates (pointValues p a))
          (fromUpperCoordinates (pointValues u b)) +
        Glennie.jordan (fromUpperCoordinates (pointValues u a))
          (fromUpperCoordinates (pointValues p b)) = 0) ∧
      (∀ f : Fin 13,
        (∑ a : Fin 3, fromUpperCoordinates (pointValues u (framePointIndex f a))) = 0) ∧
      (∀ (fg : Pair 13) (a b : Fin 3),
        let i : Fin 39 := framePointIndex fg.val.1 a
        let j : Fin 39 := framePointIndex fg.val.2 b
        Glennie.trace (Glennie.jordan
          (fromUpperCoordinates (pointValues p i))
          (fromUpperCoordinates (pointValues u j))) +
        Glennie.trace (Glennie.jordan
          (fromUpperCoordinates (pointValues u i))
          (fromUpperCoordinates (pointValues p j))) = 0)) :=
  (original_fRows_linearMatrix_zero_iff_gRows p u hPoint).trans
    (original_all_gRows_linearMatrix_zero_iff_native p u)

end NativePolynomial.ConfigurationResiduals.FirstCoefficients

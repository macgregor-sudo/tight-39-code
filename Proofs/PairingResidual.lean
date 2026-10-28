module
public import PairingDefinitions
public import OriginalFAnalyticDerivativeV2
public import NativeOriginalGIdempotencyDifferential
public import TCDefs
@[expose] public section

noncomputable section

/- The compact statement definitions are identical to ResidualDefinitions.lean.
Native ConfigurationResidualIndices is imported instead of redeclared here. -/
namespace Option2StatementResidual
open scoped BigOperators
open ConfigurationResidualIndices
open NativePolynomial CKM.NativeTightCode

theorem originalF_eq_native (C : Configuration) :
    originalF C = Option2.NativeStress.AnalyticDerivative.originalF C := by
  funext r
  unfold originalF Option2.NativeStress.AnalyticDerivative.originalF
  rw [NativePolynomial.PartialAction.eval_fRow]
  rcases ConfigurationResidualIndices.fNumber.symm r with ⟨i, k⟩ | i | ⟨f, k⟩ | ij
  · change upperCoordinates (Glennie.jordan (codePoint C i) (codePoint C i)) k - C i k =
      NativePolynomial.CoordinateMaps.coordinateProduct (1/2 : ℝ) (C i) (C i) k - C i k
    rw [NativePolynomial.CoordinateMaps.coordinateProduct_real_eq_native_coordinates
      (1/2 : ℝ) (by norm_num)]
    rfl
  · exact congrArg (fun t : ℝ => t - 1)
      (NativePolynomial.CoordinateMaps.coordinateTrace_apply (C i)).symm
  · rfl
  · simp [originalValue, NativePolynomial.PartialAction.originalValue,
      NativePolynomial.CoordinateMaps.coordinatePairing,
      NativePolynomial.IntegralStructureConstants.coordinateTraceWeight]

end Option2StatementResidual

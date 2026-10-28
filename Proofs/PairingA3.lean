module
public import PairingDefinitions
public import A3Main
public import PairingResidual
@[expose] public section
noncomputable section

namespace Option2StatementA3
open CKM.NativeFirstOrder
open scoped BigOperators

/- Count all signed native anchor resonances, including resonant unit phases. -/
end Option2StatementA3

namespace Option2StatementA3
open CKM.NativeFirstOrder
open scoped BigOperators

/- Actual original-row derivative dimension for every unit phase, with no
GoodPhase hypothesis and no removal of resonant phases. This does not replace
the separate unrestricted nine-matrix first-order normal-form clause. -/
theorem finrank_original_derivative_kernel (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ
      (LinearMap.ker (fderiv ℝ Option2StatementResidual.originalF (literalCfg ξ)).toLinearMap) =
      80 + 2 * ∑ H : Fin 4, resonanceCount ξ H := by
  have hf : Option2StatementResidual.originalF =
      Option2.NativeStress.AnalyticDerivative.originalF :=
    funext Option2StatementResidual.originalF_eq_native
  rw [hf]
  exact finrank_tangentSpace ξ hξ

end Option2StatementA3

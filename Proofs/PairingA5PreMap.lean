module
public import PairingDefinitions
public import PairingA5PreCfg
@[expose] public section

noncomputable section
/- Exact finite-dimensional chart data and germ conventions, inline fragment.
 Requires Mathlib.Analysis.Normed.Algebra.MatrixExponential. These definitions
 do not specify the four native branches or their chosen slice map. -/
namespace Option2StatementA5
open Complex Filter Topology
open scoped Matrix BigOperators

end Option2StatementA5

/- Exact phase-chart and eighteen-parameter anchored family constructors.
Requires the checked A5PreCfgDefinitions and A5ChartDefinitions fragments. -/
namespace Option2StatementA5Anchor
open CKM.NativeFirstOrder Option2StatementA5
open scoped BigOperators

end Option2StatementA5Anchor

namespace Option2StatementA5Anchor
open CKM.NativeFirstOrder

theorem anchorTriple_eq_native (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    anchorTriple ξ hξ H = CKM.NativeFirstOrder.anchorTriple ξ hξ H := rfl

theorem torusPhase_eq_native (d : PhaseTriple) (e : Fin 2 → ℝ) :
    torusPhase d e = CKM.NativeFourFamily.torusPhase d e := rfl

theorem preMap_eq_native (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) (p : PreParam) :
    preMap ξ hξ H p = CKM.NativeFourFamily.preMap ξ hξ H p := rfl

#print axioms preMap_eq_native
end Option2StatementA5Anchor

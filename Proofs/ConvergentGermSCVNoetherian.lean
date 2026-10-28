/-
First-party isolated Noetherian transfer prototype, 2026-10-23.
No outgoing project license is selected here. The sole Noetherian input is the
source-proved SCV finite-coordinate theorem imported below, including its actual
analytic Weierstrass proof closure. No unproved instance or comparison axiom.
-/
module

public import ConvergentGermSCVBridge
public import SeveralComplexVariables.AnalyticGerm.Noetherian

@[expose] public section

namespace ConvergentGermSCVBridge

open ConvergentResidualJets

/-- Noetherianity of the unchanged accepted analytic-representative germ ring. -/
theorem germRing_isNoetherianRing (n : ℕ) : IsNoetherianRing (GermRing n) := by
  letI : IsNoetherianRing
      (SeveralComplexVariables.AnalyticGerm ℂ (0 : Fin n → ℂ)) :=
    SeveralComplexVariables.AnalyticGerm.isNoetherianRing_coordinates n
  exact isNoetherianRing_of_ringEquiv _ (germEquiv n).symm.toRingEquiv

end ConvergentGermSCVBridge

module

public import NativeHEquilibriumCore

@[expose] public section

namespace Option2.NativeStress.NativeH.Equilibrium

open NativePolynomial.ConfigurationResiduals

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Bounded complete point block: every original coordinate, not a selected sample. -/
theorem h00_point0_fast :
    ∀ k : Fin 27, fastContraction (rawEntries 0 0) (hSpec 0 0)
      (Q12.lit 1 0 0 0 2) baseQ12 (variableIndex 0 k) = 0 := by
  intro k
  fin_cases k <;> decide +kernel

theorem h00_point1_fast :
    ∀ k : Fin 27, fastContraction (rawEntries 0 0) (hSpec 0 0)
      (Q12.lit 1 0 0 0 2) baseQ12 (variableIndex 1 k) = 0 := by
  intro k
  fin_cases k <;> decide +kernel

end Option2.NativeStress.NativeH.Equilibrium

#print axioms Option2.NativeStress.NativeH.Equilibrium.h00_point0_fast
#print axioms Option2.NativeStress.NativeH.Equilibrium.h00_point1_fast

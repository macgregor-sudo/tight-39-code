module

public import NativeHEquilibriumTransport
public import NativeHZeroSkipping
public import NativeHPointCancellation

@[expose] public section

namespace Option2.NativeStress.NativeH.Equilibrium

open NativePolynomial.ConfigurationResiduals

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Every coordinate of all12 anchor points for the actual H00 component. -/
theorem h00_all_anchor_fast :
    ∀ (p : Fin 12) (k : Fin 27), fastContraction (rawEntries 0 0) (hSpec 0 0)
      (Q12.lit 1 0 0 0 2) baseQ12
        (variableIndex ⟨p.val, by omega⟩ k) = 0 := by
  intro p
  fin_cases p
  · exact h00_point0_fast
  · exact h00_point1_fast
  all_goals
    intro k
    rw [← sparseContraction_eq]
    fin_cases k <;> decide +kernel

end Option2.NativeStress.NativeH.Equilibrium

#print axioms Option2.NativeStress.NativeH.Equilibrium.h00_all_anchor_fast

module

public import NativeHZeroSkipping
public import NativeHAnchorEnumeration

@[expose] public section

namespace Option2.NativeStress.NativeH.Equilibrium

open NativePolynomial.ConfigurationResiduals
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- All324 anchor coordinates for the actual phased H30 component. -/
theorem h30_all_anchor_fast :
    ∀ (p : Fin 12) (k : Fin 27), fastContraction (rawEntries 3 0) (hSpec 3 0)
      (Q12.lit 1 0 0 0 2) baseQ12 (variableIndex (anchorPoint 3 p) k) = 0 := by
  intro p k
  rw [← sparseContraction_eq]
  fin_cases p <;> fin_cases k <;> decide +kernel

end Option2.NativeStress.NativeH.Equilibrium

#print axioms Option2.NativeStress.NativeH.Equilibrium.h30_all_anchor_fast

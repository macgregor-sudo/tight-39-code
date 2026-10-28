module

public import NativeHZeroSkipping
public import NativeHAnchorEnumeration

@[expose] public section

namespace Option2.NativeStress.NativeH.Equilibrium

open NativePolynomial.ConfigurationResiduals
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Every original coordinate of the actual twelve anchors for H32. -/
theorem h32_all_anchor_fast :
    ∀ (p : Fin 12) (k : Fin 27), fastContraction (rawEntries 3 2) (hSpec 3 2)
      (Q12.lit 1 0 0 0 2) baseQ12 (variableIndex (anchorPoint 3 p) k) = 0 := by
  intro p k
  rw [← sparseContraction_eq]
  fin_cases p <;> fin_cases k <;> decide +kernel

end Option2.NativeStress.NativeH.Equilibrium

#print axioms Option2.NativeStress.NativeH.Equilibrium.h32_all_anchor_fast

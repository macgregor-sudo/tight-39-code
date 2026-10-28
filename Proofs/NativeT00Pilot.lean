module

public import NativeTData00
public import NativeHZeroSkipping

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT
open NativeH NativeH.Equilibrium NativePolynomial.ConfigurationResiduals

/-- The actual first T representative, all27 coordinates at native point0. -/
theorem t00_point0 : ∀ k : Fin 27,
    fastContraction lambda42 ⟨42, false, false⟩
      (Q12.lit 1 0 0 0 2) baseQ12 (variableIndex 0 k) = 0 := by
  intro k
  rw [← sparseContraction_eq]
  fin_cases k <;> decide +kernel

end Option2.NativeStress.NativeT
#check Option2.NativeStress.NativeT.t00_point0
#print axioms Option2.NativeStress.NativeT.t00_point0

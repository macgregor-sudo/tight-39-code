module

public import NativeTData00
public import NativeHZeroSkipping

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT
open NativeH NativeH.Equilibrium NativePolynomial.ConfigurationResiduals

theorem t00_block2 : ∀ (p : Fin 6) (k : Fin 27),
    fastContraction lambda42 ⟨42, false, false⟩ (Q12.lit 1 0 0 0 2) baseQ12
      (variableIndex (![15,16,17,18,19,20] p) k) = 0 := by
  intro p k
  rw [← sparseContraction_eq]
  fin_cases p <;> fin_cases k <;> decide +kernel

end Option2.NativeStress.NativeT
#print axioms Option2.NativeStress.NativeT.t00_block2

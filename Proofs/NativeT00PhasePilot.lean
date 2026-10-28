module

public import NativeT00Pilot

@[expose] public section

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Option2.NativeStress.NativeT
open NativeH NativeH.Equilibrium NativePolynomial.ConfigurationResiduals

theorem t00_point1 : ∀ k : Fin 27,
    fastContraction lambda42 ⟨42, false, false⟩
      (Q12.lit 1 0 0 0 2) baseQ12 (variableIndex 1 k) = 0 := by
  intro k
  rw [← sparseContraction_eq]
  fin_cases k <;> decide +kernel

theorem t00_point12 : ∀ k : Fin 27,
    fastContraction lambda42 ⟨42, false, false⟩
      (Q12.lit 1 0 0 0 2) baseQ12 (variableIndex 12 k) = 0 := by
  intro k
  rw [← sparseContraction_eq]
  fin_cases k <;> decide +kernel

theorem t00_point30 : ∀ k : Fin 27,
    fastContraction lambda42 ⟨42, false, false⟩
      (Q12.lit 1 0 0 0 2) baseQ12 (variableIndex 30 k) = 0 := by
  intro k
  rw [← sparseContraction_eq]
  fin_cases k <;> decide +kernel

end Option2.NativeStress.NativeT
#print axioms Option2.NativeStress.NativeT.t00_point1
#print axioms Option2.NativeStress.NativeT.t00_point12
#print axioms Option2.NativeStress.NativeT.t00_point30

module

public import HTPhaseKronStates00

@[expose] public section

/-! T00 phased-equilibrium column checks, states 21–23. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 200
namespace Option2.NativeStress.HTPhaseKron

theorem c00_21_0 : okRange (covAt00 21) (27 * 21 + 0) 9 = true := by decide +kernel
theorem c00_21_1 : okRange (covAt00 21) (27 * 21 + 9) 9 = true := by decide +kernel
theorem c00_21_2 : okRange (covAt00 21) (27 * 21 + 18) 9 = true := by decide +kernel
theorem c00_22_0 : okRange (covAt00 22) (27 * 22 + 0) 9 = true := by decide +kernel
theorem c00_22_1 : okRange (covAt00 22) (27 * 22 + 9) 9 = true := by decide +kernel
theorem c00_22_2 : okRange (covAt00 22) (27 * 22 + 18) 9 = true := by decide +kernel
theorem c00_23_0 : okRange (covAt00 23) (27 * 23 + 0) 9 = true := by decide +kernel
theorem c00_23_1 : okRange (covAt00 23) (27 * 23 + 9) 9 = true := by decide +kernel
theorem c00_23_2 : okRange (covAt00 23) (27 * 23 + 18) 9 = true := by decide +kernel

end Option2.NativeStress.HTPhaseKron

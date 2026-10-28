module

public import HTPhaseKronStates00

@[expose] public section

/-! T00 phased-equilibrium column checks, states 12–14. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 200
namespace Option2.NativeStress.HTPhaseKron

theorem c00_12_0 : okRange (covAt00 12) (27 * 12 + 0) 9 = true := by decide +kernel
theorem c00_12_1 : okRange (covAt00 12) (27 * 12 + 9) 9 = true := by decide +kernel
theorem c00_12_2 : okRange (covAt00 12) (27 * 12 + 18) 9 = true := by decide +kernel
theorem c00_13_0 : okRange (covAt00 13) (27 * 13 + 0) 9 = true := by decide +kernel
theorem c00_13_1 : okRange (covAt00 13) (27 * 13 + 9) 9 = true := by decide +kernel
theorem c00_13_2 : okRange (covAt00 13) (27 * 13 + 18) 9 = true := by decide +kernel
theorem c00_14_0 : okRange (covAt00 14) (27 * 14 + 0) 9 = true := by decide +kernel
theorem c00_14_1 : okRange (covAt00 14) (27 * 14 + 9) 9 = true := by decide +kernel
theorem c00_14_2 : okRange (covAt00 14) (27 * 14 + 18) 9 = true := by decide +kernel

end Option2.NativeStress.HTPhaseKron

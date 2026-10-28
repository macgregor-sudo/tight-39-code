module

public import HTPhaseKronStates00

@[expose] public section

/-! T00 phased-equilibrium column checks, states 15–17. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 200
namespace Option2.NativeStress.HTPhaseKron

theorem c00_15_0 : okRange (covAt00 15) (27 * 15 + 0) 9 = true := by decide +kernel
theorem c00_15_1 : okRange (covAt00 15) (27 * 15 + 9) 9 = true := by decide +kernel
theorem c00_15_2 : okRange (covAt00 15) (27 * 15 + 18) 9 = true := by decide +kernel
theorem c00_16_0 : okRange (covAt00 16) (27 * 16 + 0) 9 = true := by decide +kernel
theorem c00_16_1 : okRange (covAt00 16) (27 * 16 + 9) 9 = true := by decide +kernel
theorem c00_16_2 : okRange (covAt00 16) (27 * 16 + 18) 9 = true := by decide +kernel
theorem c00_17_0 : okRange (covAt00 17) (27 * 17 + 0) 9 = true := by decide +kernel
theorem c00_17_1 : okRange (covAt00 17) (27 * 17 + 9) 9 = true := by decide +kernel
theorem c00_17_2 : okRange (covAt00 17) (27 * 17 + 18) 9 = true := by decide +kernel

end Option2.NativeStress.HTPhaseKron

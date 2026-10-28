module

public import HTPhaseKronStates00

@[expose] public section

/-! T00 phased-equilibrium column checks, states 24–26. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 200
namespace Option2.NativeStress.HTPhaseKron

theorem c00_24_0 : okRange (covAt00 24) (27 * 24 + 0) 9 = true := by decide +kernel
theorem c00_24_1 : okRange (covAt00 24) (27 * 24 + 9) 9 = true := by decide +kernel
theorem c00_24_2 : okRange (covAt00 24) (27 * 24 + 18) 9 = true := by decide +kernel
theorem c00_25_0 : okRange (covAt00 25) (27 * 25 + 0) 9 = true := by decide +kernel
theorem c00_25_1 : okRange (covAt00 25) (27 * 25 + 9) 9 = true := by decide +kernel
theorem c00_25_2 : okRange (covAt00 25) (27 * 25 + 18) 9 = true := by decide +kernel
theorem c00_26_0 : okRange (covAt00 26) (27 * 26 + 0) 9 = true := by decide +kernel
theorem c00_26_1 : okRange (covAt00 26) (27 * 26 + 9) 9 = true := by decide +kernel
theorem c00_26_2 : okRange (covAt00 26) (27 * 26 + 18) 9 = true := by decide +kernel

end Option2.NativeStress.HTPhaseKron

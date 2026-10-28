module

public import HTPhaseKronStates00

@[expose] public section

/-! T00 phased-equilibrium column checks, states 30–32. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 200
namespace Option2.NativeStress.HTPhaseKron

theorem c00_30_0 : okRange (covAt00 30) (27 * 30 + 0) 9 = true := by decide +kernel
theorem c00_30_1 : okRange (covAt00 30) (27 * 30 + 9) 9 = true := by decide +kernel
theorem c00_30_2 : okRange (covAt00 30) (27 * 30 + 18) 9 = true := by decide +kernel
theorem c00_31_0 : okRange (covAt00 31) (27 * 31 + 0) 9 = true := by decide +kernel
theorem c00_31_1 : okRange (covAt00 31) (27 * 31 + 9) 9 = true := by decide +kernel
theorem c00_31_2 : okRange (covAt00 31) (27 * 31 + 18) 9 = true := by decide +kernel
theorem c00_32_0 : okRange (covAt00 32) (27 * 32 + 0) 9 = true := by decide +kernel
theorem c00_32_1 : okRange (covAt00 32) (27 * 32 + 9) 9 = true := by decide +kernel
theorem c00_32_2 : okRange (covAt00 32) (27 * 32 + 18) 9 = true := by decide +kernel

end Option2.NativeStress.HTPhaseKron

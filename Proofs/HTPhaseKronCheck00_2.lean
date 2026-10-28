module

public import HTPhaseKronStates00

@[expose] public section

/-! T00 phased-equilibrium column checks, states 18–20. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 200
namespace Option2.NativeStress.HTPhaseKron

theorem c00_18_0 : okRange (covAt00 18) (27 * 18 + 0) 9 = true := by decide +kernel
theorem c00_18_1 : okRange (covAt00 18) (27 * 18 + 9) 9 = true := by decide +kernel
theorem c00_18_2 : okRange (covAt00 18) (27 * 18 + 18) 9 = true := by decide +kernel
theorem c00_19_0 : okRange (covAt00 19) (27 * 19 + 0) 9 = true := by decide +kernel
theorem c00_19_1 : okRange (covAt00 19) (27 * 19 + 9) 9 = true := by decide +kernel
theorem c00_19_2 : okRange (covAt00 19) (27 * 19 + 18) 9 = true := by decide +kernel
theorem c00_20_0 : okRange (covAt00 20) (27 * 20 + 0) 9 = true := by decide +kernel
theorem c00_20_1 : okRange (covAt00 20) (27 * 20 + 9) 9 = true := by decide +kernel
theorem c00_20_2 : okRange (covAt00 20) (27 * 20 + 18) 9 = true := by decide +kernel

end Option2.NativeStress.HTPhaseKron

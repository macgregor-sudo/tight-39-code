module

public import HTPhaseKronStates00

@[expose] public section

/-! T00 phased-equilibrium column checks, states 33–35. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 200
namespace Option2.NativeStress.HTPhaseKron

theorem c00_33_0 : okRange (covAt00 33) (27 * 33 + 0) 9 = true := by decide +kernel
theorem c00_33_1 : okRange (covAt00 33) (27 * 33 + 9) 9 = true := by decide +kernel
theorem c00_33_2 : okRange (covAt00 33) (27 * 33 + 18) 9 = true := by decide +kernel
theorem c00_34_0 : okRange (covAt00 34) (27 * 34 + 0) 9 = true := by decide +kernel
theorem c00_34_1 : okRange (covAt00 34) (27 * 34 + 9) 9 = true := by decide +kernel
theorem c00_34_2 : okRange (covAt00 34) (27 * 34 + 18) 9 = true := by decide +kernel
theorem c00_35_0 : okRange (covAt00 35) (27 * 35 + 0) 9 = true := by decide +kernel
theorem c00_35_1 : okRange (covAt00 35) (27 * 35 + 9) 9 = true := by decide +kernel
theorem c00_35_2 : okRange (covAt00 35) (27 * 35 + 18) 9 = true := by decide +kernel

end Option2.NativeStress.HTPhaseKron

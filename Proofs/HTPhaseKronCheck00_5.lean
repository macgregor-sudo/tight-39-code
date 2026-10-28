module

public import HTPhaseKronStates00

@[expose] public section

/-! T00 phased-equilibrium column checks, states 27–29. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 200
namespace Option2.NativeStress.HTPhaseKron

theorem c00_27_0 : okRange (covAt00 27) (27 * 27 + 0) 9 = true := by decide +kernel
theorem c00_27_1 : okRange (covAt00 27) (27 * 27 + 9) 9 = true := by decide +kernel
theorem c00_27_2 : okRange (covAt00 27) (27 * 27 + 18) 9 = true := by decide +kernel
theorem c00_28_0 : okRange (covAt00 28) (27 * 28 + 0) 9 = true := by decide +kernel
theorem c00_28_1 : okRange (covAt00 28) (27 * 28 + 9) 9 = true := by decide +kernel
theorem c00_28_2 : okRange (covAt00 28) (27 * 28 + 18) 9 = true := by decide +kernel
theorem c00_29_0 : okRange (covAt00 29) (27 * 29 + 0) 9 = true := by decide +kernel
theorem c00_29_1 : okRange (covAt00 29) (27 * 29 + 9) 9 = true := by decide +kernel
theorem c00_29_2 : okRange (covAt00 29) (27 * 29 + 18) 9 = true := by decide +kernel

end Option2.NativeStress.HTPhaseKron

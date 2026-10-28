module

public import HTPhaseKronStates00

@[expose] public section

/-! T00 phased-equilibrium column checks, states 36–38. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 200
namespace Option2.NativeStress.HTPhaseKron

theorem c00_36_0 : okRange (covAt00 36) (27 * 36 + 0) 9 = true := by decide +kernel
theorem c00_36_1 : okRange (covAt00 36) (27 * 36 + 9) 9 = true := by decide +kernel
theorem c00_36_2 : okRange (covAt00 36) (27 * 36 + 18) 9 = true := by decide +kernel
theorem c00_37_0 : okRange (covAt00 37) (27 * 37 + 0) 9 = true := by decide +kernel
theorem c00_37_1 : okRange (covAt00 37) (27 * 37 + 9) 9 = true := by decide +kernel
theorem c00_37_2 : okRange (covAt00 37) (27 * 37 + 18) 9 = true := by decide +kernel
theorem c00_38_0 : okRange (covAt00 38) (27 * 38 + 0) 9 = true := by decide +kernel
theorem c00_38_1 : okRange (covAt00 38) (27 * 38 + 9) 9 = true := by decide +kernel
theorem c00_38_2 : okRange (covAt00 38) (27 * 38 + 18) 9 = true := by decide +kernel

end Option2.NativeStress.HTPhaseKron

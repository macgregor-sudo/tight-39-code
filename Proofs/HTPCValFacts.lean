module

public import HTPCValEng

@[expose] public section

/-! Global kernel facts of the value engine (first-party). -/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace Option2.NativeStress.HTPhaseComplete.ValEng

theorem baseOK_eq : baseOK = true := by decide +kernel
theorem closureOK_eq : closureOK = true := by decide +kernel
theorem kPosOK_eq : kPosOK = true := by decide +kernel

end Option2.NativeStress.HTPhaseComplete.ValEng

#print axioms Option2.NativeStress.HTPhaseComplete.ValEng.baseOK_eq
#print axioms Option2.NativeStress.HTPhaseComplete.ValEng.closureOK_eq
#print axioms Option2.NativeStress.HTPhaseComplete.ValEng.kPosOK_eq

module

public import A6LinChecks

@[expose] public section

/-!
# Lane LIN: validity of the packed data

Kernel runs (`decide +kernel`) of the Boolean checks; one declaration per block keeps kernel memory small.
First-party code.
-/

namespace A6Compact.LinRun

open A6Compact.LinCheck

theorem validW_ok : validW = true := by decide +kernel
theorem validB_ok : validB = true := by decide +kernel
theorem validL_ok : validL = true := by decide +kernel
theorem validLU_ok : validLU = true := by decide +kernel
theorem validColPos_ok : validColPos = true := by decide +kernel
theorem pivotOK_ok : pivotOK = true := by decide +kernel

end A6Compact.LinRun

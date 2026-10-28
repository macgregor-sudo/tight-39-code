module

public import A6LinChecks

@[expose] public section

/-!
# Lane LIN: D4 checks `A = Lo · U` row by row (973 minor rows, blocks of 325)

Kernel runs (`decide +kernel`) of the Boolean checks; one declaration per block keeps kernel memory small.
First-party code.
-/

namespace A6Compact.LinRun

open A6Compact.LinCheck

theorem d4_0 : (List.range' 0 325).all d4CheckT = true := by decide +kernel
theorem d4_1 : (List.range' 325 324).all d4CheckT = true := by decide +kernel
theorem d4_2 : (List.range' 649 324).all d4CheckT = true := by decide +kernel

/-- Collection of the blocks (no kernel evaluation). -/
theorem d4_range (n : ℕ) (h1 : 0 ≤ n) (h2 : n < 973) : d4CheckT n = true := by
  by_cases hb0 : n < 325
  · exact A6Compact.LinCheck.all_range'_of d4_0 n (by omega) hb0
  by_cases hb1 : n < 649
  · exact A6Compact.LinCheck.all_range'_of d4_1 n (by omega) hb1
  exact A6Compact.LinCheck.all_range'_of d4_2 n (by omega) (by omega)

end A6Compact.LinRun

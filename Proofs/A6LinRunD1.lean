module

public import A6LinChecks

@[expose] public section

/-!
# Lane LIN: D1 checks `w_s · L_p ≡ 0` (48 annihilators, blocks of 12)

Kernel runs (`decide +kernel`) of the Boolean checks; one declaration per block keeps kernel memory small.
First-party code.
-/

namespace A6Compact.LinRun

open A6Compact.LinCheck

theorem d1_0 : (List.range' 0 12).all d1CheckT = true := by decide +kernel
theorem d1_1 : (List.range' 12 12).all d1CheckT = true := by decide +kernel
theorem d1_2 : (List.range' 24 12).all d1CheckT = true := by decide +kernel
theorem d1_3 : (List.range' 36 12).all d1CheckT = true := by decide +kernel

/-- Collection of the blocks (no kernel evaluation). -/
theorem d1_range (n : ℕ) (h1 : 0 ≤ n) (h2 : n < 48) : d1CheckT n = true := by
  by_cases hb0 : n < 12
  · exact A6Compact.LinCheck.all_range'_of d1_0 n (by omega) hb0
  by_cases hb1 : n < 24
  · exact A6Compact.LinCheck.all_range'_of d1_1 n (by omega) hb1
  by_cases hb2 : n < 36
  · exact A6Compact.LinCheck.all_range'_of d1_2 n (by omega) hb2
  exact A6Compact.LinCheck.all_range'_of d1_3 n (by omega) (by omega)

end A6Compact.LinRun

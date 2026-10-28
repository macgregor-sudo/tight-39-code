module

public import A6LinChecks

@[expose] public section

/-!
# Lane LIN: D3 checks `(L_p · B)_r ≡ 0` (2184 rows, blocks of 364)

Kernel runs (`decide +kernel`) of the Boolean checks; one declaration per block keeps kernel memory small.
First-party code.
-/

namespace A6Compact.LinRun

open A6Compact.LinCheck

theorem d3_0 : (List.range' 0 364).all d3CheckT = true := by decide +kernel
theorem d3_1 : (List.range' 364 364).all d3CheckT = true := by decide +kernel
theorem d3_2 : (List.range' 728 364).all d3CheckT = true := by decide +kernel
theorem d3_3 : (List.range' 1092 364).all d3CheckT = true := by decide +kernel
theorem d3_4 : (List.range' 1456 364).all d3CheckT = true := by decide +kernel
theorem d3_5 : (List.range' 1820 364).all d3CheckT = true := by decide +kernel

/-- Collection of the blocks (no kernel evaluation). -/
theorem d3_range (n : ℕ) (h1 : 0 ≤ n) (h2 : n < 2184) : d3CheckT n = true := by
  by_cases hb0 : n < 364
  · exact A6Compact.LinCheck.all_range'_of d3_0 n (by omega) hb0
  by_cases hb1 : n < 728
  · exact A6Compact.LinCheck.all_range'_of d3_1 n (by omega) hb1
  by_cases hb2 : n < 1092
  · exact A6Compact.LinCheck.all_range'_of d3_2 n (by omega) hb2
  by_cases hb3 : n < 1456
  · exact A6Compact.LinCheck.all_range'_of d3_3 n (by omega) hb3
  by_cases hb4 : n < 1820
  · exact A6Compact.LinCheck.all_range'_of d3_4 n (by omega) hb4
  exact A6Compact.LinCheck.all_range'_of d3_5 n (by omega) (by omega)

end A6Compact.LinRun

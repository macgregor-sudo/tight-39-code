module

public import A6LinTie

@[expose] public section

/-!
# Lane LIN: tie of `lRow` to `jacobianRow`, part 0 (blocks of 56 rows)

Kernel runs (`decide +kernel`) of the Boolean checks; one declaration per block keeps kernel memory small.
First-party code.
-/

namespace A6Compact.LinRun

open A6Compact.LinTie

theorem tie_0 : (List.range' 0 56).all tieCheckN = true := by decide +kernel
theorem tie_1 : (List.range' 56 56).all tieCheckN = true := by decide +kernel
theorem tie_2 : (List.range' 112 56).all tieCheckN = true := by decide +kernel
theorem tie_3 : (List.range' 168 56).all tieCheckN = true := by decide +kernel
theorem tie_4 : (List.range' 224 56).all tieCheckN = true := by decide +kernel
theorem tie_5 : (List.range' 280 56).all tieCheckN = true := by decide +kernel
theorem tie_6 : (List.range' 336 56).all tieCheckN = true := by decide +kernel
theorem tie_7 : (List.range' 392 56).all tieCheckN = true := by decide +kernel
theorem tie_8 : (List.range' 448 56).all tieCheckN = true := by decide +kernel
theorem tie_9 : (List.range' 504 56).all tieCheckN = true := by decide +kernel
theorem tie_10 : (List.range' 560 56).all tieCheckN = true := by decide +kernel
theorem tie_11 : (List.range' 616 56).all tieCheckN = true := by decide +kernel
theorem tie_12 : (List.range' 672 56).all tieCheckN = true := by decide +kernel
theorem tie_13 : (List.range' 728 56).all tieCheckN = true := by decide +kernel
theorem tie_14 : (List.range' 784 56).all tieCheckN = true := by decide +kernel
theorem tie_15 : (List.range' 840 56).all tieCheckN = true := by decide +kernel
theorem tie_16 : (List.range' 896 56).all tieCheckN = true := by decide +kernel
theorem tie_17 : (List.range' 952 56).all tieCheckN = true := by decide +kernel
theorem tie_18 : (List.range' 1008 56).all tieCheckN = true := by decide +kernel
theorem tie_19 : (List.range' 1064 56).all tieCheckN = true := by decide +kernel

/-- Collection of the blocks (no kernel evaluation). -/
theorem tie_range0 (n : ℕ) (h1 : 0 ≤ n) (h2 : n < 1120) : tieCheckN n = true := by
  by_cases hb0 : n < 56
  · exact A6Compact.LinCheck.all_range'_of tie_0 n (by omega) hb0
  by_cases hb1 : n < 112
  · exact A6Compact.LinCheck.all_range'_of tie_1 n (by omega) hb1
  by_cases hb2 : n < 168
  · exact A6Compact.LinCheck.all_range'_of tie_2 n (by omega) hb2
  by_cases hb3 : n < 224
  · exact A6Compact.LinCheck.all_range'_of tie_3 n (by omega) hb3
  by_cases hb4 : n < 280
  · exact A6Compact.LinCheck.all_range'_of tie_4 n (by omega) hb4
  by_cases hb5 : n < 336
  · exact A6Compact.LinCheck.all_range'_of tie_5 n (by omega) hb5
  by_cases hb6 : n < 392
  · exact A6Compact.LinCheck.all_range'_of tie_6 n (by omega) hb6
  by_cases hb7 : n < 448
  · exact A6Compact.LinCheck.all_range'_of tie_7 n (by omega) hb7
  by_cases hb8 : n < 504
  · exact A6Compact.LinCheck.all_range'_of tie_8 n (by omega) hb8
  by_cases hb9 : n < 560
  · exact A6Compact.LinCheck.all_range'_of tie_9 n (by omega) hb9
  by_cases hb10 : n < 616
  · exact A6Compact.LinCheck.all_range'_of tie_10 n (by omega) hb10
  by_cases hb11 : n < 672
  · exact A6Compact.LinCheck.all_range'_of tie_11 n (by omega) hb11
  by_cases hb12 : n < 728
  · exact A6Compact.LinCheck.all_range'_of tie_12 n (by omega) hb12
  by_cases hb13 : n < 784
  · exact A6Compact.LinCheck.all_range'_of tie_13 n (by omega) hb13
  by_cases hb14 : n < 840
  · exact A6Compact.LinCheck.all_range'_of tie_14 n (by omega) hb14
  by_cases hb15 : n < 896
  · exact A6Compact.LinCheck.all_range'_of tie_15 n (by omega) hb15
  by_cases hb16 : n < 952
  · exact A6Compact.LinCheck.all_range'_of tie_16 n (by omega) hb16
  by_cases hb17 : n < 1008
  · exact A6Compact.LinCheck.all_range'_of tie_17 n (by omega) hb17
  by_cases hb18 : n < 1064
  · exact A6Compact.LinCheck.all_range'_of tie_18 n (by omega) hb18
  exact A6Compact.LinCheck.all_range'_of tie_19 n (by omega) (by omega)

end A6Compact.LinRun

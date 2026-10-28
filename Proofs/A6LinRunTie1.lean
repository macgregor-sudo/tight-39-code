module

public import A6LinTie

@[expose] public section

/-!
# Lane LIN: tie of `lRow` to `jacobianRow`, part 1 (blocks of 56 rows)

Kernel runs (`decide +kernel`) of the Boolean checks; one declaration per block keeps kernel memory small.
First-party code.
-/

namespace A6Compact.LinRun

open A6Compact.LinTie

theorem tie_20 : (List.range' 1120 56).all tieCheckN = true := by decide +kernel
theorem tie_21 : (List.range' 1176 56).all tieCheckN = true := by decide +kernel
theorem tie_22 : (List.range' 1232 56).all tieCheckN = true := by decide +kernel
theorem tie_23 : (List.range' 1288 56).all tieCheckN = true := by decide +kernel
theorem tie_24 : (List.range' 1344 56).all tieCheckN = true := by decide +kernel
theorem tie_25 : (List.range' 1400 56).all tieCheckN = true := by decide +kernel
theorem tie_26 : (List.range' 1456 56).all tieCheckN = true := by decide +kernel
theorem tie_27 : (List.range' 1512 56).all tieCheckN = true := by decide +kernel
theorem tie_28 : (List.range' 1568 56).all tieCheckN = true := by decide +kernel
theorem tie_29 : (List.range' 1624 56).all tieCheckN = true := by decide +kernel
theorem tie_30 : (List.range' 1680 56).all tieCheckN = true := by decide +kernel
theorem tie_31 : (List.range' 1736 56).all tieCheckN = true := by decide +kernel
theorem tie_32 : (List.range' 1792 56).all tieCheckN = true := by decide +kernel
theorem tie_33 : (List.range' 1848 56).all tieCheckN = true := by decide +kernel
theorem tie_34 : (List.range' 1904 56).all tieCheckN = true := by decide +kernel
theorem tie_35 : (List.range' 1960 56).all tieCheckN = true := by decide +kernel
theorem tie_36 : (List.range' 2016 56).all tieCheckN = true := by decide +kernel
theorem tie_37 : (List.range' 2072 56).all tieCheckN = true := by decide +kernel
theorem tie_38 : (List.range' 2128 56).all tieCheckN = true := by decide +kernel

/-- Collection of the blocks (no kernel evaluation). -/
theorem tie_range1 (n : ℕ) (h1 : 1120 ≤ n) (h2 : n < 2184) : tieCheckN n = true := by
  by_cases hb20 : n < 1176
  · exact A6Compact.LinCheck.all_range'_of tie_20 n (by omega) hb20
  by_cases hb21 : n < 1232
  · exact A6Compact.LinCheck.all_range'_of tie_21 n (by omega) hb21
  by_cases hb22 : n < 1288
  · exact A6Compact.LinCheck.all_range'_of tie_22 n (by omega) hb22
  by_cases hb23 : n < 1344
  · exact A6Compact.LinCheck.all_range'_of tie_23 n (by omega) hb23
  by_cases hb24 : n < 1400
  · exact A6Compact.LinCheck.all_range'_of tie_24 n (by omega) hb24
  by_cases hb25 : n < 1456
  · exact A6Compact.LinCheck.all_range'_of tie_25 n (by omega) hb25
  by_cases hb26 : n < 1512
  · exact A6Compact.LinCheck.all_range'_of tie_26 n (by omega) hb26
  by_cases hb27 : n < 1568
  · exact A6Compact.LinCheck.all_range'_of tie_27 n (by omega) hb27
  by_cases hb28 : n < 1624
  · exact A6Compact.LinCheck.all_range'_of tie_28 n (by omega) hb28
  by_cases hb29 : n < 1680
  · exact A6Compact.LinCheck.all_range'_of tie_29 n (by omega) hb29
  by_cases hb30 : n < 1736
  · exact A6Compact.LinCheck.all_range'_of tie_30 n (by omega) hb30
  by_cases hb31 : n < 1792
  · exact A6Compact.LinCheck.all_range'_of tie_31 n (by omega) hb31
  by_cases hb32 : n < 1848
  · exact A6Compact.LinCheck.all_range'_of tie_32 n (by omega) hb32
  by_cases hb33 : n < 1904
  · exact A6Compact.LinCheck.all_range'_of tie_33 n (by omega) hb33
  by_cases hb34 : n < 1960
  · exact A6Compact.LinCheck.all_range'_of tie_34 n (by omega) hb34
  by_cases hb35 : n < 2016
  · exact A6Compact.LinCheck.all_range'_of tie_35 n (by omega) hb35
  by_cases hb36 : n < 2072
  · exact A6Compact.LinCheck.all_range'_of tie_36 n (by omega) hb36
  by_cases hb37 : n < 2128
  · exact A6Compact.LinCheck.all_range'_of tie_37 n (by omega) hb37
  exact A6Compact.LinCheck.all_range'_of tie_38 n (by omega) (by omega)

end A6Compact.LinRun

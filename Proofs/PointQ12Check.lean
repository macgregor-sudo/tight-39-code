module

public import Q12Consts
public import PointQ12Table

/-!
# Kernel check: the literal table equals the generic shape over Q12

One `decide +kernel` per point (39 theorems, 27 coordinates each); a single
`∀ i k` decision exceeded the 4 GiB guard, the per-point split does not.
First-party, no borrowed text.
-/

@[expose] public section

namespace FourSheets.PointQ12

open FourSheets.PointShape

theorem shape_row_00 : List.ofFn (shape q12Consts 0) = point_00 := by decide +kernel
theorem shape_row_01 : List.ofFn (shape q12Consts 1) = point_01 := by decide +kernel
theorem shape_row_02 : List.ofFn (shape q12Consts 2) = point_02 := by decide +kernel
theorem shape_row_03 : List.ofFn (shape q12Consts 3) = point_03 := by decide +kernel
theorem shape_row_04 : List.ofFn (shape q12Consts 4) = point_04 := by decide +kernel
theorem shape_row_05 : List.ofFn (shape q12Consts 5) = point_05 := by decide +kernel
theorem shape_row_06 : List.ofFn (shape q12Consts 6) = point_06 := by decide +kernel
theorem shape_row_07 : List.ofFn (shape q12Consts 7) = point_07 := by decide +kernel
theorem shape_row_08 : List.ofFn (shape q12Consts 8) = point_08 := by decide +kernel
theorem shape_row_09 : List.ofFn (shape q12Consts 9) = point_09 := by decide +kernel
theorem shape_row_10 : List.ofFn (shape q12Consts 10) = point_10 := by decide +kernel
theorem shape_row_11 : List.ofFn (shape q12Consts 11) = point_11 := by decide +kernel
theorem shape_row_12 : List.ofFn (shape q12Consts 12) = point_12 := by decide +kernel
theorem shape_row_13 : List.ofFn (shape q12Consts 13) = point_13 := by decide +kernel
theorem shape_row_14 : List.ofFn (shape q12Consts 14) = point_14 := by decide +kernel
theorem shape_row_15 : List.ofFn (shape q12Consts 15) = point_15 := by decide +kernel
theorem shape_row_16 : List.ofFn (shape q12Consts 16) = point_16 := by decide +kernel
theorem shape_row_17 : List.ofFn (shape q12Consts 17) = point_17 := by decide +kernel
theorem shape_row_18 : List.ofFn (shape q12Consts 18) = point_18 := by decide +kernel
theorem shape_row_19 : List.ofFn (shape q12Consts 19) = point_19 := by decide +kernel
theorem shape_row_20 : List.ofFn (shape q12Consts 20) = point_20 := by decide +kernel
theorem shape_row_21 : List.ofFn (shape q12Consts 21) = point_21 := by decide +kernel
theorem shape_row_22 : List.ofFn (shape q12Consts 22) = point_22 := by decide +kernel
theorem shape_row_23 : List.ofFn (shape q12Consts 23) = point_23 := by decide +kernel
theorem shape_row_24 : List.ofFn (shape q12Consts 24) = point_24 := by decide +kernel
theorem shape_row_25 : List.ofFn (shape q12Consts 25) = point_25 := by decide +kernel
theorem shape_row_26 : List.ofFn (shape q12Consts 26) = point_26 := by decide +kernel
theorem shape_row_27 : List.ofFn (shape q12Consts 27) = point_27 := by decide +kernel
theorem shape_row_28 : List.ofFn (shape q12Consts 28) = point_28 := by decide +kernel
theorem shape_row_29 : List.ofFn (shape q12Consts 29) = point_29 := by decide +kernel
theorem shape_row_30 : List.ofFn (shape q12Consts 30) = point_30 := by decide +kernel
theorem shape_row_31 : List.ofFn (shape q12Consts 31) = point_31 := by decide +kernel
theorem shape_row_32 : List.ofFn (shape q12Consts 32) = point_32 := by decide +kernel
theorem shape_row_33 : List.ofFn (shape q12Consts 33) = point_33 := by decide +kernel
theorem shape_row_34 : List.ofFn (shape q12Consts 34) = point_34 := by decide +kernel
theorem shape_row_35 : List.ofFn (shape q12Consts 35) = point_35 := by decide +kernel
theorem shape_row_36 : List.ofFn (shape q12Consts 36) = point_36 := by decide +kernel
theorem shape_row_37 : List.ofFn (shape q12Consts 37) = point_37 := by decide +kernel
theorem shape_row_38 : List.ofFn (shape q12Consts 38) = point_38 := by decide +kernel

end FourSheets.PointQ12

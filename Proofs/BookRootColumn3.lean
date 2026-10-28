module

public import BookSheetOneColumn

@[expose] public section

/-! Literal supplied D6 column 3, original sheet 0; root order is the existing rootPair. -/
set_option Elab.async false
namespace Option2.NativeStress.BookHT.TangentCoordinates

theorem column3_at12 : SheetColumnAtPoint 3 12 := by decide +kernel
theorem column3_at13 : SheetColumnAtPoint 3 13 := by decide +kernel
theorem column3_at14 : SheetColumnAtPoint 3 14 := by decide +kernel
theorem column3_at15 : SheetColumnAtPoint 3 15 := by decide +kernel
theorem column3_at16 : SheetColumnAtPoint 3 16 := by decide +kernel
theorem column3_at17 : SheetColumnAtPoint 3 17 := by decide +kernel
theorem column3_at18 : SheetColumnAtPoint 3 18 := by decide +kernel
theorem column3_at19 : SheetColumnAtPoint 3 19 := by decide +kernel
theorem column3_at20 : SheetColumnAtPoint 3 20 := by decide +kernel
theorem column3_at21 : SheetColumnAtPoint 3 21 := by decide +kernel
theorem column3_at22 : SheetColumnAtPoint 3 22 := by decide +kernel
theorem column3_at23 : SheetColumnAtPoint 3 23 := by decide +kernel
theorem column3_at24 : SheetColumnAtPoint 3 24 := by decide +kernel
theorem column3_at25 : SheetColumnAtPoint 3 25 := by decide +kernel
theorem column3_at26 : SheetColumnAtPoint 3 26 := by decide +kernel
theorem column3_at27 : SheetColumnAtPoint 3 27 := by decide +kernel
theorem column3_at28 : SheetColumnAtPoint 3 28 := by decide +kernel
theorem column3_at29 : SheetColumnAtPoint 3 29 := by decide +kernel
theorem column3_at30 : SheetColumnAtPoint 3 30 := by decide +kernel
theorem column3_at31 : SheetColumnAtPoint 3 31 := by decide +kernel
theorem column3_at32 : SheetColumnAtPoint 3 32 := by decide +kernel
theorem column3_at33 : SheetColumnAtPoint 3 33 := by decide +kernel
theorem column3_at34 : SheetColumnAtPoint 3 34 := by decide +kernel
theorem column3_at35 : SheetColumnAtPoint 3 35 := by decide +kernel
theorem column3_at36 : SheetColumnAtPoint 3 36 := by decide +kernel
theorem column3_at37 : SheetColumnAtPoint 3 37 := by decide +kernel
theorem column3_at38 : SheetColumnAtPoint 3 38 := by decide +kernel

theorem column3_all_points (p : Fin 39) : SheetColumnAtPoint 3 p := by
  revert p
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 3 0 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 3 1 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 3 2 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 3 3 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 3 4 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 3 5 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 3 6 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 3 7 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 3 8 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 3 9 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 3 10 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 3 11 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at12, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at13, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at14, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at15, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at16, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at17, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at18, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at19, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at20, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at21, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at22, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at23, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at24, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at25, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at26, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at27, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at28, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at29, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at30, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at31, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at32, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at33, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at34, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at35, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at36, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at37, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_at38, ?_⟩
  exact Fin.forall_fin_zero.mpr trivial

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.column3_all_points
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.column3_all_points


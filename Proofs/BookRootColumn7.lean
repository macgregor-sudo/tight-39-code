module

public import BookSheetOneColumn

@[expose] public section

/-! Literal supplied D6 column 7, original sheet 1; root order is the existing rootPair. -/
set_option Elab.async false
namespace Option2.NativeStress.BookHT.TangentCoordinates

theorem column7_at3 : SheetColumnAtPoint 7 3 := by decide +kernel
theorem column7_at4 : SheetColumnAtPoint 7 4 := by decide +kernel
theorem column7_at5 : SheetColumnAtPoint 7 5 := by decide +kernel
theorem column7_at6 : SheetColumnAtPoint 7 6 := by decide +kernel
theorem column7_at7 : SheetColumnAtPoint 7 7 := by decide +kernel
theorem column7_at8 : SheetColumnAtPoint 7 8 := by decide +kernel
theorem column7_at9 : SheetColumnAtPoint 7 9 := by decide +kernel
theorem column7_at10 : SheetColumnAtPoint 7 10 := by decide +kernel
theorem column7_at11 : SheetColumnAtPoint 7 11 := by decide +kernel
theorem column7_at21 : SheetColumnAtPoint 7 21 := by decide +kernel
theorem column7_at22 : SheetColumnAtPoint 7 22 := by decide +kernel
theorem column7_at23 : SheetColumnAtPoint 7 23 := by decide +kernel
theorem column7_at24 : SheetColumnAtPoint 7 24 := by decide +kernel
theorem column7_at25 : SheetColumnAtPoint 7 25 := by decide +kernel
theorem column7_at26 : SheetColumnAtPoint 7 26 := by decide +kernel
theorem column7_at27 : SheetColumnAtPoint 7 27 := by decide +kernel
theorem column7_at28 : SheetColumnAtPoint 7 28 := by decide +kernel
theorem column7_at29 : SheetColumnAtPoint 7 29 := by decide +kernel
theorem column7_at30 : SheetColumnAtPoint 7 30 := by decide +kernel
theorem column7_at31 : SheetColumnAtPoint 7 31 := by decide +kernel
theorem column7_at32 : SheetColumnAtPoint 7 32 := by decide +kernel
theorem column7_at33 : SheetColumnAtPoint 7 33 := by decide +kernel
theorem column7_at34 : SheetColumnAtPoint 7 34 := by decide +kernel
theorem column7_at35 : SheetColumnAtPoint 7 35 := by decide +kernel
theorem column7_at36 : SheetColumnAtPoint 7 36 := by decide +kernel
theorem column7_at37 : SheetColumnAtPoint 7 37 := by decide +kernel
theorem column7_at38 : SheetColumnAtPoint 7 38 := by decide +kernel

theorem column7_all_points (p : Fin 39) : SheetColumnAtPoint 7 p := by
  revert p
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 7 0 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 7 1 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 7 2 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at3, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at4, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at5, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at6, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at7, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at8, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at9, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at10, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at11, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 7 12 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 7 13 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 7 14 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 7 15 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 7 16 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 7 17 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 7 18 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 7 19 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 7 20 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at21, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at22, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at23, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at24, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at25, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at26, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at27, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at28, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at29, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at30, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at31, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at32, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at33, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at34, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at35, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at36, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at37, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_at38, ?_⟩
  exact Fin.forall_fin_zero.mpr trivial

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.column7_all_points
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.column7_all_points


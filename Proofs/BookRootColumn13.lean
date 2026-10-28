module

public import BookSheetOneColumn

@[expose] public section

/-! Literal supplied D6 column 13, original sheet 2; root order is the existing rootPair. -/
set_option Elab.async false
namespace Option2.NativeStress.BookHT.TangentCoordinates

theorem column13_at3 : SheetColumnAtPoint 13 3 := by decide +kernel
theorem column13_at4 : SheetColumnAtPoint 13 4 := by decide +kernel
theorem column13_at5 : SheetColumnAtPoint 13 5 := by decide +kernel
theorem column13_at6 : SheetColumnAtPoint 13 6 := by decide +kernel
theorem column13_at7 : SheetColumnAtPoint 13 7 := by decide +kernel
theorem column13_at8 : SheetColumnAtPoint 13 8 := by decide +kernel
theorem column13_at9 : SheetColumnAtPoint 13 9 := by decide +kernel
theorem column13_at10 : SheetColumnAtPoint 13 10 := by decide +kernel
theorem column13_at11 : SheetColumnAtPoint 13 11 := by decide +kernel
theorem column13_at12 : SheetColumnAtPoint 13 12 := by decide +kernel
theorem column13_at13 : SheetColumnAtPoint 13 13 := by decide +kernel
theorem column13_at14 : SheetColumnAtPoint 13 14 := by decide +kernel
theorem column13_at15 : SheetColumnAtPoint 13 15 := by decide +kernel
theorem column13_at16 : SheetColumnAtPoint 13 16 := by decide +kernel
theorem column13_at17 : SheetColumnAtPoint 13 17 := by decide +kernel
theorem column13_at18 : SheetColumnAtPoint 13 18 := by decide +kernel
theorem column13_at19 : SheetColumnAtPoint 13 19 := by decide +kernel
theorem column13_at20 : SheetColumnAtPoint 13 20 := by decide +kernel
theorem column13_at30 : SheetColumnAtPoint 13 30 := by decide +kernel
theorem column13_at31 : SheetColumnAtPoint 13 31 := by decide +kernel
theorem column13_at32 : SheetColumnAtPoint 13 32 := by decide +kernel
theorem column13_at33 : SheetColumnAtPoint 13 33 := by decide +kernel
theorem column13_at34 : SheetColumnAtPoint 13 34 := by decide +kernel
theorem column13_at35 : SheetColumnAtPoint 13 35 := by decide +kernel
theorem column13_at36 : SheetColumnAtPoint 13 36 := by decide +kernel
theorem column13_at37 : SheetColumnAtPoint 13 37 := by decide +kernel
theorem column13_at38 : SheetColumnAtPoint 13 38 := by decide +kernel

theorem column13_all_points (p : Fin 39) : SheetColumnAtPoint 13 p := by
  revert p
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 13 0 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 13 1 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 13 2 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at3, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at4, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at5, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at6, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at7, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at8, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at9, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at10, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at11, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at12, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at13, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at14, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at15, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at16, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at17, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at18, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at19, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at20, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 13 21 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 13 22 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 13 23 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 13 24 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 13 25 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 13 26 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 13 27 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 13 28 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 13 29 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at30, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at31, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at32, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at33, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at34, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at35, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at36, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at37, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_at38, ?_⟩
  exact Fin.forall_fin_zero.mpr trivial

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.column13_all_points
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.column13_all_points


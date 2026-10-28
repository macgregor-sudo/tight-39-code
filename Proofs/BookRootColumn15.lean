module

public import BookSheetOneColumn

@[expose] public section

/-! Literal supplied D6 column 15, original sheet 2; root order is the existing rootPair. -/
set_option Elab.async false
namespace Option2.NativeStress.BookHT.TangentCoordinates

theorem column15_at3 : SheetColumnAtPoint 15 3 := by decide +kernel
theorem column15_at4 : SheetColumnAtPoint 15 4 := by decide +kernel
theorem column15_at5 : SheetColumnAtPoint 15 5 := by decide +kernel
theorem column15_at6 : SheetColumnAtPoint 15 6 := by decide +kernel
theorem column15_at7 : SheetColumnAtPoint 15 7 := by decide +kernel
theorem column15_at8 : SheetColumnAtPoint 15 8 := by decide +kernel
theorem column15_at9 : SheetColumnAtPoint 15 9 := by decide +kernel
theorem column15_at10 : SheetColumnAtPoint 15 10 := by decide +kernel
theorem column15_at11 : SheetColumnAtPoint 15 11 := by decide +kernel
theorem column15_at12 : SheetColumnAtPoint 15 12 := by decide +kernel
theorem column15_at13 : SheetColumnAtPoint 15 13 := by decide +kernel
theorem column15_at14 : SheetColumnAtPoint 15 14 := by decide +kernel
theorem column15_at15 : SheetColumnAtPoint 15 15 := by decide +kernel
theorem column15_at16 : SheetColumnAtPoint 15 16 := by decide +kernel
theorem column15_at17 : SheetColumnAtPoint 15 17 := by decide +kernel
theorem column15_at18 : SheetColumnAtPoint 15 18 := by decide +kernel
theorem column15_at19 : SheetColumnAtPoint 15 19 := by decide +kernel
theorem column15_at20 : SheetColumnAtPoint 15 20 := by decide +kernel
theorem column15_at30 : SheetColumnAtPoint 15 30 := by decide +kernel
theorem column15_at31 : SheetColumnAtPoint 15 31 := by decide +kernel
theorem column15_at32 : SheetColumnAtPoint 15 32 := by decide +kernel
theorem column15_at33 : SheetColumnAtPoint 15 33 := by decide +kernel
theorem column15_at34 : SheetColumnAtPoint 15 34 := by decide +kernel
theorem column15_at35 : SheetColumnAtPoint 15 35 := by decide +kernel
theorem column15_at36 : SheetColumnAtPoint 15 36 := by decide +kernel
theorem column15_at37 : SheetColumnAtPoint 15 37 := by decide +kernel
theorem column15_at38 : SheetColumnAtPoint 15 38 := by decide +kernel

theorem column15_all_points (p : Fin 39) : SheetColumnAtPoint 15 p := by
  revert p
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 15 0 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 15 1 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 15 2 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at3, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at4, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at5, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at6, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at7, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at8, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at9, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at10, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at11, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at12, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at13, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at14, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at15, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at16, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at17, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at18, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at19, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at20, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 15 21 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 15 22 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 15 23 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 15 24 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 15 25 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 15 26 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 15 27 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 15 28 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 15 29 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at30, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at31, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at32, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at33, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at34, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at35, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at36, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at37, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_at38, ?_⟩
  exact Fin.forall_fin_zero.mpr trivial

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.column15_all_points
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.column15_all_points


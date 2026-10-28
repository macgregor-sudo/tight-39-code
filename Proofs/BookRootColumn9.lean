module

public import BookSheetOneColumn

@[expose] public section

/-! Literal supplied D6 column 9, original sheet 1; root order is the existing rootPair. -/
set_option Elab.async false
namespace Option2.NativeStress.BookHT.TangentCoordinates

theorem column9_at3 : SheetColumnAtPoint 9 3 := by decide +kernel
theorem column9_at4 : SheetColumnAtPoint 9 4 := by decide +kernel
theorem column9_at5 : SheetColumnAtPoint 9 5 := by decide +kernel
theorem column9_at6 : SheetColumnAtPoint 9 6 := by decide +kernel
theorem column9_at7 : SheetColumnAtPoint 9 7 := by decide +kernel
theorem column9_at8 : SheetColumnAtPoint 9 8 := by decide +kernel
theorem column9_at9 : SheetColumnAtPoint 9 9 := by decide +kernel
theorem column9_at10 : SheetColumnAtPoint 9 10 := by decide +kernel
theorem column9_at11 : SheetColumnAtPoint 9 11 := by decide +kernel
theorem column9_at21 : SheetColumnAtPoint 9 21 := by decide +kernel
theorem column9_at22 : SheetColumnAtPoint 9 22 := by decide +kernel
theorem column9_at23 : SheetColumnAtPoint 9 23 := by decide +kernel
theorem column9_at24 : SheetColumnAtPoint 9 24 := by decide +kernel
theorem column9_at25 : SheetColumnAtPoint 9 25 := by decide +kernel
theorem column9_at26 : SheetColumnAtPoint 9 26 := by decide +kernel
theorem column9_at27 : SheetColumnAtPoint 9 27 := by decide +kernel
theorem column9_at28 : SheetColumnAtPoint 9 28 := by decide +kernel
theorem column9_at29 : SheetColumnAtPoint 9 29 := by decide +kernel
theorem column9_at30 : SheetColumnAtPoint 9 30 := by decide +kernel
theorem column9_at31 : SheetColumnAtPoint 9 31 := by decide +kernel
theorem column9_at32 : SheetColumnAtPoint 9 32 := by decide +kernel
theorem column9_at33 : SheetColumnAtPoint 9 33 := by decide +kernel
theorem column9_at34 : SheetColumnAtPoint 9 34 := by decide +kernel
theorem column9_at35 : SheetColumnAtPoint 9 35 := by decide +kernel
theorem column9_at36 : SheetColumnAtPoint 9 36 := by decide +kernel
theorem column9_at37 : SheetColumnAtPoint 9 37 := by decide +kernel
theorem column9_at38 : SheetColumnAtPoint 9 38 := by decide +kernel

theorem column9_all_points (p : Fin 39) : SheetColumnAtPoint 9 p := by
  revert p
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 9 0 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 9 1 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 9 2 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at3, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at4, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at5, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at6, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at7, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at8, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at9, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at10, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at11, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 9 12 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 9 13 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 9 14 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 9 15 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 9 16 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 9 17 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 9 18 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 9 19 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 9 20 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at21, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at22, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at23, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at24, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at25, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at26, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at27, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at28, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at29, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at30, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at31, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at32, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at33, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at34, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at35, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at36, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at37, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_at38, ?_⟩
  exact Fin.forall_fin_zero.mpr trivial

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.column9_all_points
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.column9_all_points


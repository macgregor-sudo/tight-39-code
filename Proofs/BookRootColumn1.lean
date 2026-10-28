module

public import BookSheetOneColumn

@[expose] public section

/-! Literal supplied D6 column 1, original sheet 0; root order is the existing rootPair. -/
set_option Elab.async false
namespace Option2.NativeStress.BookHT.TangentCoordinates

theorem column1_at12 : SheetColumnAtPoint 1 12 := by decide +kernel
theorem column1_at13 : SheetColumnAtPoint 1 13 := by decide +kernel
theorem column1_at14 : SheetColumnAtPoint 1 14 := by decide +kernel
theorem column1_at15 : SheetColumnAtPoint 1 15 := by decide +kernel
theorem column1_at16 : SheetColumnAtPoint 1 16 := by decide +kernel
theorem column1_at17 : SheetColumnAtPoint 1 17 := by decide +kernel
theorem column1_at18 : SheetColumnAtPoint 1 18 := by decide +kernel
theorem column1_at19 : SheetColumnAtPoint 1 19 := by decide +kernel
theorem column1_at20 : SheetColumnAtPoint 1 20 := by decide +kernel
theorem column1_at21 : SheetColumnAtPoint 1 21 := by decide +kernel
theorem column1_at22 : SheetColumnAtPoint 1 22 := by decide +kernel
theorem column1_at23 : SheetColumnAtPoint 1 23 := by decide +kernel
theorem column1_at24 : SheetColumnAtPoint 1 24 := by decide +kernel
theorem column1_at25 : SheetColumnAtPoint 1 25 := by decide +kernel
theorem column1_at26 : SheetColumnAtPoint 1 26 := by decide +kernel
theorem column1_at27 : SheetColumnAtPoint 1 27 := by decide +kernel
theorem column1_at28 : SheetColumnAtPoint 1 28 := by decide +kernel
theorem column1_at29 : SheetColumnAtPoint 1 29 := by decide +kernel
theorem column1_at30 : SheetColumnAtPoint 1 30 := by decide +kernel
theorem column1_at31 : SheetColumnAtPoint 1 31 := by decide +kernel
theorem column1_at32 : SheetColumnAtPoint 1 32 := by decide +kernel
theorem column1_at33 : SheetColumnAtPoint 1 33 := by decide +kernel
theorem column1_at34 : SheetColumnAtPoint 1 34 := by decide +kernel
theorem column1_at35 : SheetColumnAtPoint 1 35 := by decide +kernel
theorem column1_at36 : SheetColumnAtPoint 1 36 := by decide +kernel
theorem column1_at37 : SheetColumnAtPoint 1 37 := by decide +kernel
theorem column1_at38 : SheetColumnAtPoint 1 38 := by decide +kernel

theorem column1_all_points (p : Fin 39) : SheetColumnAtPoint 1 p := by
  revert p
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 1 0 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 1 1 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 1 2 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 1 3 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 1 4 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 1 5 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 1 6 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 1 7 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 1 8 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 1 9 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 1 10 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 1 11 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at12, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at13, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at14, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at15, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at16, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at17, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at18, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at19, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at20, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at21, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at22, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at23, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at24, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at25, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at26, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at27, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at28, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at29, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at30, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at31, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at32, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at33, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at34, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at35, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at36, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at37, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_at38, ?_⟩
  exact Fin.forall_fin_zero.mpr trivial

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.column1_all_points
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.column1_all_points


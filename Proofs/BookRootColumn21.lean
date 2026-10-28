module

public import BookSheetOneColumn

@[expose] public section

/-! Literal supplied D6 column 21, original sheet 3; root order is the existing rootPair. -/
set_option Elab.async false
namespace Option2.NativeStress.BookHT.TangentCoordinates

theorem column21_at3 : SheetColumnAtPoint 21 3 := by decide +kernel
theorem column21_at4 : SheetColumnAtPoint 21 4 := by decide +kernel
theorem column21_at5 : SheetColumnAtPoint 21 5 := by decide +kernel
theorem column21_at6 : SheetColumnAtPoint 21 6 := by decide +kernel
theorem column21_at7 : SheetColumnAtPoint 21 7 := by decide +kernel
theorem column21_at8 : SheetColumnAtPoint 21 8 := by decide +kernel
theorem column21_at9 : SheetColumnAtPoint 21 9 := by decide +kernel
theorem column21_at10 : SheetColumnAtPoint 21 10 := by decide +kernel
theorem column21_at11 : SheetColumnAtPoint 21 11 := by decide +kernel
theorem column21_at12 : SheetColumnAtPoint 21 12 := by decide +kernel
theorem column21_at13 : SheetColumnAtPoint 21 13 := by decide +kernel
theorem column21_at14 : SheetColumnAtPoint 21 14 := by decide +kernel
theorem column21_at15 : SheetColumnAtPoint 21 15 := by decide +kernel
theorem column21_at16 : SheetColumnAtPoint 21 16 := by decide +kernel
theorem column21_at17 : SheetColumnAtPoint 21 17 := by decide +kernel
theorem column21_at18 : SheetColumnAtPoint 21 18 := by decide +kernel
theorem column21_at19 : SheetColumnAtPoint 21 19 := by decide +kernel
theorem column21_at20 : SheetColumnAtPoint 21 20 := by decide +kernel
theorem column21_at21 : SheetColumnAtPoint 21 21 := by decide +kernel
theorem column21_at22 : SheetColumnAtPoint 21 22 := by decide +kernel
theorem column21_at23 : SheetColumnAtPoint 21 23 := by decide +kernel
theorem column21_at24 : SheetColumnAtPoint 21 24 := by decide +kernel
theorem column21_at25 : SheetColumnAtPoint 21 25 := by decide +kernel
theorem column21_at26 : SheetColumnAtPoint 21 26 := by decide +kernel
theorem column21_at27 : SheetColumnAtPoint 21 27 := by decide +kernel
theorem column21_at28 : SheetColumnAtPoint 21 28 := by decide +kernel
theorem column21_at29 : SheetColumnAtPoint 21 29 := by decide +kernel

theorem column21_all_points (p : Fin 39) : SheetColumnAtPoint 21 p := by
  revert p
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 21 0 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 21 1 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 21 2 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at3, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at4, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at5, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at6, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at7, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at8, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at9, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at10, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at11, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at12, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at13, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at14, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at15, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at16, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at17, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at18, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at19, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at20, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at21, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at22, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at23, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at24, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at25, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at26, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at27, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at28, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_at29, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 21 30 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 21 31 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 21 32 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 21 33 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 21 34 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 21 35 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 21 36 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 21 37 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 21 38 (by decide), ?_⟩
  exact Fin.forall_fin_zero.mpr trivial

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.column21_all_points
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.column21_all_points


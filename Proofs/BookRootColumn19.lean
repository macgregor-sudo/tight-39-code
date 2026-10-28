module

public import BookSheetOneColumn

@[expose] public section

/-! Literal supplied D6 column 19, original sheet 3; root order is the existing rootPair. -/
set_option Elab.async false
namespace Option2.NativeStress.BookHT.TangentCoordinates

theorem column19_at3 : SheetColumnAtPoint 19 3 := by decide +kernel
theorem column19_at4 : SheetColumnAtPoint 19 4 := by decide +kernel
theorem column19_at5 : SheetColumnAtPoint 19 5 := by decide +kernel
theorem column19_at6 : SheetColumnAtPoint 19 6 := by decide +kernel
theorem column19_at7 : SheetColumnAtPoint 19 7 := by decide +kernel
theorem column19_at8 : SheetColumnAtPoint 19 8 := by decide +kernel
theorem column19_at9 : SheetColumnAtPoint 19 9 := by decide +kernel
theorem column19_at10 : SheetColumnAtPoint 19 10 := by decide +kernel
theorem column19_at11 : SheetColumnAtPoint 19 11 := by decide +kernel
theorem column19_at12 : SheetColumnAtPoint 19 12 := by decide +kernel
theorem column19_at13 : SheetColumnAtPoint 19 13 := by decide +kernel
theorem column19_at14 : SheetColumnAtPoint 19 14 := by decide +kernel
theorem column19_at15 : SheetColumnAtPoint 19 15 := by decide +kernel
theorem column19_at16 : SheetColumnAtPoint 19 16 := by decide +kernel
theorem column19_at17 : SheetColumnAtPoint 19 17 := by decide +kernel
theorem column19_at18 : SheetColumnAtPoint 19 18 := by decide +kernel
theorem column19_at19 : SheetColumnAtPoint 19 19 := by decide +kernel
theorem column19_at20 : SheetColumnAtPoint 19 20 := by decide +kernel
theorem column19_at21 : SheetColumnAtPoint 19 21 := by decide +kernel
theorem column19_at22 : SheetColumnAtPoint 19 22 := by decide +kernel
theorem column19_at23 : SheetColumnAtPoint 19 23 := by decide +kernel
theorem column19_at24 : SheetColumnAtPoint 19 24 := by decide +kernel
theorem column19_at25 : SheetColumnAtPoint 19 25 := by decide +kernel
theorem column19_at26 : SheetColumnAtPoint 19 26 := by decide +kernel
theorem column19_at27 : SheetColumnAtPoint 19 27 := by decide +kernel
theorem column19_at28 : SheetColumnAtPoint 19 28 := by decide +kernel
theorem column19_at29 : SheetColumnAtPoint 19 29 := by decide +kernel

theorem column19_all_points (p : Fin 39) : SheetColumnAtPoint 19 p := by
  revert p
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 19 0 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 19 1 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 19 2 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at3, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at4, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at5, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at6, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at7, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at8, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at9, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at10, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at11, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at12, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at13, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at14, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at15, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at16, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at17, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at18, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at19, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at20, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at21, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at22, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at23, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at24, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at25, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at26, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at27, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at28, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_at29, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 19 30 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 19 31 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 19 32 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 19 33 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 19 34 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 19 35 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 19 36 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 19 37 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 19 38 (by decide), ?_⟩
  exact Fin.forall_fin_zero.mpr trivial

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.column19_all_points
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.column19_all_points


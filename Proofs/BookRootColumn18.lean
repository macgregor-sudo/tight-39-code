module

public import BookSheetOneColumn

@[expose] public section

/-! Literal supplied D6 column 18, original sheet 3; root order is the existing rootPair. -/
set_option Elab.async false
namespace Option2.NativeStress.BookHT.TangentCoordinates

theorem column18_at3 : SheetColumnAtPoint 18 3 := by decide +kernel
theorem column18_at4 : SheetColumnAtPoint 18 4 := by decide +kernel
theorem column18_at5 : SheetColumnAtPoint 18 5 := by decide +kernel
theorem column18_at6 : SheetColumnAtPoint 18 6 := by decide +kernel
theorem column18_at7 : SheetColumnAtPoint 18 7 := by decide +kernel
theorem column18_at8 : SheetColumnAtPoint 18 8 := by decide +kernel
theorem column18_at9 : SheetColumnAtPoint 18 9 := by decide +kernel
theorem column18_at10 : SheetColumnAtPoint 18 10 := by decide +kernel
theorem column18_at11 : SheetColumnAtPoint 18 11 := by decide +kernel
theorem column18_at12 : SheetColumnAtPoint 18 12 := by decide +kernel
theorem column18_at13 : SheetColumnAtPoint 18 13 := by decide +kernel
theorem column18_at14 : SheetColumnAtPoint 18 14 := by decide +kernel
theorem column18_at15 : SheetColumnAtPoint 18 15 := by decide +kernel
theorem column18_at16 : SheetColumnAtPoint 18 16 := by decide +kernel
theorem column18_at17 : SheetColumnAtPoint 18 17 := by decide +kernel
theorem column18_at18 : SheetColumnAtPoint 18 18 := by decide +kernel
theorem column18_at19 : SheetColumnAtPoint 18 19 := by decide +kernel
theorem column18_at20 : SheetColumnAtPoint 18 20 := by decide +kernel
theorem column18_at21 : SheetColumnAtPoint 18 21 := by decide +kernel
theorem column18_at22 : SheetColumnAtPoint 18 22 := by decide +kernel
theorem column18_at23 : SheetColumnAtPoint 18 23 := by decide +kernel
theorem column18_at24 : SheetColumnAtPoint 18 24 := by decide +kernel
theorem column18_at25 : SheetColumnAtPoint 18 25 := by decide +kernel
theorem column18_at26 : SheetColumnAtPoint 18 26 := by decide +kernel
theorem column18_at27 : SheetColumnAtPoint 18 27 := by decide +kernel
theorem column18_at28 : SheetColumnAtPoint 18 28 := by decide +kernel
theorem column18_at29 : SheetColumnAtPoint 18 29 := by decide +kernel

theorem column18_all_points (p : Fin 39) : SheetColumnAtPoint 18 p := by
  revert p
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 18 0 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 18 1 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 18 2 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at3, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at4, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at5, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at6, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at7, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at8, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at9, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at10, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at11, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at12, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at13, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at14, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at15, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at16, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at17, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at18, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at19, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at20, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at21, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at22, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at23, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at24, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at25, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at26, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at27, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at28, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_at29, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 18 30 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 18 31 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 18 32 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 18 33 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 18 34 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 18 35 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 18 36 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 18 37 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 18 38 (by decide), ?_⟩
  exact Fin.forall_fin_zero.mpr trivial

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.column18_all_points
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.column18_all_points


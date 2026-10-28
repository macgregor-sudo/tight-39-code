module

public import BookSheetOneColumn

@[expose] public section

/-! Literal supplied D6 column 12, original sheet 2; root order is the existing rootPair. -/
set_option Elab.async false
namespace Option2.NativeStress.BookHT.TangentCoordinates

theorem column12_at3 : SheetColumnAtPoint 12 3 := by decide +kernel
theorem column12_at4 : SheetColumnAtPoint 12 4 := by decide +kernel
theorem column12_at5 : SheetColumnAtPoint 12 5 := by decide +kernel
theorem column12_at6 : SheetColumnAtPoint 12 6 := by decide +kernel
theorem column12_at7 : SheetColumnAtPoint 12 7 := by decide +kernel
theorem column12_at8 : SheetColumnAtPoint 12 8 := by decide +kernel
theorem column12_at9 : SheetColumnAtPoint 12 9 := by decide +kernel
theorem column12_at10 : SheetColumnAtPoint 12 10 := by decide +kernel
theorem column12_at11 : SheetColumnAtPoint 12 11 := by decide +kernel
theorem column12_at12 : SheetColumnAtPoint 12 12 := by decide +kernel
theorem column12_at13 : SheetColumnAtPoint 12 13 := by decide +kernel
theorem column12_at14 : SheetColumnAtPoint 12 14 := by decide +kernel
theorem column12_at15 : SheetColumnAtPoint 12 15 := by decide +kernel
theorem column12_at16 : SheetColumnAtPoint 12 16 := by decide +kernel
theorem column12_at17 : SheetColumnAtPoint 12 17 := by decide +kernel
theorem column12_at18 : SheetColumnAtPoint 12 18 := by decide +kernel
theorem column12_at19 : SheetColumnAtPoint 12 19 := by decide +kernel
theorem column12_at20 : SheetColumnAtPoint 12 20 := by decide +kernel
theorem column12_at30 : SheetColumnAtPoint 12 30 := by decide +kernel
theorem column12_at31 : SheetColumnAtPoint 12 31 := by decide +kernel
theorem column12_at32 : SheetColumnAtPoint 12 32 := by decide +kernel
theorem column12_at33 : SheetColumnAtPoint 12 33 := by decide +kernel
theorem column12_at34 : SheetColumnAtPoint 12 34 := by decide +kernel
theorem column12_at35 : SheetColumnAtPoint 12 35 := by decide +kernel
theorem column12_at36 : SheetColumnAtPoint 12 36 := by decide +kernel
theorem column12_at37 : SheetColumnAtPoint 12 37 := by decide +kernel
theorem column12_at38 : SheetColumnAtPoint 12 38 := by decide +kernel

theorem column12_all_points (p : Fin 39) : SheetColumnAtPoint 12 p := by
  revert p
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 12 0 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 12 1 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 12 2 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at3, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at4, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at5, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at6, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at7, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at8, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at9, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at10, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at11, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at12, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at13, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at14, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at15, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at16, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at17, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at18, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at19, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at20, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 12 21 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 12 22 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 12 23 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 12 24 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 12 25 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 12 26 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 12 27 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 12 28 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 12 29 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at30, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at31, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at32, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at33, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at34, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at35, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at36, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at37, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_at38, ?_⟩
  exact Fin.forall_fin_zero.mpr trivial

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.column12_all_points
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.column12_all_points


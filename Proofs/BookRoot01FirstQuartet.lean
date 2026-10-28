module

public import BookConjugationQ12

/-! Exact first non-anchor quartet of the specified sheet0/E01 column. -/

@[expose] public section
set_option Elab.async false

namespace Option2.NativeStress.BookHT.TangentCoordinates

abbrev Root01AtPoint (p : Fin 39) : Prop := ∀ k : Fin 27,
  d6ColumnQ12 0 ⟨27 * p.val + k.val, by omega⟩ =
    q12SeedRoot01Fast ⟨27 * p.val + k.val, by omega⟩

theorem root01_at12 : Root01AtPoint 12 := by decide +kernel
theorem root01_at13 : Root01AtPoint 13 := by decide +kernel
theorem root01_at14 : Root01AtPoint 14 := by decide +kernel
theorem root01_at15 : Root01AtPoint 15 := by decide +kernel
theorem root01_at16 : Root01AtPoint 16 := by decide +kernel
theorem root01_at17 : Root01AtPoint 17 := by decide +kernel
theorem root01_at18 : Root01AtPoint 18 := by decide +kernel
theorem root01_at19 : Root01AtPoint 19 := by decide +kernel
theorem root01_at20 : Root01AtPoint 20 := by decide +kernel

end Option2.NativeStress.BookHT.TangentCoordinates

#check Option2.NativeStress.BookHT.TangentCoordinates.root01_at20
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.root01_at20

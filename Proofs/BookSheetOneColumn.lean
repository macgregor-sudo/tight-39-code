module

public import BookSheetConjugation

@[expose] public section

/-! Literal D6 sheet1/E01 against the unchanged T1-conjugation formula, all1053 coordinates. -/
set_option Elab.async false
namespace Option2.NativeStress.BookHT.TangentCoordinates

abbrev SheetColumnAtPoint (b : Fin 24) (p : Fin 39) : Prop := ∀ k : Fin 27,
  d6ColumnQ12 b ⟨27 * p.val + k.val, by omega⟩ = q12SheetColumn b p k

theorem sheetColumn_at_anchor (b : Fin 24) (p : Fin 39)
    (hp : p.val / 3 = 0 ∨ (1 + 3 * (d6Sheet b).val ≤ p.val / 3 ∧
      p.val / 3 ≤ 3 + 3 * (d6Sheet b).val)) : SheetColumnAtPoint b p := by
  intro k
  let v : Fin 1053 := ⟨27 * p.val + k.val, by omega⟩
  have hidx : v.val / 81 = p.val / 3 := by dsimp [v]; omega
  have hv : AnchorSupport.AnchorCoordinate (d6Sheet b) v := by
    simpa only [AnchorSupport.AnchorCoordinate, hidx] using hp
  change d6ColumnQ12 b v = q12SheetColumn b p k
  have hz : d6ColumnQ12 b v = 0 := by
    apply Q12.toComplex_injective
    rw [d6ColumnQ12_complex, d6Column_anchor_zero b v hv, map_zero]
  rw [hz]
  simp only [q12SheetColumn, hp, ite_true, Pi.zero_apply]

theorem column6_at3 : SheetColumnAtPoint 6 3 := by decide +kernel
theorem column6_at4 : SheetColumnAtPoint 6 4 := by decide +kernel
theorem column6_at5 : SheetColumnAtPoint 6 5 := by decide +kernel
theorem column6_at6 : SheetColumnAtPoint 6 6 := by decide +kernel
theorem column6_at7 : SheetColumnAtPoint 6 7 := by decide +kernel
theorem column6_at8 : SheetColumnAtPoint 6 8 := by decide +kernel
theorem column6_at9 : SheetColumnAtPoint 6 9 := by decide +kernel
theorem column6_at10 : SheetColumnAtPoint 6 10 := by decide +kernel
theorem column6_at11 : SheetColumnAtPoint 6 11 := by decide +kernel
theorem column6_at21 : SheetColumnAtPoint 6 21 := by decide +kernel
theorem column6_at22 : SheetColumnAtPoint 6 22 := by decide +kernel
theorem column6_at23 : SheetColumnAtPoint 6 23 := by decide +kernel
theorem column6_at24 : SheetColumnAtPoint 6 24 := by decide +kernel
theorem column6_at25 : SheetColumnAtPoint 6 25 := by decide +kernel
theorem column6_at26 : SheetColumnAtPoint 6 26 := by decide +kernel
theorem column6_at27 : SheetColumnAtPoint 6 27 := by decide +kernel
theorem column6_at28 : SheetColumnAtPoint 6 28 := by decide +kernel
theorem column6_at29 : SheetColumnAtPoint 6 29 := by decide +kernel
theorem column6_at30 : SheetColumnAtPoint 6 30 := by decide +kernel
theorem column6_at31 : SheetColumnAtPoint 6 31 := by decide +kernel
theorem column6_at32 : SheetColumnAtPoint 6 32 := by decide +kernel
theorem column6_at33 : SheetColumnAtPoint 6 33 := by decide +kernel
theorem column6_at34 : SheetColumnAtPoint 6 34 := by decide +kernel
theorem column6_at35 : SheetColumnAtPoint 6 35 := by decide +kernel
theorem column6_at36 : SheetColumnAtPoint 6 36 := by decide +kernel
theorem column6_at37 : SheetColumnAtPoint 6 37 := by decide +kernel
theorem column6_at38 : SheetColumnAtPoint 6 38 := by decide +kernel

theorem column6_all_points (p : Fin 39) : SheetColumnAtPoint 6 p := by
  revert p
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 6 0 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 6 1 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 6 2 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at3, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at4, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at5, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at6, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at7, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at8, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at9, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at10, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at11, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 6 12 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 6 13 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 6 14 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 6 15 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 6 16 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 6 17 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 6 18 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 6 19 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨sheetColumn_at_anchor 6 20 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at21, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at22, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at23, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at24, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at25, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at26, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at27, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at28, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at29, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at30, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at31, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at32, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at33, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at34, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at35, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at36, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at37, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_at38, ?_⟩
  exact Fin.forall_fin_zero.mpr trivial

theorem column6_all_coordinates (v : Fin 1053) :
    d6Column 6 v = Q12.toComplex (q12SheetColumn 6 (Fin.divNat (n := 27) v)
      (Fin.modNat (m := 39) v)) := by
  let p : Fin 39 := Fin.divNat (n := 27) v
  let k : Fin 27 := Fin.modNat (m := 39) v
  have h := column6_all_points p k
  have he : (⟨27 * p.val + k.val, by omega⟩ : Fin 1053) = v := by
    apply Fin.ext
    change 27 * (v.val / 27) + v.val % 27 = v.val
    omega
  rw [he] at h
  rw [← d6ColumnQ12_complex, h]

end Option2.NativeStress.BookHT.TangentCoordinates

#check Option2.NativeStress.BookHT.TangentCoordinates.column6_all_coordinates
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.column6_all_coordinates

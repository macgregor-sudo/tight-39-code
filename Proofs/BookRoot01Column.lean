module

public import BookRoot01FirstQuartet

/-! Exact full1053-coordinate comparison for D6 sheet0/E01. -/

@[expose] public section
set_option Elab.async false

namespace Option2.NativeStress.BookHT.TangentCoordinates

theorem root01_at21 : Root01AtPoint 21 := by decide +kernel
theorem root01_at22 : Root01AtPoint 22 := by decide +kernel
theorem root01_at23 : Root01AtPoint 23 := by decide +kernel
theorem root01_at24 : Root01AtPoint 24 := by decide +kernel
theorem root01_at25 : Root01AtPoint 25 := by decide +kernel
theorem root01_at26 : Root01AtPoint 26 := by decide +kernel
theorem root01_at27 : Root01AtPoint 27 := by decide +kernel
theorem root01_at28 : Root01AtPoint 28 := by decide +kernel
theorem root01_at29 : Root01AtPoint 29 := by decide +kernel
theorem root01_at30 : Root01AtPoint 30 := by decide +kernel
theorem root01_at31 : Root01AtPoint 31 := by decide +kernel
theorem root01_at32 : Root01AtPoint 32 := by decide +kernel
theorem root01_at33 : Root01AtPoint 33 := by decide +kernel
theorem root01_at34 : Root01AtPoint 34 := by decide +kernel
theorem root01_at35 : Root01AtPoint 35 := by decide +kernel
theorem root01_at36 : Root01AtPoint 36 := by decide +kernel
theorem root01_at37 : Root01AtPoint 37 := by decide +kernel
theorem root01_at38 : Root01AtPoint 38 := by decide +kernel

theorem root01_at_anchor (p : Fin 39) (hp : p.val < 12) : Root01AtPoint p := by
  intro k
  let v : Fin 1053 := ⟨27 * p.val + k.val, by omega⟩
  have hv : AnchorSupport.AnchorCoordinate (d6Sheet 0) v := by
    change v.val / 81 = 0 ∨ (1 + 3 * (d6Sheet 0).val ≤ v.val / 81 ∧
      v.val / 81 ≤ 3 + 3 * (d6Sheet 0).val)
    change (27 * p.val + k.val) / 81 = 0 ∨
      (1 ≤ (27 * p.val + k.val) / 81 ∧ (27 * p.val + k.val) / 81 ≤ 3)
    omega
  have hzero : d6ColumnQ12 0 v = 0 := by
    apply Q12.toComplex_injective
    rw [d6ColumnQ12_complex, d6Column_anchor_zero 0 v hv, map_zero]
  change d6ColumnQ12 0 v = q12SeedRoot01Fast v
  rw [hzero, q12SeedRoot01Fast, ite_eq_left (by dsimp [v]; omega)]

theorem root01_all_points (p : Fin 39) : Root01AtPoint p := by
  revert p
  refine Fin.forall_fin_succ.mpr ⟨root01_at_anchor 0 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at_anchor 1 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at_anchor 2 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at_anchor 3 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at_anchor 4 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at_anchor 5 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at_anchor 6 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at_anchor 7 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at_anchor 8 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at_anchor 9 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at_anchor 10 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at_anchor 11 (by decide), ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at12, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at13, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at14, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at15, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at16, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at17, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at18, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at19, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at20, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at21, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at22, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at23, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at24, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at25, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at26, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at27, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at28, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at29, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at30, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at31, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at32, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at33, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at34, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at35, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at36, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at37, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨root01_at38, ?_⟩
  exact Fin.forall_fin_zero.mpr trivial

theorem root01_all_coordinates (v : Fin 1053) :
    d6Column 0 v = Q12.toComplex (q12SeedRoot01 v) := by
  let p : Fin 39 := Fin.divNat (n := 27) v
  let k : Fin 27 := Fin.modNat (m := 39) v
  have h := root01_all_points p k
  have he : (⟨27 * p.val + k.val, by omega⟩ : Fin 1053) = v := by
    apply Fin.ext
    change 27 * (v.val / 27) + v.val % 27 = v.val
    omega
  rw [he, q12SeedRoot01Fast_eq] at h
  rw [← d6ColumnQ12_complex, h]

end Option2.NativeStress.BookHT.TangentCoordinates

#check Option2.NativeStress.BookHT.TangentCoordinates.root01_all_coordinates
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.root01_all_coordinates

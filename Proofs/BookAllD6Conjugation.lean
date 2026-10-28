module

public import BookRoot01Column
public import BookSheetOneColumn
public import BookSheetRealStructure
public import BookRootColumn1
public import BookRootColumn3
public import BookRootColumn7
public import BookRootColumn9
public import BookRootColumn12
public import BookRootColumn13
public import BookRootColumn15
public import BookRootColumn18
public import BookRootColumn19
public import BookRootColumn21

@[expose] public section

/-! Every literal D6 column equals the exact signed, anchor-masked conjugation formula. -/
set_option Elab.async false
namespace Option2.NativeStress.BookHT.TangentCoordinates
open Option2.BookNativeBase

theorem q12SheetColumn_zero (p : Fin 39) (k : Fin 27) :
    q12SheetColumn 0 p k = q12SeedRoot01 ⟨27*p.val+k.val, by omega⟩ := by
  have hi : (27*p.val+k.val)/27 = p.val := by omega
  have hk : (27*p.val+k.val)%27 = k.val := by omega
  have hanchor : (p.val/3 = 0 ∨ (1 ≤ p.val/3 ∧ p.val/3 ≤ 3)) ↔ p.val < 12 := by omega
  have hmat : (Matrix.single (0 : Fin 3) (1 : Fin 3) (1 : Q12)) = q12Root01 := by decide +kernel
  have hroot (x : Fin 27 → Q12) : q12RootCoordinates 0 1 x = q12Conjugation q12Root01 x := by
    rw [q12RootCoordinates_eq, hmat]
  unfold q12SheetColumn q12SeedRoot01
  simp only [d6Sheet, rootPair, q12SheetTransport, q12SheetInverse, hi, hk]
  change (if p.val/3 = 0 ∨ (1 ≤ p.val/3 ∧ p.val/3 ≤ 3)
      then (0 : Fin 27 → Q12) else q12RootCoordinates 0 1 (bookPointQ12 p)) k =
    if p.val < 12 then 0 else
      q12Conjugation q12Root01
        (fun j => bookQ12 ⟨27*p.val+j.val, by omega⟩) ⟨k.val, by omega⟩
  have hb : (fun j : Fin 27 => bookQ12 ⟨27*p.val+j.val, by omega⟩) = bookPointQ12 p := by
    funext j
    unfold bookQ12
    congr 1 <;> apply Fin.ext <;> dsimp <;> omega
  rw [hb]
  by_cases hp : p.val < 12
  · simp only [hanchor.mpr hp, hp, ite_true, Pi.zero_apply]
  · simp only [mt hanchor.mp hp, hp, ite_false, hroot]

theorem column0_all_points (p : Fin 39) : SheetColumnAtPoint 0 p := by
  intro k
  apply Q12.toComplex_injective
  rw [d6ColumnQ12_complex, root01_all_coordinates, q12SheetColumn_zero]

theorem columnMatch_bar (b : Fin 24) (h : ∀ p, SheetColumnAtPoint b p) :
    ∀ p, SheetColumnAtPoint (basisBar b) p := by
  intro p k
  apply Q12.toComplex_injective
  rw [d6ColumnQ12_complex, d6Column_bar, ← d6ColumnQ12_complex, h p k,
    q12SheetColumn_bar, map_neg, Q12.toComplex_conj]

theorem d6_all_points : ∀ b : Fin 24, ∀ p, SheetColumnAtPoint b p := by
  refine Fin.forall_fin_succ.mpr ⟨column0_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column1_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨columnMatch_bar 0 column0_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column3_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨columnMatch_bar 1 column1_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨columnMatch_bar 3 column3_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column6_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column7_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨columnMatch_bar 6 column6_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column9_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨columnMatch_bar 7 column7_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨columnMatch_bar 9 column9_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column12_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column13_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨columnMatch_bar 12 column12_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column15_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨columnMatch_bar 13 column13_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨columnMatch_bar 15 column15_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column18_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column19_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨columnMatch_bar 18 column18_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨column21_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨columnMatch_bar 19 column19_all_points, ?_⟩
  refine Fin.forall_fin_succ.mpr ⟨columnMatch_bar 21 column21_all_points, ?_⟩
  exact Fin.forall_fin_zero.mpr trivial

theorem d6_all_coordinates (b : Fin 24) (v : Fin 1053) :
    d6Column b v = Q12.toComplex (q12SheetColumn b (Fin.divNat (n := 27) v)
      (Fin.modNat (m := 39) v)) := by
  let p : Fin 39 := Fin.divNat (n := 27) v
  let k : Fin 27 := Fin.modNat (m := 39) v
  have h := d6_all_points b p k
  have he : (⟨27 * p.val + k.val, by omega⟩ : Fin 1053) = v := by
    apply Fin.ext
    change 27 * (v.val / 27) + v.val % 27 = v.val
    omega
  rw [he] at h
  rw [← d6ColumnQ12_complex, h]

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.d6_all_coordinates
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.d6_all_coordinates


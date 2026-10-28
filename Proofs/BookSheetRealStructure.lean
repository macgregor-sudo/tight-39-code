module

public import BookConjugationRealStructure

@[expose] public section

/-! The literal real Book base and the existing signed transports respect conjugation. -/
set_option Elab.async false
namespace Option2.NativeStress.BookHT.TangentCoordinates
open Option2.BookNativeBase

theorem bookPointQ12_conj (p : Fin 39) (k : Fin 27) :
    Q12.conj (bookPointQ12 p k) = bookPointQ12 p k := by
  let v : Fin 1053 := ⟨27 * p.val + k.val, by omega⟩
  have hv : bookQ12 v = bookPointQ12 p k := by
    unfold bookQ12
    congr 1 <;> apply Fin.ext <;> dsimp [v] <;> omega
  rw [← hv]
  apply Q12.toComplex_injective
  rw [Q12.toComplex_conj, ← bookBase_complex]
  exact Complex.conj_ofReal _

private theorem signed_conj (p : Fin 27 → Fin 27) (sg : Fin 27 → ℤ)
    (x : Fin 27 → Q12) :
    TitsS.sgnPerm p sg (fun k => Q12.conj (x k)) =
      fun k => Q12.conj (TitsS.sgnPerm p sg x k) := by
  funext k
  simp [TitsS.sgnPerm, -Q12.conj_apply]

private theorem signed_neg (p : Fin 27 → Fin 27) (sg : Fin 27 → ℤ)
    (x : Fin 27 → Q12) :
    TitsS.sgnPerm p sg (-x) = -TitsS.sgnPerm p sg x := by
  funext k
  simp [TitsS.sgnPerm]

theorem q12SheetTransport_conj (s : Fin 4) (x : Fin 27 → Q12) :
    q12SheetTransport s (fun k => Q12.conj (x k)) =
      fun k => Q12.conj (q12SheetTransport s x k) := by
  fin_cases s <;> simp only [q12SheetTransport]
  · rfl
  · exact signed_conj _ _ _
  · exact signed_conj _ _ _
  · exact signed_conj _ _ _

theorem q12SheetTransport_neg (s : Fin 4) (x : Fin 27 → Q12) :
    q12SheetTransport s (-x) = -q12SheetTransport s x := by
  fin_cases s <;> simp only [q12SheetTransport]
  · rfl
  · exact signed_neg _ _ _
  · exact signed_neg _ _ _
  · exact signed_neg _ _ _

theorem q12SheetInverse_conj (s : Fin 4) (x : Fin 27 → Q12) :
    q12SheetInverse s (fun k => Q12.conj (x k)) =
      fun k => Q12.conj (q12SheetInverse s x k) := by
  fin_cases s <;> simp only [q12SheetInverse]
  · rfl
  · exact signed_conj _ _ _
  · exact signed_conj _ _ _
  · exact signed_conj _ _ _

theorem basisBar_sheet_root : ∀ b : Fin 24,
    d6Sheet (basisBar b) = d6Sheet b ∧
    rootPair ⟨(basisBar b).val % 6, Nat.mod_lt _ (by decide)⟩ =
      (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).swap := by
  decide +kernel

theorem q12SheetColumn_bar (b : Fin 24) (p : Fin 39) (k : Fin 27) :
    q12SheetColumn (basisBar b) p k = -Q12.conj (q12SheetColumn b p k) := by
  have hs := (basisBar_sheet_root b).1
  have hr := (basisBar_sheet_root b).2
  simp only [q12SheetColumn, hs, hr]
  split_ifs with hp
  · simp only [Pi.zero_apply, map_zero, neg_zero]
  · let x := q12SheetInverse (d6Sheet b) (bookPointQ12 p)
    have hx : (fun j => Q12.conj (x j)) = x := by
      change (fun j => Q12.conj (q12SheetInverse (d6Sheet b) (bookPointQ12 p) j)) = _
      rw [← q12SheetInverse_conj]
      congr 1
      funext j
      exact bookPointQ12_conj p j
    have hroot : q12RootCoordinates
        (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).2
        (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).1 x =
        -(fun j => Q12.conj (q12RootCoordinates
          (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).1
          (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).2 x j)) := by
      funext j
      have h := q12RootCoordinates_conj
        (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).1
        (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).2 x j
      rw [hx] at h
      exact h
    change q12SheetTransport (d6Sheet b) (q12RootCoordinates
      (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).2
      (rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩).1 x) k = _
    rw [hroot, q12SheetTransport_neg, q12SheetTransport_conj]
    rfl

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.q12SheetColumn_bar
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.q12SheetColumn_bar


module

public import BookSheetConjugation

@[expose] public section

/-! Real-structure compatibility of the existing sparse root formula. -/
set_option Elab.async false
namespace Option2.NativeStress.BookHT.TangentCoordinates
open Option2.BookNativeBase

private theorem q12_conj_I : Q12.conj Q12.I = -Q12.I := by decide +kernel
private theorem q12_conj_rat (r : ℚ) : Q12.conj (Q12.ofRat r) = Q12.ofRat r := by
  apply Q12.toComplex_injective
  rw [Q12.toComplex_conj, Q12.toComplex_ofRat]
  simp

theorem q12Partner_conj (x : Fin 27 → Q12) :
    q12Partner (fun k => Q12.conj (x k)) =
      fun i j => Q12.conj (q12Hidden x i j) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [q12Partner, q12Hidden, q12_conj_I, -Q12.conj_apply] <;> ring

theorem q12Hidden_conj (x : Fin 27 → Q12) :
    q12Hidden (fun k => Q12.conj (x k)) =
      fun i j => Q12.conj (q12Partner x i j) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [q12Partner, q12Hidden, q12_conj_I, -Q12.conj_apply] <;> ring

theorem q12HiddenCoordinates_conj (B Bt : Matrix (Fin 3) (Fin 3) Q12) (k : Fin 27) :
    Q12.conj (q12HiddenCoordinates B Bt k) =
      q12HiddenCoordinates (fun i j => Q12.conj (Bt i j))
        (fun i j => Q12.conj (B i j)) k := by
  fin_cases k <;>
    simp [q12HiddenCoordinates, q12_conj_I, q12_conj_rat, -Q12.conj_apply] <;> ring

theorem q12HiddenCoordinates_neg (B Bt : Matrix (Fin 3) (Fin 3) Q12) (k : Fin 27) :
    q12HiddenCoordinates (-B) (-Bt) k = -q12HiddenCoordinates B Bt k := by
  fin_cases k <;>
    simp [q12HiddenCoordinates] <;> ring

theorem q12RootHidden_conj (a b : Fin 3) (B : Matrix (Fin 3) (Fin 3) Q12) :
    q12RootHidden a b (fun i j => Q12.conj (B i j)) =
      fun i j => Q12.conj (q12RootHidden a b B i j) := by
  funext i j
  by_cases hi : i = a <;> by_cases hj : j = b <;>
    simp [q12RootHidden, hi, hj, -Q12.conj_apply]

theorem q12RootCoordinates_conj (a b : Fin 3) (x : Fin 27 → Q12) (k : Fin 27) :
    q12RootCoordinates b a (fun j => Q12.conj (x j)) k =
      -Q12.conj (q12RootCoordinates a b x k) := by
  simp only [q12RootCoordinates, q12RootPartner, q12Partner_conj, q12Hidden_conj,
    q12RootHidden_conj, q12HiddenCoordinates_conj]
  let B : Matrix (Fin 3) (Fin 3) Q12 :=
    Matrix.of (fun i j => Q12.conj (q12RootHidden b a (q12Partner x) i j))
  let C : Matrix (Fin 3) (Fin 3) Q12 :=
    Matrix.of (fun i j => Q12.conj (q12RootHidden a b (q12Hidden x) i j))
  change q12HiddenCoordinates B (-C) k =
    -q12HiddenCoordinates (Matrix.of (fun i j => Q12.conj ((-q12RootHidden b a (q12Partner x)) i j))) C k
  have hn : Matrix.of (fun i j => Q12.conj ((-q12RootHidden b a (q12Partner x)) i j)) = -B := by
    apply Matrix.ext
    intro i j
    change Q12.conj (-q12RootHidden b a (q12Partner x) i j) =
      -Q12.conj (q12RootHidden b a (q12Partner x) i j)
    exact map_neg Q12.conj _
  rw [hn]
  simpa only [neg_neg] using q12HiddenCoordinates_neg (-B) C k

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.q12RootCoordinates_conj
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.q12RootCoordinates_conj


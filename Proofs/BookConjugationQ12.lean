module

public import BookTangentQ12

/-!
Literal Q12 coordinate formula for hidden simultaneous conjugation. This is
the coefficient formula to be compared with the unchanged D6 payload; its
identification with the accepted native Tits maps is a separate proof obligation.
The x22 sign follows native octonionFromTitsRow, not the erroneous producer
markdown row. No originalF or tangent assertion is made in this data formula.
-/

@[expose] public section
set_option Elab.async false

namespace Option2.NativeStress.BookHT.TangentCoordinates

open Option2.BookNativeBase

def q12Hidden (x : Fin 27 → Q12) : Matrix (Fin 3) (Fin 3) Q12 :=
  !![-x 21 + Q12.I * x 22, -x 23 + Q12.I * x 24, -x 25 - Q12.I * x 26;
      x 13 - Q12.I * x 14,  x 15 - Q12.I * x 16,  x 17 + Q12.I * x 18;
     -x 5 + Q12.I * x 6,   -x 7 + Q12.I * x 8,   -x 9 - Q12.I * x 10]

def q12Partner (x : Fin 27 → Q12) : Matrix (Fin 3) (Fin 3) Q12 :=
  !![-x 21 - Q12.I * x 22, -x 23 - Q12.I * x 24, -x 25 + Q12.I * x 26;
      x 13 + Q12.I * x 14,  x 15 + Q12.I * x 16,  x 17 - Q12.I * x 18;
     -x 5 - Q12.I * x 6,   -x 7 - Q12.I * x 8,   -x 9 + Q12.I * x 10]

def q12HiddenCoordinates (B Bt : Matrix (Fin 3) (Fin 3) Q12) : Fin 27 → Q12 :=
  let h := Q12.ofRat (1/2)
  ![0, 0, 0, 0, 0,
    -h*(B 2 0 + Bt 2 0), -Q12.I*h*(B 2 0 - Bt 2 0),
    -h*(B 2 1 + Bt 2 1), -Q12.I*h*(B 2 1 - Bt 2 1),
    -h*(B 2 2 + Bt 2 2), Q12.I*h*(B 2 2 - Bt 2 2), 0, 0,
     h*(B 1 0 + Bt 1 0), Q12.I*h*(B 1 0 - Bt 1 0),
     h*(B 1 1 + Bt 1 1), Q12.I*h*(B 1 1 - Bt 1 1),
     h*(B 1 2 + Bt 1 2), -Q12.I*h*(B 1 2 - Bt 1 2), 0, 0,
    -h*(B 0 0 + Bt 0 0), -Q12.I*h*(B 0 0 - Bt 0 0),
    -h*(B 0 1 + Bt 0 1), -Q12.I*h*(B 0 1 - Bt 0 1),
    -h*(B 0 2 + Bt 0 2), Q12.I*h*(B 0 2 - Bt 0 2)]

def q12Conjugation (G : Matrix (Fin 3) (Fin 3) Q12) (x : Fin 27 → Q12) : Fin 27 → Q12 :=
  q12HiddenCoordinates (G * q12Hidden x - q12Hidden x * G)
    (-G.transpose * q12Partner x + q12Partner x * G.transpose)

def q12Root01 : Matrix (Fin 3) (Fin 3) Q12 := !![0,1,0; 0,0,0; 0,0,0]

def q12Root01Hidden (B : Matrix (Fin 3) (Fin 3) Q12) : Matrix (Fin 3) (Fin 3) Q12 :=
  !![B 1 0, B 1 1 - B 0 0, B 1 2; 0, -B 1 0, 0; 0, -B 2 0, 0]

def q12Root01Partner (Bt : Matrix (Fin 3) (Fin 3) Q12) : Matrix (Fin 3) (Fin 3) Q12 :=
  !![Bt 0 1, 0, 0; Bt 1 1 - Bt 0 0, -Bt 0 1, -Bt 0 2; Bt 2 1, 0, 0]

theorem q12Root01Hidden_eq (B : Matrix (Fin 3) (Fin 3) Q12) :
    q12Root01Hidden B = q12Root01 * B - B * q12Root01 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [q12Root01Hidden, q12Root01, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

theorem q12Root01Partner_eq (Bt : Matrix (Fin 3) (Fin 3) Q12) :
    q12Root01Partner Bt = -q12Root01.transpose * Bt + Bt * q12Root01.transpose := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [q12Root01Partner, q12Root01, Matrix.mul_apply,
      Fin.sum_univ_succ, sub_eq_add_neg] <;> exact add_comm _ _

def q12Root01Coordinates (x : Fin 27 → Q12) : Fin 27 → Q12 :=
  q12HiddenCoordinates (q12Root01Hidden (q12Hidden x)) (q12Root01Partner (q12Partner x))

theorem q12Root01Coordinates_eq (x : Fin 27 → Q12) :
    q12Root01Coordinates x = q12Conjugation q12Root01 x := by
  rw [q12Root01Coordinates, q12Root01Hidden_eq, q12Root01Partner_eq]
  rfl

noncomputable def q12SeedRoot01Fast (v : Fin 1053) : Q12 :=
  if v.val / 27 < 12 then 0 else
    q12Root01Coordinates
      (fun k => bookQ12 ⟨27 * (v.val / 27) + k.val, by omega⟩) ⟨v.val % 27, Nat.mod_lt _ (by decide)⟩

noncomputable def q12SeedRoot01 (v : Fin 1053) : Q12 :=
  if v.val / 27 < 12 then 0 else
    q12Conjugation q12Root01
      (fun k => bookQ12 ⟨27 * (v.val / 27) + k.val, by omega⟩) ⟨v.val % 27, Nat.mod_lt _ (by decide)⟩

theorem root01_point12 : ∀ k : Fin 27,
    d6ColumnQ12 0 ⟨324 + k.val, by omega⟩ = q12SeedRoot01 ⟨324 + k.val, by omega⟩ := by
  decide +kernel

theorem q12SeedRoot01Fast_eq (v : Fin 1053) : q12SeedRoot01Fast v = q12SeedRoot01 v := by
  unfold q12SeedRoot01Fast q12SeedRoot01
  split_ifs
  · rfl
  · rw [q12Root01Coordinates_eq]

end Option2.NativeStress.BookHT.TangentCoordinates

#check Option2.NativeStress.BookHT.TangentCoordinates.root01_point12
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.root01_point12
#check Option2.NativeStress.BookHT.TangentCoordinates.q12Root01Coordinates_eq
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.q12Root01Coordinates_eq

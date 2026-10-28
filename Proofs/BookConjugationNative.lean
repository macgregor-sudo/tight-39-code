module

public import BookConjugationQ12
public import NativeIncludedQuartetReadouts

/-! The Q12 hidden-coordinate formula has the actual native real form. -/

@[expose] public section
set_option Elab.async false
noncomputable section

namespace Option2.NativeStress.BookHT.TangentCoordinates

open CompactAlbert NativePolynomial

theorem q12HiddenCoordinates_native
    (B : Matrix (Fin 3) (Fin 3) Q12) (k : Fin 27) :
    Q12.toComplex (q12HiddenCoordinates B (fun i j => Q12.conj (B i j)) k) =
      ((upperCoordinates (fromTitsCoordinates
        (0, 0, fun i j => Q12.toComplex (B i j))) k : ℝ) : ℂ) := by
  fin_cases k <;> apply Complex.ext <;>
    simp [q12HiddenCoordinates, map_mul, map_sub, map_add, map_neg,
      Q12.toComplex_ofRat, Q12.toComplex_I, Q12.toComplex_conj,
      upperCoordinates, fromTitsCoordinates, octonionFromTitsRow, Glennie.octConj,
      -Q12.conj_apply] <;> ring

end Option2.NativeStress.BookHT.TangentCoordinates

#check Option2.NativeStress.BookHT.TangentCoordinates.q12HiddenCoordinates_native
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.q12HiddenCoordinates_native

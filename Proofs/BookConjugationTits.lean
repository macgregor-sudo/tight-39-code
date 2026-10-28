module

public import BookConjugationNative
public import TitsForm

@[expose] public section

/-!
The computational formulas reuse the existing complexified Tits owner.
This local compatibility companion uses the imported TitsForm legacy module
format; its accepted source/object is unchanged. No submission-format closure
is inferred from this ordinary local composition.
-/

set_option Elab.async false

namespace Option2.NativeStress.BookHT.TangentCoordinates

theorem q12Hidden_eq_titsOfNative (x : Fin 27 → Q12) :
    q12Hidden x = (TitsS.titsOfNative (RingHom.id Q12) x).2.1 := rfl

theorem q12Partner_eq_titsOfNative (x : Fin 27 → Q12) :
    q12Partner x = (TitsS.titsOfNative (RingHom.id Q12) x).2.2 := rfl

theorem q12HiddenCoordinates_eq_titsToNative
    (B Bt : Matrix (Fin 3) (Fin 3) Q12) :
    q12HiddenCoordinates B Bt =
      TitsS.titsToNative (RingHom.id Q12) TitsS.half (0, B, Bt) := by
  funext k
  fin_cases k <;>
    simp [q12HiddenCoordinates, TitsS.titsToNative, TitsS.half, Q12.ofRat]

end Option2.NativeStress.BookHT.TangentCoordinates

#check Option2.NativeStress.BookHT.TangentCoordinates.q12HiddenCoordinates_eq_titsToNative
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.q12HiddenCoordinates_eq_titsToNative

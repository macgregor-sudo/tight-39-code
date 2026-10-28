module

public import BookNativeBaseBinding
public import BookAxisAnchorCompatibility

/-!
Exact computable interpretation of the unchanged Book D6 sparse columns.
The field map is proved equal to the accepted complex evaluator; no tangent
identity or finite comparison is assumed. First-party composition only.
-/

@[expose] public section

set_option Elab.async false

namespace Option2.NativeStress.BookHT.TangentCoordinates

def coefficientQ12 (q : Coeff) : Q12 :=
  Q12.lit q.1 q.2.1 q.2.2.1 q.2.2.2 denominator

theorem coefficientQ12_complex (q : Coeff) :
    Q12.toComplex (coefficientQ12 q) = coefficient q := by
  rw [coefficientQ12, Q12.toComplex_lit]
  rfl

def sparseQ12 : List Entry → Fin 1053 → Q12
  | [], _ => 0
  | e :: es, r => if r = e.1 then coefficientQ12 e.2 + sparseQ12 es r else sparseQ12 es r

theorem sparseQ12_complex (es : List Entry) (r : Fin 1053) :
    Q12.toComplex (sparseQ12 es r) = sparseValue es r := by
  induction es with
  | nil => exact map_zero Q12.toComplex
  | cons e es ih =>
    change Q12.toComplex (if r = e.1 then coefficientQ12 e.2 + sparseQ12 es r else sparseQ12 es r) =
      (if r = e.1 then coefficient e.2 else 0) + sparseValue es r
    by_cases h : r = e.1
    · rw [if_pos h, if_pos h, map_add, coefficientQ12_complex, ih]
    · rw [if_neg h, if_neg h, zero_add, ih]

noncomputable def d6ColumnQ12 (b : Fin 24) (r : Fin 1053) : Q12 := sparseQ12 (d6Entries b) r

theorem d6ColumnQ12_complex (b : Fin 24) (r : Fin 1053) :
    Q12.toComplex (d6ColumnQ12 b r) = d6Column b r :=
  sparseQ12_complex (d6Entries b) r

end Option2.NativeStress.BookHT.TangentCoordinates

#check Option2.NativeStress.BookHT.TangentCoordinates.d6ColumnQ12_complex
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.d6ColumnQ12_complex

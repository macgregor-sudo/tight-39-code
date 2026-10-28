module

public import BookNativeConjugationFamily
public import BookAllD6Conjugation

@[expose] public section

/-! Exact real/imaginary projection of the complexified hidden Tits coordinates. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.BookHT.TangentCoordinates
open NativePolynomial CompactAlbert

def complexHiddenCoordinates (B Bt : TitsComplexMatrix) : Fin 27 → ℂ :=
  TitsS.titsToNative Q12.toComplex (1/2) (0, B, Bt)

theorem q12HiddenCoordinates_complex (B Bt : Matrix (Fin 3) (Fin 3) Q12) (k : Fin 27) :
    Q12.toComplex (q12HiddenCoordinates B Bt k) =
      complexHiddenCoordinates (Q12.toComplex.mapMatrix B) (Q12.toComplex.mapMatrix Bt) k := by
  fin_cases k <;>
    simp [q12HiddenCoordinates, complexHiddenCoordinates, TitsS.titsToNative,
      Q12.toComplex_ofRat, Q12.toComplex_I, RingHom.mapMatrix_apply]

theorem complexHiddenCoordinates_re (B D : TitsComplexMatrix) (k : Fin 27) :
    (complexHiddenCoordinates B (-D.map (starRingEnd ℂ)) k).re =
      upperCoordinates (fromTitsCoordinates (0, 0, (1/2 : ℂ) • (B-D))) k := by
  fin_cases k <;>
    simp [complexHiddenCoordinates, TitsS.titsToNative, Q12.toComplex_I,
      upperCoordinates, fromTitsCoordinates, octonionFromTitsRow, Glennie.octConj] <;> ring

theorem complexHiddenCoordinates_im (B D : TitsComplexMatrix) (k : Fin 27) :
    (complexHiddenCoordinates B (-D.map (starRingEnd ℂ)) k).im =
      upperCoordinates (fromTitsCoordinates (0, 0, (-Complex.I/2) • (B+D))) k := by
  fin_cases k <;>
    simp [complexHiddenCoordinates, TitsS.titsToNative, Q12.toComplex_I,
      upperCoordinates, fromTitsCoordinates, octonionFromTitsRow, Glennie.octConj] <;> ring

theorem q12Hidden_native_of_real (x : Fin 27 → Q12) (r : Fin 27 → ℝ)
    (hx : ∀ k, Q12.toComplex (x k) = (r k : ℂ)) :
    Q12.toComplex.mapMatrix (q12Hidden x) =
      (nativeTitsMatrixPair (fromUpperCoordinates r)).2 := by
  apply Matrix.ext
  intro i j
  change Q12.toComplex (q12Hidden x i j) =
    (toTitsCoordinates (fromUpperCoordinates r)).2.2 i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [q12Hidden, hx, Q12.toComplex_I, toTitsCoordinates, fromUpperCoordinates,
      octonionToTitsRow, Glennie.octConj]

theorem q12RootHidden_complex (a b : Fin 3) (B : Matrix (Fin 3) (Fin 3) Q12) :
    Q12.toComplex.mapMatrix (q12RootHidden a b B) =
      Matrix.single a b 1 * Q12.toComplex.mapMatrix B -
        Q12.toComplex.mapMatrix B * Matrix.single a b 1 := by
  rw [q12RootHidden_eq, map_sub, map_mul, map_mul]
  have hs : Q12.toComplex.mapMatrix (Matrix.single a b 1) =
      Matrix.single a b (1 : ℂ) := by
    apply Matrix.ext
    intro i j
    simp [Matrix.single, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [hs]

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.complexHiddenCoordinates_re
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.complexHiddenCoordinates_re
#check Option2.NativeStress.BookHT.TangentCoordinates.complexHiddenCoordinates_im
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.complexHiddenCoordinates_im
#check Option2.NativeStress.BookHT.TangentCoordinates.q12Hidden_native_of_real
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.q12Hidden_native_of_real


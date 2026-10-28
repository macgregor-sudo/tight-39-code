module

public import BookRootRealImagNative

@[expose] public section

/-! Both real components of each root column are native skew-Hermitian conjugation velocities. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.BookHT.TangentCoordinates
open NativePolynomial CompactAlbert CKM.NativeFourFamily
open scoped Matrix

def rootRealGenerator (a b : Fin 3) : TitsComplexMatrix :=
  (1/2 : ℂ) • (Matrix.single a b 1 - Matrix.single b a 1)

def rootImagGenerator (a b : Fin 3) : TitsComplexMatrix :=
  (-Complex.I/2) • (Matrix.single a b 1 + Matrix.single b a 1)

theorem q12RootCoordinates_complex_real (a b : Fin 3) (x : Fin 27 → Q12)
    (r : Fin 27 → ℝ) (hx : ∀ k, Q12.toComplex (x k) = (r k : ℂ)) (k : Fin 27) :
    Q12.toComplex (q12RootCoordinates a b x k) =
      complexHiddenCoordinates
        (Matrix.single a b 1 * (nativeTitsMatrixPair (fromUpperCoordinates r)).2 -
          (nativeTitsMatrixPair (fromUpperCoordinates r)).2 * Matrix.single a b 1)
        (-((Matrix.single b a 1 * (nativeTitsMatrixPair (fromUpperCoordinates r)).2 -
          (nativeTitsMatrixPair (fromUpperCoordinates r)).2 * Matrix.single b a 1).map
            (starRingEnd ℂ))) k := by
  have hcx : (fun j => Q12.conj (x j)) = x := by
    funext j
    apply Q12.toComplex_injective
    rw [Q12.toComplex_conj, hx]
    exact Complex.conj_ofReal _
  have hp : q12Partner x = Q12.conj.mapMatrix (q12Hidden x) := by
    have h := q12Partner_conj x
    rw [hcx] at h
    exact h
  have hr : q12RootHidden b a (Q12.conj.mapMatrix (q12Hidden x)) =
      Q12.conj.mapMatrix (q12RootHidden b a (q12Hidden x)) :=
    q12RootHidden_conj b a (q12Hidden x)
  have hc (M : Matrix (Fin 3) (Fin 3) Q12) :
      Q12.toComplex.mapMatrix (Q12.conj.mapMatrix M) =
        (Q12.toComplex.mapMatrix M).map (starRingEnd ℂ) := by
    apply Matrix.ext
    intro i j
    exact Q12.toComplex_conj (M i j)
  rw [q12RootCoordinates, q12HiddenCoordinates_complex, q12RootPartner,
    map_neg, hp, hr, hc, q12RootHidden_complex, q12RootHidden_complex,
    q12Hidden_native_of_real x r hx]

theorem nativeHiddenConjugation_fromTits (X : TitsComplexMatrix) (v : Glennie.Albert) :
    nativeHiddenConjugation X v = fromTitsCoordinates
      (0, 0, X * (nativeTitsMatrixPair v).2 - (nativeTitsMatrixPair v).2 * X) := rfl

theorem q12RootCoordinates_re_native (a b : Fin 3) (x : Fin 27 → Q12)
    (v : Glennie.Albert) (hx : ∀ k, Q12.toComplex (x k) = (upperCoordinates v k : ℂ))
    (k : Fin 27) :
    (Q12.toComplex (q12RootCoordinates a b x k)).re =
      upperCoordinates (nativeHiddenConjugation (rootRealGenerator a b) v) k := by
  rw [q12RootCoordinates_complex_real a b x (upperCoordinates v) hx,
    fromUpperCoordinates_upperCoordinates, complexHiddenCoordinates_re,
    nativeHiddenConjugation_fromTits]
  have he : (1/2 : ℂ) •
      (Matrix.single a b 1 * (nativeTitsMatrixPair v).2 -
        (nativeTitsMatrixPair v).2 * Matrix.single a b 1 -
        (Matrix.single b a 1 * (nativeTitsMatrixPair v).2 -
          (nativeTitsMatrixPair v).2 * Matrix.single b a 1)) =
      rootRealGenerator a b * (nativeTitsMatrixPair v).2 -
        (nativeTitsMatrixPair v).2 * rootRealGenerator a b := by
    simp only [rootRealGenerator, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.sub_mul, Matrix.mul_sub, smul_sub]
    abel
  rw [he]

theorem q12RootCoordinates_im_native (a b : Fin 3) (x : Fin 27 → Q12)
    (v : Glennie.Albert) (hx : ∀ k, Q12.toComplex (x k) = (upperCoordinates v k : ℂ))
    (k : Fin 27) :
    (Q12.toComplex (q12RootCoordinates a b x k)).im =
      upperCoordinates (nativeHiddenConjugation (rootImagGenerator a b) v) k := by
  rw [q12RootCoordinates_complex_real a b x (upperCoordinates v) hx,
    fromUpperCoordinates_upperCoordinates, complexHiddenCoordinates_im,
    nativeHiddenConjugation_fromTits]
  have he : (-Complex.I/2) •
      (Matrix.single a b 1 * (nativeTitsMatrixPair v).2 -
        (nativeTitsMatrixPair v).2 * Matrix.single a b 1 +
        (Matrix.single b a 1 * (nativeTitsMatrixPair v).2 -
          (nativeTitsMatrixPair v).2 * Matrix.single b a 1)) =
      rootImagGenerator a b * (nativeTitsMatrixPair v).2 -
        (nativeTitsMatrixPair v).2 * rootImagGenerator a b := by
    simp only [rootImagGenerator, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.add_mul, Matrix.mul_add, smul_sub, smul_add]
    abel
  rw [he]

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.q12RootCoordinates_re_native
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.q12RootCoordinates_re_native
#check Option2.NativeStress.BookHT.TangentCoordinates.q12RootCoordinates_im_native
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.q12RootCoordinates_im_native


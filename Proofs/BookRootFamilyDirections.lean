module

public import BookRootGeneratorsNative
public import BookLiteralFamilyBindings

@[expose] public section

/-! Exact six-root parameter directions in the accepted SU3 family; every original label retained. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.BookHT.TangentCoordinates
open CKM.NativeFirstOrder CKM.NativeFourFamily NativePolynomial CompactAlbert
open QuadraticCertificate.ExactCKMConfiguration

def rootRealParam : Fin 6 → Fin 8 → ℝ :=
  ![Pi.single 1 (1/2), Pi.single 4 (1/2), Pi.single 1 (-1/2),
    Pi.single 6 (1/2), Pi.single 4 (-1/2), Pi.single 6 (-1/2)]

def rootImagParam : Fin 6 → Fin 8 → ℝ :=
  ![Pi.single 0 (-1/2), Pi.single 3 (-1/2), Pi.single 0 (-1/2),
    Pi.single 5 (-1/2), Pi.single 3 (-1/2), Pi.single 5 (-1/2)]

theorem suMat_rootRealParam (j : Fin 6) :
    suMat (rootRealParam j) = rootRealGenerator (rootPair j).1 (rootPair j).2 := by
  rw [su_suMat_eq]
  apply Matrix.ext
  intro a b
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [rootRealParam, rootRealGenerator, rootPair, Matrix.single, Pi.single_apply]

theorem suMat_rootImagParam (j : Fin 6) :
    suMat (rootImagParam j) = rootImagGenerator (rootPair j).1 (rootPair j).2 := by
  rw [su_suMat_eq]
  apply Matrix.ext
  intro a b
  fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [rootImagParam, rootImagGenerator, rootPair, Matrix.single, Pi.single_apply] <;> ring

theorem d6Column_re_preVar_point (b : Fin 24) (p : Fin 39) (k : Fin 27) :
    (d6Column b ⟨27*p.val+k.val, by omega⟩).re =
      preVar exactPhases exactPhases_unit (d6Sheet b)
        (rootRealParam ⟨b.val%6, by omega⟩, rootRealParam ⟨b.val%6, by omega⟩, 0) p k := by
  rw [← d6ColumnQ12_complex, d6_all_points, preVar_same_conjugation]
  simp only [q12SheetColumn, anchorRelabel_mask]
  split_ifs with hp
  · simp only [Pi.zero_apply, map_zero]
    change (0 : ℝ) = upperCoordinateEquiv 0 k
    rw [map_zero]
    rfl
  · rw [q12SheetTransport_re_native]
    have he : (fun j => (Q12.toComplex (q12RootCoordinates
        (rootPair ⟨b.val%6, by omega⟩).1 (rootPair ⟨b.val%6, by omega⟩).2
        (q12SheetInverse (d6Sheet b) (Option2.BookNativeBase.bookPointQ12 p)) j)).re) =
      upperCoordinates (nativeHiddenConjugation
        (rootRealGenerator (rootPair ⟨b.val%6, by omega⟩).1 (rootPair ⟨b.val%6, by omega⟩).2)
        (anchorΨ (d6Sheet b) (literalPoint exactPhases p))) := by
      funext j
      exact q12RootCoordinates_re_native _ _ _
        (anchorΨ (d6Sheet b) (literalPoint exactPhases p))
        (q12SheetInverse_complex_native (d6Sheet b) p) j
    rw [he, fromUpperCoordinates_upperCoordinates, suMat_rootRealParam]

theorem d6Column_im_preVar_point (b : Fin 24) (p : Fin 39) (k : Fin 27) :
    (d6Column b ⟨27*p.val+k.val, by omega⟩).im =
      preVar exactPhases exactPhases_unit (d6Sheet b)
        (rootImagParam ⟨b.val%6, by omega⟩, rootImagParam ⟨b.val%6, by omega⟩, 0) p k := by
  rw [← d6ColumnQ12_complex, d6_all_points, preVar_same_conjugation]
  simp only [q12SheetColumn, anchorRelabel_mask]
  split_ifs with hp
  · simp only [Pi.zero_apply, map_zero]
    change (0 : ℝ) = upperCoordinateEquiv 0 k
    rw [map_zero]
    rfl
  · rw [q12SheetTransport_im_native]
    have he : (fun j => (Q12.toComplex (q12RootCoordinates
        (rootPair ⟨b.val%6, by omega⟩).1 (rootPair ⟨b.val%6, by omega⟩).2
        (q12SheetInverse (d6Sheet b) (Option2.BookNativeBase.bookPointQ12 p)) j)).im) =
      upperCoordinates (nativeHiddenConjugation
        (rootImagGenerator (rootPair ⟨b.val%6, by omega⟩).1 (rootPair ⟨b.val%6, by omega⟩).2)
        (anchorΨ (d6Sheet b) (literalPoint exactPhases p))) := by
      funext j
      exact q12RootCoordinates_im_native _ _ _
        (anchorΨ (d6Sheet b) (literalPoint exactPhases p))
        (q12SheetInverse_complex_native (d6Sheet b) p) j
    rw [he, fromUpperCoordinates_upperCoordinates, suMat_rootImagParam]

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.d6Column_re_preVar_point
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.d6Column_re_preVar_point
#check Option2.NativeStress.BookHT.TangentCoordinates.d6Column_im_preVar_point
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.d6Column_im_preVar_point


module

public import NativeHEquilibriumCore

@[expose] public section

namespace Option2.NativeStress.NativeH.Equilibrium

open scoped BigOperators
open ConfigurationResidualIndices QuarticCertificate.RowBridge
open QuadraticCertificate.ExactCKMConfiguration
open PolynomialJets AnchorSupport

theorem shapeJacobianEntry_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (h : R) (s : RowShape) (P : Fin 1053 → R) (c : Fin 1053) :
    f (shapeJacobianEntry h s P c) =
      shapeJacobianEntry (f h) s (fun v => f (P v)) c := by
  simp only [shapeJacobianEntry, map_add, map_list_sum, List.map_map, Function.comp_def]
  congr 1
  · apply congrArg List.sum
    apply List.map_congr_left
    intro e _
    simp only [map_mul, map_add, map_intCast]
    simp [quadraticScale, apply_ite f]
  · apply congrArg List.sum
    apply List.map_congr_left
    intro e _
    simp [apply_ite f]

theorem jacobianEntry_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (h t : R) (P : Fin 1053 → R) (r : Fin 2184) (c : Fin 1053) :
    f (jacobianEntry h t r P c) =
      jacobianEntry (f h) (f t) r (fun v => f (P v)) c :=
  shapeJacobianEntry_map f h (rowShape r) P c

theorem baseQ12_complex :
    (fun v => Q12.toComplex (baseQ12 v)) =
      (fun v => ((pointCoordinates v : ℝ) : ℂ)) :=
  FourSheets.PointQ12.P_literal.symm

theorem halfQ12_complex : Q12.toComplex (Q12.lit 1 0 0 0 2) = (1 / 2 : ℂ) := by
  rw [Q12.toComplex_lit]
  norm_num

theorem thirdQ12_complex : Q12.toComplex (Q12.lit 1 0 0 0 3) = (1 / 3 : ℂ) := by
  rw [Q12.toComplex_lit]
  norm_num

/-- The unchanged original-row column contraction is the complex image of the
optimized exact sum. This theorem assumes no cancellation. -/
theorem fastContraction_to_original_column (i : Fin 4) (a : Fin 3) (c : Fin 1053) :
    Q12.toComplex (fastContraction (rawEntries i a) (hSpec i a)
      (Q12.lit 1 0 0 0 2) baseQ12 c) =
    ∑ r : Fin 2184, weightC i a r *
      equationLinearMatrix (translatedRow (fun v => ((pointCoordinates v : ℝ) : ℂ))) r c := by
  rw [actual_fastContraction_eq]
  rw [weightC_dense_sparse]
  have hmap := hEntriesQ12_toComplex i a
  rw [← hmap]
  simp only [map_list_sum, List.map_map, Function.comp_def, map_mul]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e _
  congr 1
  rw [jacobianEntry_map, halfQ12_complex, thirdQ12_complex, baseQ12_complex]
  exact (equationLinearMatrix_translate_fRow _ _ _ _ _).symm

end Option2.NativeStress.NativeH.Equilibrium

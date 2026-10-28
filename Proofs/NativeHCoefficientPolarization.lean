module

public import NativeHIntegerCoefficientBridge

@[expose] public section

namespace Option2.NativeStress.NativeH.Reproduction

open scoped BigOperators
open BookHT.TangentCoordinates QuarticCertificate.RowBridge ConfigurationResidualIndices

theorem list_sum_sub {α : Type*} (l : List α) (f g : α → ℂ) :
    (l.map (fun a => f a-g a)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.sum_cons,ih]; ring

theorem termCoefficient_complex (j k : Fin 24) (p q : Fin 1053) :
    Q12.toComplex (termCoefficient j k p q) =
      eigenColumn j p * eigenColumn k q +
        if j=k then 0 else eigenColumn k p * eigenColumn j q := by
  by_cases h : j=k <;>
    simp [termCoefficient,h,nonzeroProduct_eq,columnQ12_eq,d6ColumnQ12_complex,eigenColumn]

theorem homogeneousH_sparse (i : Fin 4) (a : Fin 3) (x : Fin 1053 → ℂ) :
    homogeneousH i a x =
      ((rawEntries i a).map fun e => orientedValue (hSpec i a) e.coefficient *
        quadraticValue (quadraticScale (1/2 : ℂ) (labelShape e.label))
          (labelShape e.label).quadratic x).sum := by
  rw [homogeneousH,weightC_dense_sparse]
  simp only [hEntries,List.map_map,Function.comp_def,quadraticPartValue,quadTable,
    rowShape,fNumber.symm_apply_apply]

theorem nativeCoefficient_plain (i : Fin 4) (a : Fin 3) (j k : Fin 24) :
    nativeCoefficient i a j k =
      ((rawEntries i a).map fun e => orientedQ12 (hSpec i a) e.coefficient *
        rationalShapeCoefficient (labelShape e.label) j k).sum := by
  unfold nativeCoefficient
  apply congrArg List.sum
  apply List.map_congr_left
  intro e _
  exact q12_skipRow _ _

/-- The off-diagonal coefficient is the exact mixed quadratic variation of the
original residual contracted with the unchanged native H covector. -/
theorem nativeCoefficient_polar (i : Fin 4) (a : Fin 3) (j k : Fin 24) (hjk : j≠k) :
    Q12.toComplex (nativeCoefficient i a j k) =
      homogeneousH i a (eigenColumn j+eigenColumn k) -
        homogeneousH i a (eigenColumn j) - homogeneousH i a (eigenColumn k) := by
  rw [nativeCoefficient_plain,map_list_sum]
  simp only [List.map_map,Function.comp_def,map_mul,orientedQ12_toComplex]
  simp only [homogeneousH_sparse]
  rw [← list_sum_sub,← list_sum_sub]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e _
  rw [rationalShapeCoefficient_image]
  unfold shapeUnscaled quadraticValue
  rw [← List.sum_map_mul_left]
  simp only [termCoefficient_complex,hjk,↓reduceIte]
  simp_rw [← List.sum_map_mul_left]
  rw [← list_sum_sub,← list_sum_sub]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  simp only [Pi.add_apply]
  ring

theorem integerNativeCoefficient_polar (i : Fin 4) (a : Fin 3)
    (j k : Fin 24) (hjk : j≠k) :
    integerImage (integerNativeCoefficient i a j k) = (integerFullScale i a : ℂ) *
      (homogeneousH i a (eigenColumn j+eigenColumn k) -
        homogeneousH i a (eigenColumn j) - homogeneousH i a (eigenColumn k)) := by
  rw [integerNativeCoefficient_image,nativeCoefficient_polar i a j k hjk]

end Option2.NativeStress.NativeH.Reproduction

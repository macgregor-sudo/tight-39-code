module

public import NativeHResidualQuadratic
public import NativeHBookQuadratic

@[expose] public section

/-! Closed native variation endpoint, with an explicit original-row homogeneous
interpretation. Equality to the Book H model remains an unproved finite
polynomial comparison; no assumption of that comparison enters these results. -/

namespace Option2.NativeStress.NativeH.Reproduction

open scoped BigOperators
open BookHT.TangentCoordinates BookHT.Dictionary
open QuarticCertificate.RowBridge PolynomialJets
open NativePolynomial.ConfigurationResiduals Option2.BookNativeBase

set_option maxRecDepth 8192

noncomputable def nativeHQuadraticAlongRealV (z : BookHT.Blocks) : BookHT.Blocks :=
  fun i => WithLp.toLp 2 (fun a => homogeneousH i a (V (realCoordinates z)))

/-- Actual residual variation at the source-bound Book point, for every Book
block and all twelve frozen H components. No tangent or reproduction premise. -/
theorem native_H_quadratic_variation (z : BookHT.Blocks) :
    residualContraction (Option2.NativeStress.originalF (bookBase+realV z)) =
      nativeHQuadraticAlongRealV z := by
  funext i
  ext a
  rw [residual_eq_homogeneous]
  have hv : (fun c => ((realV z c : ℝ) : ℂ)) = V (realCoordinates z) :=
    funext (realV_complex z)
  rw [hv]
  rfl

/-- The evaluator is the degree-two part of every original residual row after
translation by the actual literal Book point, with the exact native half/third. -/
theorem native_quadratic_original_rows (z : BookHT.Blocks) (i : Fin 4) (a : Fin 3) :
    nativeHQuadraticAlongRealV z i a =
      ∑ r : Fin 2184, weightC i a r * MvPolynomial.eval (V (realCoordinates z))
        (MvPolynomial.homogeneousComponent 2
          (translate (fun c => ((bookBase c : ℝ) : ℂ))
            (fRow (1/2 : ℂ) (1/3 : ℂ) r))) := by
  simp only [eval_homogeneousComponent_two_translate_fRow]
  rfl

/-- The complete native evaluator has the proved sparse computation semantics. -/
theorem native_quadratic_sparse_evaluator (z : BookHT.Blocks) (i : Fin 4) (a : Fin 3) :
    nativeHQuadraticAlongRealV z i a =
      CoeffTree.evaluate Q12.toComplex (restrictionTree i a)
        (pairWeight (by decide) (realCoordinates z)) :=
  (restrictionTree_evaluate i a (realCoordinates z)).symm

/-- Precisely the remaining native-to-Book obligation, with the full residual
and homogeneous forms proved equivalent rather than either one assumed. -/
theorem reproduction_iff_homogeneous (z : BookHT.Blocks) :
    residualContraction (Option2.NativeStress.originalF (bookBase+realV z)) = BookHT.H z ↔
      nativeHQuadraticAlongRealV z = BookHT.H z := by
  rw [native_H_quadratic_variation]

end Option2.NativeStress.NativeH.Reproduction

#print axioms Option2.NativeStress.NativeH.Reproduction.native_H_quadratic_variation
#print axioms Option2.NativeStress.NativeH.Reproduction.native_quadratic_original_rows
#print axioms Option2.NativeStress.NativeH.Reproduction.native_quadratic_sparse_evaluator
#print axioms Option2.NativeStress.NativeH.Reproduction.reproduction_iff_homogeneous

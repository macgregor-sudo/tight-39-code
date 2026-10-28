module

public import A3PolyCalc
public import NativeHEquilibriumTransport
public import NativeStressConsumer
public import OriginalFAnalyticDerivativeV2

@[expose] public section

/-! The generic column-to-derivative transfer at the actual packed original F.
It needs no H anchor support. The eventual T endpoint discharges its exact
column premise by literal characteristic-zero cancellation. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.NativeT
open scoped BigOperators
open MvPolynomial PolynomialJets AnchorSupport
open NativePolynomial.ConfigurationResiduals QuarticCertificate.RowBridge
open NativeH.Equilibrium CKM.NativeFirstOrder.PolyCalcReal

theorem originalF_hasFDerivAt (C : NativeAmbient) :
    HasFDerivAt Option2.NativeStress.originalF
      (ContinuousLinearMap.pi fun r : Fin 2184 =>
        ∑ c : Fin 1053, eval C (pderiv c (fRow (1/2 : ℝ) (1/3 : ℝ) r)) •
          (ContinuousLinearMap.proj c : NativeAmbient →L[ℝ] ℝ)) C :=
  hasFDerivAt_pi.2 fun r => hasFDerivAt_eval (fRow (1/2 : ℝ) (1/3 : ℝ) r) C

theorem original_column_cast (C : NativeAmbient) (r : Fin 2184) (c : Fin 1053) :
    (eval C (pderiv c (fRow (1/2 : ℝ) (1/3 : ℝ) r)) : ℂ) =
      equationLinearMatrix (translatedRow (fun v => (C v : ℂ))) r c := by
  calc
    (eval C (pderiv c (fRow (1/2 : ℝ) (1/3 : ℝ) r)) : ℂ) =
        ((equationLinearMatrix (fun r => translate C (fRow (1/2 : ℝ) (1/3 : ℝ) r)) r c : ℝ) : ℂ) :=
      congrArg (fun x : ℝ => (x : ℂ)) (translate_coeff_single _ C c).symm
    _ = ((jacobianEntry (1/2 : ℝ) (1/3 : ℝ) r C c : ℝ) : ℂ) :=
      congrArg (fun x : ℝ => (x : ℂ)) (equationLinearMatrix_translate_fRow C _ _ r c)
    _ = jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r (fun v => (C v : ℂ)) c := by
      simpa using jacobianEntry_map Complex.ofRealHom (1/2 : ℝ) (1/3 : ℝ) C r c
    _ = equationLinearMatrix (translatedRow (fun v => (C v : ℂ))) r c :=
      (equationLinearMatrix_translate_fRow _ _ _ r c).symm

/-- The real continuous covector annihilates the genuine original-F derivative
when every original ambient column cancels; no support or base-solution premise. -/
theorem stressCovector_originalF_derivative_zero_of_columns
    (C : NativeAmbient) (ell : Weights)
    (hL : ∀ c : Fin 1053, ∑ r : Fin 2184, ell r *
      equationLinearMatrix (translatedRow (fun v => (C v : ℂ))) r c = 0) :
    (AnalyticDerivative.stressCovector ell).comp
      (fderiv ℝ Option2.NativeStress.originalF C) = 0 := by
  ext W
  rw [(originalF_hasFDerivAt C).fderiv]
  simp only [ContinuousLinearMap.comp_apply, AnalyticDerivative.stressCovector_apply,
    ContinuousLinearMap.pi_apply, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul, original_column_cast,
    Finset.mul_sum, zero_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro c _
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [hL, zero_mul]

end Option2.NativeStress.NativeT
#check Option2.NativeStress.NativeT.stressCovector_originalF_derivative_zero_of_columns
#print axioms Option2.NativeStress.NativeT.stressCovector_originalF_derivative_zero_of_columns

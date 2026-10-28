module

public import BookTangentQ12
public import A5Analytic
public import A5AnchorF

@[expose] public section

/-! The accepted actual solution families differentiate to the original packed kernel.
This module supplies no D6-to-family equality; that literal binding is separate. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.BookHT.TangentCoordinates
open CKM.NativeFirstOrder CKM.NativeFourFamily NativePolynomial
open NativePolynomial.ConfigurationResiduals

theorem packed_originalF_hasFDerivAt (x : Fin 1053 → ℝ) :
    HasFDerivAt Option2.NativeStress.originalF
      (ContinuousLinearMap.pi fun r : Fin 2184 =>
        ∑ j : Fin 1053, MvPolynomial.eval x
          (MvPolynomial.pderiv j (fRow (1/2 : ℝ) (1/3 : ℝ) r)) •
          (ContinuousLinearMap.proj j : (Fin 1053 → ℝ) →L[ℝ] ℝ)) x :=
  hasFDerivAt_pi.2 fun r =>
    PolyCalcReal.hasFDerivAt_eval (fRow (1/2 : ℝ) (1/3 : ℝ) r) x

theorem packed_originalF_derivative (C W : PartialAction.Configuration ℝ) :
    fderiv ℝ Option2.NativeStress.originalF (PartialAction.pack C)
      (PartialAction.pack W) =
    fderiv ℝ AnalyticDerivative.originalF C W := by
  rw [(packed_originalF_hasFDerivAt _).fderiv, (hasFDerivAt_originalF C).fderiv]
  funext r
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply, packCLM_apply]

theorem preVar_mem_original_kernel {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ)
    (H : Fin 4) (p : PreParam) :
    fderiv ℝ Option2.NativeStress.originalF (PartialAction.pack (literalCfg ξ))
      (PartialAction.pack (preVar ξ hξ H p)) = 0 := by
  rw [packed_originalF_derivative, ← preDer_apply hξ H p]
  have hD := (hasFDerivAt_originalF (literalCfg ξ)).differentiableAt.hasFDerivAt
  have hP := (hasStrictFDerivAt_preMap hξ H).hasFDerivAt
  have hD' : HasFDerivAt AnalyticDerivative.originalF
      (fderiv ℝ AnalyticDerivative.originalF (literalCfg ξ))
      (preMap ξ hξ H 0) := by simpa only [preMap_zero hξ H] using hD
  have hchain := hD'.comp 0 hP
  have hzero : (AnalyticDerivative.originalF ∘ preMap ξ hξ H) =
      fun _ : PreParam => (0 : Fin 2184 → ℝ) := by
    funext q
    exact originalF_preCfg hξ H (suExp_mem_specialUnitaryGroup q.1)
      (suExp_mem_specialUnitaryGroup q.2.1) _
  rw [hzero] at hchain
  have h := hchain.unique (hasFDerivAt_const (0 : Fin 2184 → ℝ) (0 : PreParam))
  exact congrArg (fun L : PreParam →L[ℝ] (Fin 2184 → ℝ) => L p) h

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.packed_originalF_derivative
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.packed_originalF_derivative
#check Option2.NativeStress.BookHT.TangentCoordinates.preVar_mem_original_kernel
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.preVar_mem_original_kernel


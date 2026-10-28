module

public import NativePhaseQuadraticCoefficient
public import NativePhaseCommonTerms
public import NativePhaseBookComplexification
public import NativeRealPolynomialExt

@[expose] public section

noncomputable section
namespace Option2.NativeStress.PhaseComplexCommonDeletionA6
open MvPolynomial PolynomialJets
open PhaseBookComplexificationA6 PhaseRealPolynomialExtA6 PhaseRawBookA6
open PhaseCommonHessianA6 PhaseQuadraticCoefficientA6 PhaseHilbertA6
open AnalyticDerivative CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open BookHT HTPhaseComplete NativePolynomial Matrix
open scoped BigOperators

/-- Actual original-row contracted quadratic, pulled back along the actual
complexification of the raw Common56/BookReal24 native tangent matrix. -/
def pulledbackQuadric {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (w : Fin 2184 → ℂ) : A6Polynomial :=
  ChainMid.linSubst (nativeComplexMatrix hξ) (equationAnnihilatorQuadric (nativeRows ξ) w)

private theorem eval_linSubst {σ τ : Type*} [Fintype τ]
    (B : Matrix σ τ ℂ) (P : MvPolynomial σ ℂ) (x : τ → ℂ) :
    eval x (ChainMid.linSubst B P) = eval (B *ᵥ x) P := by
  unfold ChainMid.linSubst
  change eval x (eval₂ C (fun j => ∑ t, C (B j t)*X t) P) = _
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun v : σ → ℂ => eval v P)
  funext j
  simp [Function.comp_apply,Matrix.mulVec,dotProduct]

private theorem value_at_equiv {A B Z : Type*} (e : A ≃ B) (f : A → Z) (g : B → Z)
    (h : ∀ b, f (e.symm b) = g b) (a : A) : f a = g (e a) :=
  (congrArg f (e.symm_apply_apply a)).symm.trans (h (e a))

set_option maxRecDepth 2000 in
private theorem nativeMatrix_real_model {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (x : CoordinateIndex → ℝ) :
    nativeComplexMatrix hξ *ᵥ (fun k => (x k : ℂ)) =
      complexPack (rawBookEquiv hξ (realModelCoordinates hξ x)).val := by
  rw [← nativeBookComplexEquiv_matrix,nativeBookComplexEquiv,LinearEquiv.trans_apply,
    nativeKernelCast_val,complexKernelEquiv_ofReal]
  have hn := value_at_equiv (realModelCoordinates hξ).toEquiv
    (fun t : CoordinateIndex → ℝ => (nativeRealCoordinates hξ t).val)
    (fun v : Model ξ => PartialAction.pack (rawBookEquiv hξ v).val)
    (nativeRealCoordinates_model hξ) x
  exact congrArg (fun f : Fin 1053 → ℝ => fun j => (f j : ℂ)) hn

private theorem stressHessian_apply (ξ : Fin 4 → ℂ)
    (ell : (Fin 2184 → ℝ) →L[ℝ] ℂ) (u v : Cfg) :
    stressHessian ξ ell u v = ell (fderiv ℝ (fderiv ℝ AnalyticDerivative.originalF) (literalCfg ξ) u v) := rfl

/-- Exact coefficient=half-Hessian, after the ACTUAL raw complex matrix pullback. -/
theorem realEval_pulledback {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (w : Fin 2184 → ℂ)
    (x : CoordinateIndex → ℝ) :
    realEval x (pulledbackQuadric hξ w) =
      (1/2 : ℝ) • stressHessian ξ (stressCovector w)
        (rawBookEquiv hξ (realModelCoordinates hξ x) : Cfg)
        (rawBookEquiv hξ (realModelCoordinates hξ x) : Cfg) := by
  rw [realEval,pulledbackQuadric,eval_linSubst,nativeMatrix_real_model,native_quadratic_coefficient,
    stressHessian_apply]

private theorem realModel_sum {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (c : Fin 56 → ℝ) (z : BookRealIndex → ℝ) :
    realModelCoordinates hξ (Sum.elim c z) =
      ((commonRealEquiv hξ).symm c,bookRealEquiv.symm z) := rfl

set_option maxRecDepth 2000 in
/-- The full natural stress hypothesis removes actual common directions.
No desired polynomial/coefficient identity or H/T value is assumed. -/
theorem realEval_pulledback_book_only {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (w : Fin 2184 → ℂ)
    (hann : (stressCovector w).comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg ξ)) = 0)
    (c : Fin 56 → ℝ) (z : BookRealIndex → ℝ) :
    realEval (Sum.elim c z) (pulledbackQuadric hξ w) =
      realEval (Sum.elim (fun _ => 0) z) (pulledbackQuadric hξ w) := by
  rw [realEval_pulledback,realEval_pulledback,realModel_sum,realModel_sum]
  have hz : (commonRealEquiv hξ).symm (fun _ : Fin 56 => (0 : ℝ)) = 0 :=
    (commonRealEquiv hξ).symm.map_zero
  rw [hz]
  rw [show (0 : Common ξ) = ((0 : orbitC ξ),(0 : fixQK ξ)) from rfl,rawBookEquiv_book]
  exact congrArg (fun q : ℂ => (1/2 : ℝ) • q)
    (stressHessian_book_only hξ (stressCovector w) hann
      ((commonRealEquiv hξ).symm c).1 ((commonRealEquiv hξ).symm c).2 (bookRealEquiv.symm z))

/-- Actual COMPLEX polynomial common56 deletion, from the unchanged original
rows and actual raw matrix; the only stress premise is full derivative annihilation. -/
theorem pulledbackQuadric_deleteCommon {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (w : Fin 2184 → ℂ)
    (hann : (stressCovector w).comp (fderiv ℝ AnalyticDerivative.originalF (literalCfg ξ)) = 0) :
    pulledbackQuadric hξ w = deleteCommon (pulledbackQuadric hξ w) :=
  eq_deleteCommon_of_real_evaluations _ (realEval_pulledback_book_only hξ w hann)

#print axioms Option2.NativeStress.PhaseComplexCommonDeletionA6.realEval_pulledback
#print axioms Option2.NativeStress.PhaseComplexCommonDeletionA6.pulledbackQuadric_deleteCommon
end Option2.NativeStress.PhaseComplexCommonDeletionA6

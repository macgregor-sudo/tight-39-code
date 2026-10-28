module

public import OriginalFAnchorAnnihilationV3
public import NativePartialAction
public import PointBridge
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
First-party algebraic-to-analytic join for the literal original real F map.
Polynomial evaluation proves differentiability. The frozen unrestricted line
identity then forces the actual Fréchet derivative's contraction to vanish.
No derivative formula, unrelated linear operator or native covector certificate
is assumed. The support and annihilation identities are imported.
-/

noncomputable section

namespace Option2.NativeStress.AnalyticDerivative

open scoped BigOperators
open MvPolynomial PolynomialJets
open NativePolynomial.PartialAction
open Option2.NativeStress.AnchorSupport

abbrev RealConfiguration := Configuration ℝ
abbrev RealResiduals := Fin 2184 → ℝ

/-- The actual real residual map, retaining every original row and its
literal half/third normalization on the native 39 by 27 configuration. -/
def originalF (C : RealConfiguration) : RealResiduals := fun r =>
  eval (pack C)
    (NativePolynomial.ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r)

def complexPack (C : RealConfiguration) : Ambient := fun v => ((pack C v : ℝ) : ℂ)

/- Construct the finite sum symbolically before specializing the index type.
This avoids reducing the 2184-element enumeration in a coercion proof. -/
private def finiteStressCovector {ι : Type*} [Fintype ι] (ell : ι → ℂ) :
    (ι → ℝ) →L[ℝ] ℂ where
  toFun y := ∑ r : ι, ell r * (y r : ℂ)
  map_add' x y := by
    simp only [Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]
  map_smul' a y := by
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
      Complex.real_smul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  cont := continuous_finsetSum _ (fun r _ =>
    continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply r)))

private theorem finiteStressCovector_apply {ι : Type*} [Fintype ι]
    (ell : ι → ℂ) (y : ι → ℝ) :
    finiteStressCovector ell y = ∑ r : ι, ell r * (y r : ℂ) := rfl

/-- Complex stress coefficients define a continuous REAL-linear covector on
the actual real residual space. Real and imaginary parts are both retained. -/
@[no_expose] def stressCovector (ell : Weights) : RealResiduals →L[ℝ] ℂ := finiteStressCovector ell

theorem stressCovector_apply (ell : Weights) (y : RealResiduals) :
    stressCovector ell y = ∑ r : Fin 2184, ell r * (y r : ℂ) := by
  unfold stressCovector
  exact finiteStressCovector_apply ell y

private theorem differentiable_eval (p : MvPolynomial (Fin 1053) ℝ) :
    Differentiable ℝ (fun x : Fin 1053 → ℝ => eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa only [eval_C] using
      (differentiable_const a : Differentiable ℝ (fun _ : Fin 1053 → ℝ => a))
  | add p q hp hq => simpa only [map_add] using hp.fun_add hq
  | mul_X p v hp => simpa only [map_mul, eval_X] using hp.fun_mul (differentiable_apply v)

private theorem differentiable_pack :
    Differentiable ℝ (fun C : RealConfiguration => pack C) := by
  apply differentiable_pi.mpr
  intro v
  have hp : Differentiable ℝ (fun C : RealConfiguration =>
      C (⟨v.val / 27, by omega⟩ : Fin 39)) := differentiable_apply _
  have hc : Differentiable ℝ (fun x : NativeVector ℝ =>
      x (⟨v.val % 27, by omega⟩ : Fin 27)) := differentiable_apply _
  exact hc.comp hp

/-- Differentiability is established for every real configuration, not supplied
as an extra hypothesis and not restricted to the solution set. -/
theorem originalF_differentiable : Differentiable ℝ originalF := by
  apply differentiable_pi.mpr
  intro r
  exact (differentiable_eval
    (NativePolynomial.ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r)).comp
      differentiable_pack

private theorem eval_complexPack_row (C : RealConfiguration) (r : Fin 2184) :
    eval (complexPack C) (row r) = (originalF C r : ℂ) := by
  have hrow : map Complex.ofRealHom
      (NativePolynomial.ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r) =
      row r := by
    simpa [row] using FourSheets.PointBridge.Rows.map_fRow
      Complex.ofRealHom (1 / 2 : ℝ) (1 / 3 : ℝ) r
  rw [← hrow, eval_map]
  exact (eval₂_comp Complex.ofRealHom (pack C)
    (NativePolynomial.ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r)).symm

private theorem stress_originalF_eq_contractedF (ell : Weights) (C : RealConfiguration) :
    stressCovector ell (originalF C) = contractedF ell (complexPack C) := by
  simp only [stressCovector_apply, contractedF, eval_complexPack_row]

private theorem complexPack_add_smul (C W : RealConfiguration) (t : ℝ) :
    complexPack (C + t • W) = complexPack C + (t : ℂ) • complexPack W := by
  funext v
  simp only [complexPack, pack, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_add, Complex.ofReal_mul]

/-- The frozen original-F identity, now on genuine real native configuration
lines and with the continuous real-linear stress covector. W is unrestricted. -/
theorem real_originalF_line_contraction
    (P C W : RealConfiguration) (ell : Weights) (i : Fin 4)
    (hP : ∀ r : Fin 2184, originalF P r = 0)
    (hL : ∀ c : Fin 1053,
      ∑ r : Fin 2184, ell r * equationLinearMatrix (translatedRow (complexPack P)) r c = 0)
    (hsupport : HasAnchorSupport (complexPack P) ell i)
    (hanchor : ∀ v, AnchorCoordinate i v → pack C v = pack P v)
    (t : ℝ) :
    stressCovector ell (originalF (C + t • W)) =
      (t : ℂ) ^ 2 * eval (complexPack W) (contractedQuadratic (complexPack P) ell) := by
  have hPc : ∀ r : Fin 2184, eval (complexPack P) (row r) = 0 := by
    intro r
    rw [eval_complexPack_row, hP r, Complex.ofReal_zero]
  have ha : ∀ v, AnchorCoordinate i v → complexPack C v = complexPack P v := by
    intro v hv
    exact congrArg (fun x : ℝ => (x : ℂ)) (hanchor v hv)
  rw [stress_originalF_eq_contractedF, complexPack_add_smul]
  exact contractedF_line_eq_quadratic_at_anchor
    (complexPack P) ell i hPc hL hsupport (complexPack C) ha (complexPack W) (t : ℂ)

/- This private calculus step keeps the continuous map opaque while taking its
derivative. The public native endpoint below derives, rather than assumes, the
required line identity from the original-F polynomial theorem. -/
private theorem covector_comp_fderiv_zero_of_quadratic_lines
    (F : RealConfiguration → RealResiduals) (hF : Differentiable ℝ F)
    (ellL : RealResiduals →L[ℝ] ℂ) (C : RealConfiguration)
    (q : RealConfiguration → ℂ)
    (hlineValue : ∀ W (t : ℝ), ellL (F (C + t • W)) = (t : ℂ) ^ 2 * q W) :
    ellL.comp (fderiv ℝ F C) = 0 := by
  apply ContinuousLinearMap.ext
  intro W
  change (ellL.comp (fderiv ℝ F C)) W = 0
  have hcov : HasFDerivAt ellL ellL (F C) := ellL.hasFDerivAt
  have hchain : HasFDerivAt (fun X : RealConfiguration => ellL (F X))
      (ellL.comp (fderiv ℝ F C)) C :=
    hcov.comp C (hF C).hasFDerivAt
  have hline := hchain.hasLineDerivAt W
  change HasDerivAt (fun t : ℝ => ellL (F (C + t • W)))
    ((ellL.comp (fderiv ℝ F C)) W) 0 at hline
  have hfunction : (fun t : ℝ => ellL (F (C + t • W))) =
      (fun t : ℝ => (t : ℂ) ^ 2 * q W) := by
    funext t
    exact hlineValue W t
  rw [hfunction] at hline
  have hcast : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) (0 : ℝ) := by
    have hf : (fun t : ℝ => (t : ℂ)) = (Complex.ofRealCLM : ℝ → ℂ) := by
      funext t
      exact (Complex.ofRealCLM_apply t).symm
    rw [hf]
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using
      (Complex.ofRealCLM.hasFDerivAt (x := (0 : ℝ))).hasDerivAt
  have hzero : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2 * q W) 0 (0 : ℝ) := by
    simpa using (hcast.pow 2).mul_const (q W)
  exact hline.unique hzero

/-- The named actual real Fréchet derivative of the full original F is
annihilated by the stress covector on the anchor-fixed affine slice.
Neither F(C)=0 nor a restriction on tested ambient directions is assumed. -/
theorem stress_comp_fderiv_originalF_eq_zero
    (P C : RealConfiguration) (ell : Weights) (i : Fin 4)
    (hP : ∀ r : Fin 2184, originalF P r = 0)
    (hL : ∀ c : Fin 1053,
      ∑ r : Fin 2184, ell r * equationLinearMatrix (translatedRow (complexPack P)) r c = 0)
    (hsupport : HasAnchorSupport (complexPack P) ell i)
    (hanchor : ∀ v, AnchorCoordinate i v → pack C v = pack P v) :
    (stressCovector ell).comp (fderiv ℝ originalF C) = 0 := by
  apply covector_comp_fderiv_zero_of_quadratic_lines originalF originalF_differentiable
    (stressCovector ell) C (fun W =>
      eval (complexPack W) (contractedQuadratic (complexPack P) ell))
  intro W t
  exact real_originalF_line_contraction P C W ell i hP hL hsupport hanchor t

/-- Coordinate spelling of the same actual derivative annihilation. -/
theorem all_real_directions_annihilated
    (P C W : RealConfiguration) (ell : Weights) (i : Fin 4)
    (hP : ∀ r : Fin 2184, originalF P r = 0)
    (hL : ∀ c : Fin 1053,
      ∑ r : Fin 2184, ell r * equationLinearMatrix (translatedRow (complexPack P)) r c = 0)
    (hsupport : HasAnchorSupport (complexPack P) ell i)
    (hanchor : ∀ v, AnchorCoordinate i v → pack C v = pack P v) :
    (∑ r : Fin 2184, ell r * ((fderiv ℝ originalF C W r : ℝ) : ℂ)) = 0 := by
  have h := congrArg (fun A : RealConfiguration →L[ℝ] ℂ => A W)
    (stress_comp_fderiv_originalF_eq_zero P C ell i hP hL hsupport hanchor)
  simpa [stressCovector_apply] using h

end Option2.NativeStress.AnalyticDerivative

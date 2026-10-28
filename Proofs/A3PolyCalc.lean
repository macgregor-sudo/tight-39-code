module

public import PolynomialJetPrerequisitesModule
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Add

@[expose] public section

/-!
# Real polynomial calculus (A3 tangent helper)

* `hasFDerivAt_eval`: the Fréchet derivative of `x ↦ eval x f` on `σ → ℝ` (finite `σ`) at `p` is
  `u ↦ ∑ j, eval p (pderiv j f) * u j`.
* `translate_coeff_single`: the degree-one coefficients of the translated polynomial
  `PolynomialJets.translate p f` are the partial derivatives at `p`.

The induction for `hasFDerivAt_eval` follows the structure of the complex lemma
`PolyCalc.hasFDerivAt_aeval` (four-sheets-selected-20261024/src/PolyCalcSheet.lean:28),
specialised here to real coordinates `c j x = x j`.
-/

noncomputable section

namespace CKM.NativeFirstOrder.PolyCalcReal

open MvPolynomial

variable {σ : Type*}

/-- The derivative of real polynomial evaluation. -/
theorem hasFDerivAt_eval [DecidableEq σ] [Fintype σ] (f : MvPolynomial σ ℝ) (p : σ → ℝ) :
    HasFDerivAt (fun x : σ → ℝ => eval x f)
      (∑ j, eval p (pderiv j f) • (ContinuousLinearMap.proj j : (σ → ℝ) →L[ℝ] ℝ)) p := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero, zero_smul, Finset.sum_const_zero]
    exact hasFDerivAt_const a p
  | add f g hf hg =>
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    exact hf.fun_add hg
  | mul_X f i hf =>
    simp only [map_mul, eval_X]
    refine (hf.fun_mul (hasFDerivAt_apply i p)).congr_fderiv ?_
    ext v
    simp only [add_apply, smul_apply, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      pderiv_mul, pderiv_X, map_add, map_mul, eval_X, Pi.single_apply]
    simp only [apply_ite (eval p), map_one, map_zero, mul_ite, mul_one, mul_zero, add_mul,
      Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring

/-- The constant coefficient of the translate is the value at the base point. -/
theorem constantCoeff_translate (f : MvPolynomial σ ℝ) (p : σ → ℝ) :
    constantCoeff (PolynomialJets.translate p f) = eval p f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [PolynomialJets.translate]
  | add f g hf hg =>
    rw [PolynomialJets.translate, eval₂_add, map_add, ← PolynomialJets.translate,
      ← PolynomialJets.translate, hf, hg, map_add]
  | mul_X f i hf =>
    rw [PolynomialJets.translate, eval₂_mul, map_mul, ← PolynomialJets.translate, hf, eval₂_X,
      map_add, constantCoeff_X, constantCoeff_C, zero_add, map_mul, eval_X]

/-- The degree-one coefficients of the translate are the partial derivatives at the base point. -/
theorem translate_coeff_single [DecidableEq σ] (f : MvPolynomial σ ℝ) (p : σ → ℝ) (n : σ) :
    (PolynomialJets.translate p f).coeff (Finsupp.single n 1) = eval p (pderiv n f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have hne : (Finsupp.single n 1 : σ →₀ ℕ) ≠ 0 := Finsupp.single_ne_zero.mpr one_ne_zero
    simp [PolynomialJets.translate, coeff_C, hne.symm]
  | add f g hf hg =>
    simp only [PolynomialJets.translate] at hf hg ⊢
    simp [eval₂_add, hf, hg]
  | mul_X f i hf =>
    have ht : PolynomialJets.translate p (f * X i) =
        PolynomialJets.translate p f * X i + C (p i) * PolynomialJets.translate p f := by
      simp only [PolynomialJets.translate, eval₂_mul, eval₂_X]
      ring
    rw [ht, show ∀ a b : MvPolynomial σ ℝ, (a + b).coeff (Finsupp.single n 1) =
        a.coeff (Finsupp.single n 1) + b.coeff (Finsupp.single n 1) from fun a b => by simp,
      coeff_C_mul, hf, coeff_mul_X', pderiv_mul, pderiv_X, map_add, map_mul,
      map_mul, eval_X]
    by_cases h : i = n
    · subst h
      simp [constantCoeff_translate, ← constantCoeff_eq, mul_comm, add_comm]
    · simp [h, mul_comm]

end CKM.NativeFirstOrder.PolyCalcReal

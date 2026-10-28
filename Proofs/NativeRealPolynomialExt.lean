module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Analysis.Complex.Basic
public import BookRealCoordinates

@[expose] public section

noncomputable section
namespace Option2.NativeStress.PhaseRealPolynomialExtA6
open MvPolynomial PhaseBookComplexificationA6

/-- Evaluation on an actual real coordinate vector, included entrywise into ℂ. -/
def realEval {σ : Type*} (x : σ → ℝ) : MvPolynomial σ ℂ →+* ℂ :=
  MvPolynomial.eval (fun i => (x i : ℂ))

/-- Direct application of mathlib's polynomial uniqueness on a box with infinite
sides, using the infinite real subset of ℂ in every variable. No finiteness or
homogeneity assumption on the variable type/polynomials is needed. -/
theorem polynomial_ext_real {σ : Type*} {P Q : MvPolynomial σ ℂ}
    (h : ∀ x : σ → ℝ, realEval x P = realEval x Q) : P = Q := by
  apply MvPolynomial.funext_set (fun _ : σ => Set.range Complex.ofReal)
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro y hy
  have hr : (fun i => ((y i).re : ℂ)) = y := by
    funext i
    obtain ⟨t,ht⟩ := hy i (Set.mem_univ i)
    rw [← ht]
    rfl
  have hx := h (fun i => (y i).re)
  simpa only [realEval,hr] using hx

abbrev A6Polynomial := MvPolynomial CoordinateIndex ℂ

def zeroCommonVariables : CoordinateIndex → A6Polynomial :=
  Sum.elim (fun _ => 0) (fun b => MvPolynomial.X (Sum.inr b))

/-- Literal coefficient-preserving substitution: common56 variables go to0;
every BookRealIndex variable keeps exactly its Sum.inr label. -/
def deleteCommon : A6Polynomial →+* A6Polynomial :=
  MvPolynomial.eval₂Hom MvPolynomial.C zeroCommonVariables

theorem eval_deleteCommon (P : A6Polynomial) (x : CoordinateIndex → ℂ) :
    MvPolynomial.eval x (deleteCommon P) =
      MvPolynomial.eval (Sum.elim (fun _ : Fin 56 => 0) (fun b => x (Sum.inr b))) P := by
  change MvPolynomial.eval x (MvPolynomial.eval₂ MvPolynomial.C zeroCommonVariables P) = _
  rw [MvPolynomial.eval_eval₂]
  have hC : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℂ := by
    ext c
    simp
  rw [hC]
  congr 1
  funext i
  cases i <;> simp [zeroCommonVariables]

theorem realEval_deleteCommon (P : A6Polynomial) (x : CoordinateIndex → ℝ) :
    realEval x (deleteCommon P) =
      realEval (Sum.elim (fun _ : Fin 56 => 0) (fun b => x (Sum.inr b))) P := by
  change MvPolynomial.eval (fun i => (x i : ℂ)) (deleteCommon P) =
    MvPolynomial.eval (fun i => ((Sum.elim (fun _ : Fin 56 => (0 : ℝ))
      (fun b => x (Sum.inr b)) i : ℝ) : ℂ)) P
  rw [eval_deleteCommon]
  apply congrArg (fun f : CoordinateIndex → ℂ => MvPolynomial.eval f P)
  funext i
  cases i <;> rfl

/-- The immediate actual-label deletion consequence. Its evaluation hypothesis
is explicit; this theorem supplies no native half-Hessian/coefficient identity. -/
theorem eq_deleteCommon_of_real_evaluations (P : A6Polynomial)
    (h : ∀ (c : Fin 56 → ℝ) (z : BookRealIndex → ℝ),
      realEval (Sum.elim c z) P = realEval (Sum.elim (fun _ => 0) z) P) :
    P = deleteCommon P := by
  apply polynomial_ext_real
  intro x
  rw [realEval_deleteCommon]
  let c : Fin 56 → ℝ := fun i => x (Sum.inl i)
  let z : BookRealIndex → ℝ := fun b => x (Sum.inr b)
  have hx : Sum.elim c z = x := by
    funext i
    cases i <;> rfl
  simpa only [hx] using h c z

#print axioms Option2.NativeStress.PhaseRealPolynomialExtA6.polynomial_ext_real
#print axioms Option2.NativeStress.PhaseRealPolynomialExtA6.eq_deleteCommon_of_real_evaluations
end Option2.NativeStress.PhaseRealPolynomialExtA6

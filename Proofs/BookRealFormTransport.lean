module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

/-!
Finite negative-conjugate column transport, with explicit ordinary hypotheses.
This module imports no project data. Its real restriction is a real linear map;
no native tangent, coordinate dictionary or coefficient pairing is assumed discharged.
-/

noncomputable section

namespace BookRealFormTransport

open scoped BigOperators ComplexConjugate

variable {J R E : Type*}

/-- The real subspace specified by the negative-conjugate coordinate relation. -/
def realForm (σ : J → J) : Submodule ℝ (J → ℂ) where
  carrier := {y | ∀ j, y (σ j) = -conj (y j)}
  zero_mem' := by simp
  add_mem' := by
    intro y z hy hz j
    simp only [Pi.add_apply, map_add, hy j, hz j, neg_add]
  smul_mem' := by
    intro a y hy j
    simp [Pi.smul_apply, hy j, Complex.real_smul]

@[simp] theorem mem_realForm (σ : J → J) (y : J → ℂ) :
    y ∈ realForm σ ↔ ∀ j, y (σ j) = -conj (y j) := Iff.rfl

variable [Fintype J]

/-- Finite complex linear combination of the displayed columns. -/
def linearCombination (C : J → R → ℂ) : (J → ℂ) →ₗ[ℂ] (R → ℂ) where
  toFun y r := ∑ j, y j * C j r
  map_add' y z := by
    ext r
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' a y := by
    ext r
    simp [Finset.mul_sum, mul_assoc]

@[simp] theorem linearCombination_apply (C : J → R → ℂ)
    (y : J → ℂ) (r : R) :
    linearCombination C y r = ∑ j, y j * C j r := rfl

theorem linearCombination_conj (σ : J → J) (hσ : Function.Involutive σ)
    (C : J → R → ℂ) (hC : ∀ j r, C (σ j) r = -conj (C j r))
    (y : J → ℂ) (hy : ∀ j, y (σ j) = -conj (y j)) (r : R) :
    conj (linearCombination C y r) = linearCombination C y r := by
  simp only [linearCombination_apply, map_sum, map_mul]
  calc
    (∑ j, conj (y j) * conj (C j r)) = ∑ j, y (σ j) * C (σ j) r := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hy j, hC j r, neg_mul_neg]
    _ = ∑ j, y j * C j r :=
      Equiv.sum_comp (Function.Involutive.toPerm σ hσ) (fun j => y j * C j r)

theorem linearCombination_im (σ : J → J) (hσ : Function.Involutive σ)
    (C : J → R → ℂ) (hC : ∀ j r, C (σ j) r = -conj (C j r))
    (y : J → ℂ) (hy : ∀ j, y (σ j) = -conj (y j)) (r : R) :
    (linearCombination C y r).im = 0 :=
  Complex.conj_eq_iff_im.mp (linearCombination_conj σ hσ C hC y hy r)

/-- Always a real-part projection; the following theorem gives exact recovery
when the stated column and involution hypotheses hold. -/
def realPartRestriction (σ : J → J) (C : J → R → ℂ) :
    realForm σ →ₗ[ℝ] (R → ℝ) :=
  (LinearMap.pi fun r => Complex.reLm.comp (LinearMap.proj r)).comp
    (((linearCombination C).restrictScalars ℝ).comp (realForm σ).subtype)

@[simp] theorem realPartRestriction_apply (σ : J → J) (C : J → R → ℂ)
    (y : realForm σ) (r : R) :
    realPartRestriction σ C y r = (linearCombination C y.val r).re := rfl

/-- The named real linear map is a genuine restriction, not only a projection. -/
theorem realPartRestriction_complex (σ : J → J) (hσ : Function.Involutive σ)
    (C : J → R → ℂ) (hC : ∀ j r, C (σ j) r = -conj (C j r))
    (y : realForm σ) (r : R) :
    (realPartRestriction σ C y r : ℂ) = linearCombination C y.val r :=
  Complex.conj_eq_iff_re.mp (linearCombination_conj σ hσ C hC y.val y.property r)

/-- Generic ordered list evaluator; no literal coefficient family is imported. -/
def listEvaluate (value : E → R → ℂ) (es : List E) (r : R) : ℂ :=
  (es.map (fun e => value e r)).sum

theorem listEvaluate_map (value : E → R → ℂ) (τ : E → E)
    (hτ : ∀ e r, value (τ e) r = -conj (value e r)) (es : List E) (r : R) :
    listEvaluate value (es.map τ) r = -conj (listEvaluate value es r) := by
  induction es with
  | nil => simp [listEvaluate]
  | cons e es ih =>
      simp only [listEvaluate, List.map_cons, List.sum_cons] at ih ⊢
      rw [hτ e r, ih]
      simp [map_add, add_comm]

omit [Fintype J] in
/-- A list-family pairing derives the column hypothesis used above. -/
theorem columns_of_listPairing (σ : J → J) (columns : J → List E)
    (value : E → R → ℂ) (τ : E → E)
    (hτ : ∀ e r, value (τ e) r = -conj (value e r))
    (hcolumns : ∀ j, columns (σ j) = (columns j).map τ) (j : J) (r : R) :
    listEvaluate value (columns (σ j)) r =
      -conj (listEvaluate value (columns j) r) := by
  rw [hcolumns j]
  exact listEvaluate_map value τ hτ (columns j) r

end BookRealFormTransport


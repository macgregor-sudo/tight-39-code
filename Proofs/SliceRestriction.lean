module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Restriction of polynomials to a linear slice

Let `K` be a field and `B : Matrix (Fin n) (Fin m) K`. The columns of `B` span a linear
subspace `U ⊆ K^n` of dimension at most `m`; the rows of `B` give a parametrisation
`K^m → U`, `y ↦ B y`. Pulling back polynomial functions along this parametrisation is the
`K`-algebra homomorphism

  `restrict B : K[X_0, …, X_{n-1}] → K[Y_0, …, Y_{m-1}]`, `X_j ↦ ∑_t B j t • Y_t`.

This file sets up the linear forms (homogeneous polynomials of degree one), identifies each
linear form with its coefficient vector, and proves that a linear form is killed by
`restrict B` exactly when its coefficient vector annihilates the column space of `B`,
i.e. `c ᵥ* B = 0`.
-/

open MvPolynomial
open scoped Matrix

namespace SliceLemmas

variable {K : Type*} [Field K] {n m : ℕ}

/-- Restriction of polynomials in `n` variables to the slice parametrised by the matrix `B`:
the substitution `X_j ↦ ∑_t B j t • X_t` into polynomials in `m` variables. -/
noncomputable def restrict (B : Matrix (Fin n) (Fin m) K) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin m) K :=
  aeval fun j => ∑ t, C (B j t) * X t

theorem restrict_X (B : Matrix (Fin n) (Fin m) K) (j : Fin n) :
    restrict B (X j) = ∑ t, C (B j t) * X t :=
  aeval_X _ _

/-- Restriction preserves homogeneity and degree, because each variable is sent to a
linear form. -/
theorem restrict_isHomogeneous (B : Matrix (Fin n) (Fin m) K) {f : MvPolynomial (Fin n) K}
    {d : ℕ} (hf : f.IsHomogeneous d) : (restrict B f).IsHomogeneous d := by
  have h := hf.aeval (fun j => ∑ t, C (B j t) * X t) (n := 1) fun j =>
    IsHomogeneous.sum _ _ _ fun t _ => isHomogeneous_C_mul_X _ _
  simpa [restrict] using h

/-- The linear form `∑_j c_j X_j` with coefficient vector `c`. -/
noncomputable def linearForm (c : Fin n → K) : MvPolynomial (Fin n) K :=
  ∑ j, C (c j) * X j

/-- The coefficient vector of a polynomial: the coefficients of the monomials `X_j`. -/
noncomputable def coeffVector (ℓ : MvPolynomial (Fin n) K) : Fin n → K :=
  fun j => ℓ.coeff (Finsupp.single j 1)

theorem linearForm_mem_homogeneousSubmodule (c : Fin n → K) :
    linearForm c ∈ homogeneousSubmodule (Fin n) K 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _

theorem coeffVector_linearForm (c : Fin n → K) : coeffVector (linearForm c) = c := by
  funext j
  classical
  simp [coeffVector, linearForm, coeff_X, Finsupp.single_left_inj]

theorem linearForm_zero : linearForm (0 : Fin n → K) = 0 := by
  simp [linearForm]

theorem linearForm_injective : Function.Injective (linearForm (K := K) (n := n)) := by
  intro c c' h
  rw [← coeffVector_linearForm c, h, coeffVector_linearForm]

theorem linearForm_eq_zero_iff (c : Fin n → K) : linearForm c = 0 ↔ c = 0 := by
  rw [← linearForm_zero]
  exact linearForm_injective.eq_iff

/-- Every homogeneous polynomial of degree one is the linear form of its coefficient vector. -/
theorem linearForm_coeffVector {ℓ : MvPolynomial (Fin n) K}
    (hℓ : ℓ ∈ homogeneousSubmodule (Fin n) K 1) : linearForm (coeffVector ℓ) = ℓ := by
  rw [homogeneousSubmodule_one_eq_span_X] at hℓ
  induction hℓ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    classical
    simp [linearForm, coeffVector, coeff_X, Finsupp.single_left_inj]
  | zero => simp [linearForm, coeffVector]
  | add x y _ _ hx hy =>
    simp only [linearForm, coeffVector] at *
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add, add_mul,
      Finset.sum_add_distrib]
    rw [hx, hy]
  | smul a x _ hx =>
    simp only [linearForm, coeffVector] at *
    simp only [coeff_smul, smul_eq_mul, map_mul]
    conv_rhs => rw [← hx]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_C_mul, mul_assoc]

/-- Restriction of a linear form: its coefficient vector is multiplied by `B` on the right. -/
theorem restrict_linearForm (B : Matrix (Fin n) (Fin m) K) (c : Fin n → K) :
    restrict B (linearForm c) = linearForm (c ᵥ* B) := by
  simp only [linearForm, map_sum, map_mul, restrict, aeval_C, aeval_X, algebraMap_eq,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Matrix.vecMul, dotProduct, map_sum, map_mul, Finset.sum_mul, mul_assoc]

/-- A linear form vanishes on the slice exactly when its coefficient vector annihilates the
column space of `B`. -/
theorem restrict_eq_zero_iff_vecMul_eq_zero (B : Matrix (Fin n) (Fin m) K)
    {ℓ : MvPolynomial (Fin n) K} (hℓ : ℓ ∈ homogeneousSubmodule (Fin n) K 1) :
    restrict B ℓ = 0 ↔ coeffVector ℓ ᵥ* B = 0 := by
  have h : restrict B ℓ = linearForm (coeffVector ℓ ᵥ* B) := by
    rw [← restrict_linearForm, linearForm_coeffVector hℓ]
  rw [h, linearForm_eq_zero_iff]

/-- The linear forms vanishing on the slice: degree-one homogeneous polynomials in the kernel
of `restrict B`. -/
noncomputable def linearAnnihilator (B : Matrix (Fin n) (Fin m) K) :
    Submodule K (MvPolynomial (Fin n) K) :=
  homogeneousSubmodule (Fin n) K 1 ⊓ LinearMap.ker (restrict B).toLinearMap

theorem mem_linearAnnihilator (B : Matrix (Fin n) (Fin m) K) (ℓ : MvPolynomial (Fin n) K) :
    ℓ ∈ linearAnnihilator B ↔
      ℓ ∈ homogeneousSubmodule (Fin n) K 1 ∧ restrict B ℓ = 0 :=
  Iff.rfl

/-- Characterisation of the annihilator by coefficient vectors. -/
theorem mem_linearAnnihilator_iff_vecMul (B : Matrix (Fin n) (Fin m) K)
    (ℓ : MvPolynomial (Fin n) K) :
    ℓ ∈ linearAnnihilator B ↔
      ℓ ∈ homogeneousSubmodule (Fin n) K 1 ∧ coeffVector ℓ ᵥ* B = 0 := by
  rw [mem_linearAnnihilator]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, (restrict_eq_zero_iff_vecMul_eq_zero B h1).mp h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (restrict_eq_zero_iff_vecMul_eq_zero B h1).mpr h2⟩

end SliceLemmas

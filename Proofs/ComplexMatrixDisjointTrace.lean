module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

/-!
The complex trace pairing is the sum of entrywise conjugate products.
Matrices with disjoint entry supports therefore have trace pairing zero.
The row and column index types may differ; only their finite sums are used.

These elementary identities are first-party proofs from the definitions in
mathlib, with no copied proof body or novelty claim. The imported mathlib
revision is065356127b1dc0016f66b7283ce0ce2c4055aa55 (Apache-2.0), with
Lean4.35.0-rc2. Thanks to the mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke,1676. No release license is selected here.
-/

namespace QuadraticCertificate.ComplexMatrixSupport

open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The trace of the product with a conjugate transpose, in entry coordinates. -/
theorem trace_mul_conjTranspose_eq_sum (A B : Matrix ι κ ℂ) :
    (A * B.conjTranspose).trace = ∑ i, ∑ j, A i j * star (B i j) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]

/-- Each trace summand vanishes when at least one of its two entries vanishes. -/
theorem trace_mul_conjTranspose_eq_zero_of_disjoint (A B : Matrix ι κ ℂ)
    (h : ∀ i j, A i j = 0 ∨ B i j = 0) :
    (A * B.conjTranspose).trace = 0 := by
  rw [trace_mul_conjTranspose_eq_sum]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  rcases h i j with hA | hB
  · rw [hA, zero_mul]
  · rw [hB, star_zero, mul_zero]

end QuadraticCertificate.ComplexMatrixSupport

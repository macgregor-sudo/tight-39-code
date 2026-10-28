module

public import NativeIncludedQuartetReadouts

@[expose] public section

/-!
The actual TitsComplexMatrix real-linear commutant of left Hermitian products.
No replacement carrier, complex-linearity hypothesis or full-matrix-commutation
premise is introduced. Arbitrary complex matrix units are derived below.
This is an algebraic implication only: native fixer binding and the multiplier's
metric/unitarity/determinant properties remain separate obligations.

First-party composition of the accepted native owner and pinned Mathlib matrix
unit APIs (065356127b1dc0016f66b7283ce0ce2c4055aa55, Apache-2.0).
No upstream proof body is copied. Thanks to the native-model and Mathlib
contributors. “If I have seen further it is by standing on the sholders of
Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace CompactAlbert

open scoped BigOperators

/-- On the actual native complex matrix carrier, commuting with every left
Hermitian multiplication forces right multiplication by the value at one. -/
theorem eq_right_mul_of_hermitian_left_commutation
    (phi : TitsComplexMatrix →ₗ[Real] TitsComplexMatrix)
    (hphi : ∀ H : TitsComplexMatrix, H.IsHermitian →
      ∀ B : TitsComplexMatrix, phi (H * B) = H * phi B) :
    ∀ B : TitsComplexMatrix, phi B = B * phi 1 := by
  classical
  have hproduct (A D : TitsComplexMatrix)
      (hA : ∀ B, phi (A * B) = A * phi B)
      (hD : ∀ B, phi (D * B) = D * phi B) :
      ∀ B, phi ((A * D) * B) = (A * D) * phi B := by
    intro B
    rw [Matrix.mul_assoc, hA, hD, Matrix.mul_assoc]
  have hdiagonal (i : Fin 3) :
      ∀ B, phi (Matrix.single i i (1 : Complex) * B) =
        Matrix.single i i (1 : Complex) * phi B := by
    apply hphi
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_single, star_one]
  have hoffdiagonal (i j : Fin 3) (z : Complex) (hij : i ≠ j) :
      ∀ B, phi (Matrix.single i j z * B) = Matrix.single i j z * phi B := by
    have hHermitian :
        (Matrix.single i j z + Matrix.single j i (star z)).IsHermitian := by
      simp only [Matrix.IsHermitian, Matrix.conjTranspose_add,
        Matrix.conjTranspose_single, star_star]
      exact add_comm _ _
    have hunit :
        Matrix.single i i (1 : Complex) *
          (Matrix.single i j z + Matrix.single j i (star z)) = Matrix.single i j z := by
      rw [Matrix.mul_add, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne (1 : Complex) i i j hij (star z)]
      simp only [one_mul, add_zero]
    have h := hproduct (Matrix.single i i (1 : Complex))
      (Matrix.single i j z + Matrix.single j i (star z))
      (hdiagonal i) (hphi _ hHermitian)
    simpa only [hunit] using h
  -- A distinct intermediate index supplies arbitrary complex diagonal units.
  have hsingle (i j : Fin 3) (z : Complex) :
      ∀ B, phi (Matrix.single i j z * B) = Matrix.single i j z * phi B := by
    by_cases hij : i = j
    · subst j
      obtain ⟨k, hki⟩ := exists_ne i
      have h := hproduct (Matrix.single i k z) (Matrix.single k i (1 : Complex))
        (hoffdiagonal i k z hki.symm) (hoffdiagonal k i 1 hki)
      simpa only [Matrix.single_mul_single_same, mul_one] using h
    · exact hoffdiagonal i j z hij
  have hone (i j : Fin 3) (z : Complex) :
      phi (Matrix.single i j z) = Matrix.single i j z * phi 1 := by
    simpa only [Matrix.mul_one] using hsingle i j z (1 : TitsComplexMatrix)
  intro B
  calc
    phi B = phi (∑ i : Fin 3, ∑ j : Fin 3, Matrix.single i j (B i j)) :=
      congrArg phi (Matrix.matrix_eq_sum_single B)
    _ = ∑ i : Fin 3, ∑ j : Fin 3, phi (Matrix.single i j (B i j)) := by
      simp only [map_sum]
    _ = ∑ i : Fin 3, ∑ j : Fin 3, Matrix.single i j (B i j) * phi 1 := by
      simp only [hone]
    _ = (∑ i : Fin 3, ∑ j : Fin 3, Matrix.single i j (B i j)) * phi 1 := by
      simp only [Finset.sum_mul]
    _ = B * phi 1 := by rw [← Matrix.matrix_eq_sum_single B]

end CompactAlbert

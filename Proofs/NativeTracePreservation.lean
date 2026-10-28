module

public import NativePolynomialEvaluationStaged
public import Mathlib.LinearAlgebra.Trace

@[expose] public section

/-!
Intrinsic native trace preservation from Jordan-product preservation.
The left multiplication operator and upper-coordinate equivalence are the
accepted native ones; no coordinate tensor or certificate is generated.
First-party symbolic proof composition with pinned Mathlib trace APIs
(065356127b1dc0016f66b7283ce0ce2c4055aa55, Apache-2.0).
Thanks to the native-model and Mathlib contributors. “If I have seen further
it is by standing on the sholders of Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
namespace Glennie
open NativePolynomial
open scoped BigOperators

private theorem oct_mul_zero_right (q : Octonion) : octMul q 0 = 0 := by
  simpa [octScalar, Prod.mk_zero_zero] using octMul_scalar_right 0 q

private theorem oct_mul_zero_left (q : Octonion) : octMul 0 q = 0 := by
  simpa [octScalar, Prod.mk_zero_zero] using octMul_scalar_left 0 q

private theorem oct_conj_zero : octConj 0 = 0 := octConjAddHom.map_zero

private theorem oct_dot_zero_right (q : Octonion) : octDot q 0 = 0 := by
  rw [octDot, oct_conj_zero, oct_mul_zero_right]
  rfl

-- Cancel off-block terms before exposing any scalar coordinates.
private theorem left_o01_block (x : Albert) (q : Octonion) :
    (jordan x ⟨0, 0, 0, q, 0, 0⟩).o01 =
      (1 / 2 : ℝ) • ((x.d0 + x.d1) • q) := by
  rw [jordan_o01]
  simp only [zero_smul, add_zero, oct_conj_zero,
    oct_mul_zero_right, oct_mul_zero_left]

private theorem left_o02_block (x : Albert) (q : Octonion) :
    (jordan x ⟨0, 0, 0, 0, q, 0⟩).o02 =
      (1 / 2 : ℝ) • ((x.d0 + x.d2) • q) := by
  rw [jordan_o02]
  simp only [zero_smul, add_zero, oct_conj_zero,
    oct_mul_zero_right, oct_mul_zero_left]

private theorem left_o12_block (x : Albert) (q : Octonion) :
    (jordan x ⟨0, 0, 0, 0, 0, q⟩).o12 =
      (1 / 2 : ℝ) • ((x.d1 + x.d2) • q) := by
  rw [jordan_o12]
  simp only [zero_smul, add_zero, oct_conj_zero,
    oct_mul_zero_right, oct_mul_zero_left]

private def leftDiagonal (x : Albert) (i : Fin 27) : ℝ :=
  upperCoordinates (jordan x (nativeCoordinateBasis i)) i

private theorem left_diagonal_d0 (x : Albert) : leftDiagonal x 0 = x.d0 := by
  change (jordan x ⟨1, 0, 0, 0, 0, 0⟩).d0 = _
  rw [jordan_d0]
  simp [oct_dot_zero_right]

private theorem left_diagonal_d1 (x : Albert) : leftDiagonal x 1 = x.d1 := by
  change (jordan x ⟨0, 1, 0, 0, 0, 0⟩).d1 = _
  rw [jordan_d1]
  simp [oct_dot_zero_right]

private theorem left_diagonal_d2 (x : Albert) : leftDiagonal x 2 = x.d2 := by
  change (jordan x ⟨0, 0, 1, 0, 0, 0⟩).d2 = _
  rw [jordan_d2]
  simp [oct_dot_zero_right]

private theorem quaternion_zero_mk : (⟨0, 0, 0, 0⟩ : Quaternion ℝ) = 0 := rfl

private theorem left_diagonal_o01 (x : Albert) (k : Fin 8) :
    leftDiagonal x (Fin.castAdd 16 (Fin.natAdd 3 k)) = (x.d0 + x.d1) / 2 := by
  fin_cases k <;>
    norm_num [leftDiagonal, upperCoordinates, nativeCoordinateBasis,
      fromUpperCoordinates, quaternion_zero_mk, Prod.mk_zero_zero, left_o01_block, smul_eq_mul] <;> ring

private theorem left_diagonal_o02 (x : Albert) (k : Fin 8) :
    leftDiagonal x (Fin.castAdd 8 (Fin.natAdd 11 k)) = (x.d0 + x.d2) / 2 := by
  fin_cases k <;>
    norm_num [leftDiagonal, upperCoordinates, nativeCoordinateBasis,
      fromUpperCoordinates, quaternion_zero_mk, Prod.mk_zero_zero, left_o02_block, smul_eq_mul] <;> ring

private theorem left_diagonal_o12 (x : Albert) (k : Fin 8) :
    leftDiagonal x (Fin.natAdd 19 k) = (x.d1 + x.d2) / 2 := by
  fin_cases k <;>
    norm_num [leftDiagonal, upperCoordinates, nativeCoordinateBasis,
      fromUpperCoordinates, quaternion_zero_mk, Prod.mk_zero_zero, left_o12_block, smul_eq_mul] <;> ring

/-- The actual native left-Jordan endomorphism has linear trace nine times the
native Albert trace. Three scalar and three uniform octonion blocks suffice. -/
theorem jordanLinear_trace (x : Albert) :
    LinearMap.trace ℝ Albert (jordanLinear x) = 9 * trace x := by
  rw [← LinearMap.trace_conj' (jordanLinear x) upperCoordinateEquiv,
    LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 27)),
    LinearMap.toMatrix_eq_toMatrix']
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix'_apply,
    LinearEquiv.conj_apply_apply, jordanLinear_apply]
  have hsingle (i : Fin 27) :
      upperCoordinateEquiv.symm (Pi.single i 1) = nativeCoordinateBasis i := by
    change fromUpperCoordinates (Pi.single i 1) = fromUpperCoordinates _
    apply congrArg fromUpperCoordinates
    funext j
    simp [Pi.single_apply, eq_comm]
  simp only [hsingle]
  change (∑ i : Fin 27, leftDiagonal x i) = _
  rw [Fin.sum_univ_add (a := 19) (b := 8),
    Fin.sum_univ_add (a := 11) (b := 8),
    Fin.sum_univ_add (a := 3) (b := 8)]
  change (((∑ i : Fin 3, leftDiagonal x (Fin.castAdd 24 i)) +
    ∑ k : Fin 8, leftDiagonal x (Fin.castAdd 16 (Fin.natAdd 3 k))) +
    ∑ k : Fin 8, leftDiagonal x (Fin.castAdd 8 (Fin.natAdd 11 k))) +
    (∑ k : Fin 8, leftDiagonal x (Fin.natAdd 19 k)) = _
  simp only [Fin.sum_univ_three, left_diagonal_d0, left_diagonal_d1,
    left_diagonal_d2, left_diagonal_o01, left_diagonal_o02, left_diagonal_o12]
  norm_num [trace, left_diagonal_d0, left_diagonal_d1, left_diagonal_d2]
  <;> ring

/-- Real-linear bijective Jordan-product preservation intrinsically preserves
native trace; no trace, metric, unit or anchor premise occurs. -/
theorem trace_preserved_of_jordan_equiv (f : Albert ≃ₗ[ℝ] Albert)
    (hprod : ∀ x y : Albert, f (jordan x y) = jordan (f x) (f y))
    (x : Albert) : trace (f x) = trace x := by
  have hconj : f.conj (jordanLinear x) = jordanLinear (f x) := by
    apply LinearMap.ext
    intro y
    change f (jordan x (f.symm y)) = jordan (f x) y
    rw [hprod, f.apply_symm_apply]
  have h := LinearMap.trace_conj' (jordanLinear x) f
  rw [hconj, jordanLinear_trace, jordanLinear_trace] at h
  linarith

/-- Preservation of the actual native trace pairing follows from the intrinsic
trace theorem and the product equation, rather than being assumed. -/
theorem trace_pairing_preserved_of_jordan_equiv (f : Albert ≃ₗ[ℝ] Albert)
    (hprod : ∀ x y : Albert, f (jordan x y) = jordan (f x) (f y))
    (x y : Albert) : trace (jordan (f x) (f y)) = trace (jordan x y) := by
  rw [← hprod]
  exact trace_preserved_of_jordan_equiv f hprod (jordan x y)

end Glennie

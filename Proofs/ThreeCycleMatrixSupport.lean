module

public import UEBResidualDerivative
public import ThreeCyclePhaseReconstruction
import all FourierTransport

/-!
# Actual cyclic matrix support underlying the scalar pair equations

The matrices here are the original shift, clock and phaseMatrix. In particular,
shift sends e_j to e_(j+1). The trace-support identity holds for arbitrary
matrices; no restriction on the ambient variation or its support is assumed.
Mathematical source: MASTER.md §6.4, equations (6.5)–(6.6).
Original first-party proofs, importing the existing pinned mathlib APIs.
No upstream implementation is copied and no release license is assigned.
-/

@[expose] public section
noncomputable section

namespace UnitaryErrorBases.ThreeCycleMatrix

open scoped BigOperators

private lemma indexCases (i : Index) : i = 0 ∨ i = 1 ∨ i = 2 := by
  exact (by decide : ∀ j : Index, j = 0 ∨ j = 1 ∨ j = 2) i

@[simp] lemma i11 : (1 : Index) + 1 = 2 := by decide
@[simp] lemma i12 : (1 : Index) + 2 = 0 := by decide
@[simp] lemma i21 : (2 : Index) + 1 = 0 := by decide
@[simp] lemma i22 : (2 : Index) + 2 = 1 := by decide
@[simp] lemma in1 : -(1 : Index) = 2 := by decide
@[simp] lemma in2 : -(2 : Index) = 1 := by decide
@[simp] lemma i02 : (0 : Index) ≠ 2 := by decide
@[simp] lemma i20 : (2 : Index) ≠ 0 := by decide
@[simp] lemma i12ne : (1 : Index) ≠ 2 := by decide
@[simp] lemma i21ne : (2 : Index) ≠ 1 := by decide

private lemma sum_three (f : Index → ℂ) : ∑ i, f i = f 0 + f 1 + f 2 :=
  Fin.sum_univ_three f

lemma shift_mul_apply (M : Mat) (i j : Index) :
    (shift * M) i j = M (i - 1) j := by
  rcases indexCases i with rfl | rfl | rfl <;>
    simp [Matrix.mul_apply, shift, sum_three, sub_eq_add_neg]

lemma mul_shift_apply (M : Mat) (i j : Index) :
    (M * shift) i j = M i (j + 1) := by
  rcases indexCases j with rfl | rfl | rfl <;>
    simp [Matrix.mul_apply, shift, sum_three]

lemma weightedShift_mul_apply (u : Index → ℂ) (M : Mat) (i j : Index) :
    ((Matrix.diagonal u * shift) * M) i j = u i * M (i - 1) j := by
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, shift_mul_apply]

lemma mul_weightedShift_apply (M : Mat) (u : Index → ℂ) (i j : Index) :
    (M * (Matrix.diagonal u * shift)) i j = M i (j + 1) * u (j + 1) := by
  rw [← Matrix.mul_assoc, mul_shift_apply, Matrix.mul_diagonal]

/-- Extract the three forward cyclic entries from every unrestricted matrix. -/
def offDiagonalCoordinates (M : Family) : ThreeCycleFourier.Coordinates :=
  fun a b k => M (a, b) k (k + 1)

/-- The exact trace support giving equation (6.6), for every matrix family.
Neither anti-Hermiticity nor vanishing diagonal entries are needed here. -/
theorem cyclic_pair_trace (u : Index → Index → ℂ) (M : Family)
    (b a a' : Index) :
    Matrix.trace
      (Matrix.diagonal (fun k => ThreeCycleFourier.character ((a' - a) * k)) *
        ((Matrix.diagonal (u b) * shift) * M (a', b + 1) -
          M (a, b) * (Matrix.diagonal (u b) * shift))) =
      ThreeCycleFourier.pairEquation u (offDiagonalCoordinates M) b a a' := by
  change (∑ k : Index, _) = ∑ k : Index, _
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.diag_apply, Matrix.diagonal_mul, Matrix.sub_apply, weightedShift_mul_apply,
    mul_weightedShift_apply, offDiagonalCoordinates, sub_add_cancel]
  ring

/-- The actual left factor of the original monomial family. -/
def leftFactor (d : PhaseTriple) (b : Index) : Mat :=
  shift ^ b.val * phaseMatrix d b

/-- The actual right factor of the original monomial family. -/
def rightFactor (a : Index) : Mat := clock ^ a.val

lemma monomialFamily_eq (d : PhaseTriple) (a b : Index) :
    monomialFamily d (a, b) = leftFactor d b * rightFactor a := rfl

lemma shift_pow_apply (b i j : Index) :
    (shift ^ b.val) i j = if i = j + b then 1 else 0 := by
  rcases indexCases b with rfl | rfl | rfl
  · simp [Matrix.one_apply]
  · change (shift ^ 1) i j = if i = j + 1 then 1 else 0
    simp only [pow_one, shift]
  · change (shift ^ 2) i j = if i = j + 2 then 1 else 0
    have h : i - 1 = j + 1 ↔ i = j + 2 :=
      (by decide : ∀ i j : Index, i - 1 = j + 1 ↔ i = j + 2) i j
    rw [pow_two, shift_mul_apply]
    simp only [shift, h]

lemma leftFactor_apply (d : PhaseTriple) (b i j : Index) :
    leftFactor d b i j =
      if i = j + b then ThreeCycleFourier.phaseEntry d.val b j else 0 := by
  simp only [leftFactor, phaseMatrix, Matrix.mul_diagonal, shift_pow_apply,
    ThreeCycleFourier.phaseEntry]
  split_ifs <;> simp_all

/-- The actual adjacent left-factor product has exactly the scalar phaseWeight.
This identity holds without using the unit-modulus or product-one conditions. -/
theorem leftFactor_adjacent (d : PhaseTriple) (b : Index) :
    (leftFactor d b).conjTranspose * leftFactor d (b + 1) =
      Matrix.diagonal (ThreeCycleFourier.phaseWeight d.val b) * shift := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, leftFactor_apply,
    Matrix.diagonal_mul]
  rcases indexCases b with rfl | rfl | rfl <;>
    rcases indexCases i with rfl | rfl | rfl <;>
    rcases indexCases j with rfl | rfl | rfl <;>
    simp [sum_three, ThreeCycleFourier.phaseWeight, ThreeCycleFourier.phaseEntry,
      shift, sub_eq_add_neg]

end UnitaryErrorBases.ThreeCycleMatrix

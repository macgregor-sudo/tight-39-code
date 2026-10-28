module

public import ThreeCycleTangentConverse
import all FourierTransport

/-!
# Concrete real diagonal and resonant Fourier parameters give original tangents

The three block diagonals have two free real entries each; the third is their
negative sum. The cyclic off-diagonal entries are arbitrary complex values,
with the reverse entries fixed by anti-Hermiticity. Applying the already proved
scalar reconstruction gives genuine vectors in the original derivative kernel.
This is a constructor, not a dimension theorem or a claim of surjectivity.
First-party proof; imported mathlib provenance unchanged. No release license assigned.
-/

@[expose] public section
noncomputable section

namespace UnitaryErrorBases.ThreeCycleMatrix

open ThreeCycleFourier

def tracelessDiagonal (s : Fin 2 → ℝ) (k : Index) : ℝ :=
  if k = 0 then s 0 else if k = 1 then s 1 else -s 0 - s 1

def parameterMatrix (s : Index → Fin 2 → ℝ) (y : Coordinates) : Family :=
  fun p i j => if i = j then Complex.I * (tracelessDiagonal (s p.2) i : ℂ)
    else if j = i + 1 then y p.1 p.2 i else -star (y p.1 p.2 j)

theorem parameterMatrix_diagonal (s : Index → Fin 2 → ℝ) (y : Coordinates)
    (a b k : Index) :
    parameterMatrix s y (a, b) k k = Complex.I * (tracelessDiagonal (s b) k : ℂ) := by
  simp [parameterMatrix]

theorem parameterMatrix_antiHermitian (s : Index → Fin 2 → ℝ) (y : Coordinates)
    (p : Label) : (parameterMatrix s y p).conjTranspose = -parameterMatrix s y p := by
  ext i j
  change star (parameterMatrix s y p j i) = -parameterMatrix s y p i j
  by_cases hij : i = j
  · subst j
    simp [parameterMatrix]
  · have hji : j ≠ i := Ne.symm hij
    by_cases hj : j = i + 1
    · have hi : i ≠ j + 1 :=
        (by decide : ∀ i j : Index, j = i + 1 → i ≠ j + 1) i j hj
      simp only [parameterMatrix, if_neg hij, if_neg hji, if_pos hj, if_neg hi]
      simp
    · have hi : i = j + 1 :=
        (by decide : ∀ i j : Index, i ≠ j → j ≠ i + 1 → i = j + 1) i j hij hj
      simp only [parameterMatrix, if_neg hij, if_neg hji, if_neg hj, if_pos hi]
      simp

theorem parameterMatrix_trace (s : Index → Fin 2 → ℝ) (y : Coordinates) (p : Label) :
    Matrix.trace (parameterMatrix s y p) = 0 := by
  calc
    Matrix.trace (parameterMatrix s y p) =
      parameterMatrix s y p 0 0 + parameterMatrix s y p 1 1 +
        parameterMatrix s y p 2 2 := Fin.sum_univ_three _
    _ = 0 := by
      simp [parameterMatrix, tracelessDiagonal, show (2 : Index) ≠ 0 by decide,
        show (2 : Index) ≠ 1 by decide]
      ring

theorem parameterMatrix_offDiagonal (s : Index → Fin 2 → ℝ) (y : Coordinates) :
    offDiagonalCoordinates (parameterMatrix s y) = y := by
  funext a b k
  have hk : k ≠ k + 1 := by
    intro h
    have := add_left_cancel (h.symm.trans (add_zero k).symm)
    exact (by decide : (1 : Index) ≠ 0) this
  simp [offDiagonalCoordinates, parameterMatrix, hk]

theorem parameterMatrix_mem_firstOrder (d : PhaseTriple) (s : Index → Fin 2 → ℝ)
    (a : Index → Index → ℂ) (ha : ResonanceSupported d a) :
    fromCoordinates d (parameterMatrix s (inverse (reconstruct d a))) ∈
      firstOrderSpace (monomialFamily d) := by
  apply fromCoordinates_mem_firstOrder
  · exact parameterMatrix_antiHermitian s _
  · exact parameterMatrix_trace s _
  · intro a a' b k
    rw [parameterMatrix_diagonal, parameterMatrix_diagonal]
  · rw [parameterMatrix_offDiagonal]
    exact (inverse_reconstruct_pairEquations_iff d a).mpr ha

end UnitaryErrorBases.ThreeCycleMatrix

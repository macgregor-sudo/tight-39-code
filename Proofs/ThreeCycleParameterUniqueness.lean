module

public import ThreeCycleParameterRecovery
import all FourierTransport

/-!
# Exact read-back and uniqueness for the tangent constructor

These small inverse identities leave only real-linear packaging and canonical
finite-index reindexing for the frozen NormalForm equivalence.
First-party proof; imported mathlib provenance unchanged. No release license assigned.
-/

@[expose] public section
noncomputable section

namespace UnitaryErrorBases.ThreeCycleMatrix

open ThreeCycleFourier

theorem diagonalParameters_parameterMatrix (s : Index → Fin 2 → ℝ) (y : Coordinates) :
    diagonalParameters (parameterMatrix s y) = s := by
  funext b t
  fin_cases t <;> simp [diagonalParameters, parameterMatrix, tracelessDiagonal]

theorem reconstruct_zero (d : PhaseTriple) (a : Index → Index → ℂ) :
    reconstruct d a 0 = a := by
  funext k mu
  simp [reconstruct]

theorem constructor_diagonal_readback (d : PhaseTriple) (s : Index → Fin 2 → ℝ)
    (a : Index → Index → ℂ) :
    diagonalParameters
      (toCoordinates d (fromCoordinates d (parameterMatrix s (inverse (reconstruct d a))))) = s := by
  rw [toCoordinates_fromCoordinates, diagonalParameters_parameterMatrix]

theorem constructor_seed_readback (d : PhaseTriple) (s : Index → Fin 2 → ℝ)
    (a : Index → Index → ℂ) :
    forward (offDiagonalCoordinates
      (toCoordinates d (fromCoordinates d (parameterMatrix s (inverse (reconstruct d a)))))) 0 = a := by
  rw [toCoordinates_fromCoordinates, parameterMatrix_offDiagonal, forward_inverse, reconstruct_zero]

/-- No support condition is needed for injectivity of the parameter constructor. -/
theorem tangent_parameters_injective (d : PhaseTriple)
    (s t : Index → Fin 2 → ℝ) (a c : Index → Index → ℂ)
    (h : fromCoordinates d (parameterMatrix s (inverse (reconstruct d a))) =
      fromCoordinates d (parameterMatrix t (inverse (reconstruct d c)))) : s = t ∧ a = c := by
  constructor
  · have hh := congrArg (fun V => diagonalParameters (toCoordinates d V)) h
    simpa only [constructor_diagonal_readback] using hh
  · have hh := congrArg (fun V => forward (offDiagonalCoordinates (toCoordinates d V)) 0) h
    simpa only [constructor_seed_readback] using hh

end UnitaryErrorBases.ThreeCycleMatrix

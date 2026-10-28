module

public import ThreeCycleKernelToFourier

/-!
# Determinant-one and trace differential for the actual monomial matrices

These proofs use the original shift, clock and product-one PhaseTriple, rather
than a special-unitary compatibility hypothesis. First-party proof; imported
mathlib provenance is unchanged. No release license is assigned here.
-/

@[expose] public section
noncomputable section

namespace UnitaryErrorBases.ThreeCycleMatrix

open scoped BigOperators

lemma shift_det : shift.det = 1 := by
  calc
    shift.det = shift 0 0 * shift 1 1 * shift 2 2 - shift 0 0 * shift 1 2 * shift 2 1
      - shift 0 1 * shift 1 0 * shift 2 2 + shift 0 1 * shift 1 2 * shift 2 0
      + shift 0 2 * shift 1 0 * shift 2 1 - shift 0 2 * shift 1 1 * shift 2 0 :=
        Matrix.det_fin_three (shift : Matrix (Fin 3) (Fin 3) ℂ)
    _ = 1 := by
      simp [shift, show (1 : Index) + 1 = 2 by decide,
        show (2 : Index) + 1 = 0 by decide, show (2 : Index) ≠ 0 by decide,
        show (1 : Index) ≠ 2 by decide, show (0 : Index) ≠ 2 by decide,
        show (2 : Index) ≠ 1 by decide]

lemma clock_det : clock.det = 1 := by
  rw [clock, Matrix.det_diagonal]
  calc
    (∏ j : Index, omega ^ j.val) = omega ^ 0 * omega ^ 1 * omega ^ 2 :=
      Fin.prod_univ_three (fun j : Index => omega ^ j.val)
    _ = omega ^ 3 := by ring
    _ = 1 := omega_cube

lemma phaseMatrix_det (d : PhaseTriple) (b : Index) : (phaseMatrix d b).det = 1 := by
  rw [phaseMatrix, Matrix.det_diagonal]
  by_cases hb : b = 2
  · simpa only [if_pos hb] using d.property.2
  · simp [hb]

theorem monomialFamily_specialUnitary (d : PhaseTriple) (p : Label) :
    IsSpecialUnitary (monomialFamily d p) := by
  constructor
  · change (leftFactor d p.2 * rightFactor p.1).conjTranspose *
      (leftFactor d p.2 * rightFactor p.1) = 1
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (leftFactor d p.2).conjTranspose
      (leftFactor d p.2) (rightFactor p.1), leftFactor_star_mul, Matrix.one_mul,
      rightFactor_star_mul]
  · simp [monomialFamily, Matrix.det_mul, Matrix.det_pow, shift_det, clock_det,
      phaseMatrix_det]

theorem trace_fromCoordinates (d : PhaseTriple) (M : Family) (p : Label) :
    Matrix.trace ((monomialFamily d p).conjTranspose * fromCoordinates d M p) =
      Matrix.trace (M p) := by
  change Matrix.trace ((leftFactor d p.2 * rightFactor p.1).conjTranspose *
    (leftFactor d p.2 * M p * rightFactor p.1)) = _
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (leftFactor d p.2).conjTranspose
    (leftFactor d p.2) (M p * rightFactor p.1), leftFactor_star_mul, Matrix.one_mul]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, rightFactor_mul_star, Matrix.one_mul]

/-- The determinant differential of the original monomial family is exactly
trace M, with no determinant-one premise left to an eventual consumer. -/
theorem determinantDerivative_fromCoordinates (d : PhaseTriple) (M : Family) (p : Label) :
    ArchitectureUEBDerivative.detMultilinear.linearDeriv (monomialFamily d p)
      (fromCoordinates d M p) = Matrix.trace (M p) :=
  (ArchitectureUEBDerivative.detDerivative_apply_of_specialUnitary _ _
    (monomialFamily_specialUnitary d p)).trans (trace_fromCoordinates d M p)

end UnitaryErrorBases.ThreeCycleMatrix

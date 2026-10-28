module

public import ThreeCycleMatrixTrivialization

/-!
# Original derivative-kernel to actual scalar Fourier equations

This module consumes the literal fderiv kernel at monomialFamily d. It derives
the Gram and ordered-pair equations from the accepted derivative formula,
then uses the proved invertible matrix trivialization and trace support.
No replacement residual, support restriction, UEB hypothesis or scalar bridge
is assumed. The determinant and within-block converse are separate conclusions.
First-party proof; no upstream implementation copied or release license assigned.
-/

@[expose] public section
noncomputable section

namespace UnitaryErrorBases.ThreeCycleMatrix

open ArchitectureUEBDerivative
open scoped Matrix.Norms.Elementwise

/-- Two literal components of the original derivative kernel, at any ambient U.
This lemma does not assert that these two components exhaust the kernel. -/
theorem gram_pair_of_mem_firstOrder (U V : Family) (hV : V ∈ firstOrderSpace U) :
    (∀ p, (U p).conjTranspose * V p + (V p).conjTranspose * U p = 0) ∧
      (∀ p q, p ≠ q →
        Matrix.trace ((V p).conjTranspose * U q + (U p).conjTranspose * V q) = 0) := by
  change fderiv ℝ residualOnAmbient U V = 0 at hV
  rw [(hasFDerivAt_residual U).fderiv] at hV
  constructor
  · intro p
    have h := congrArg (fun R : AmbientResidual => R.1 p) hV
    change productDerivative U p p V = 0 at h
    exact (productDerivative_apply U V p p).symm.trans h
  · intro p q hpq
    have h := congrArg (fun R : AmbientResidual => R.2.2 p q) hV
    change ((residualDerivative U) V).2.2 p q = 0 at h
    have he : ((residualDerivative U) V).2.2 p q = pairingDerivative U p q V := by
      change (if p = q then (0 : AmbientFamily →L[ℝ] ℂ)
        else pairingDerivative U p q) V = pairingDerivative U p q V
      rw [if_neg hpq]
    exact (pairingDerivative_apply U V p q).symm.trans (he.symm.trans h)

/-- The extracted full matrix family is anti-Hermitian as a consequence of the
original Gram differential; this is not imposed on the ambient variation. -/
theorem toCoordinates_antiHermitian_of_mem_firstOrder (d : PhaseTriple) (V : Family)
    (hV : V ∈ firstOrderSpace (monomialFamily d)) (p : Label) :
    (toCoordinates d V p).conjTranspose = -toCoordinates d V p := by
  apply antiHermitian_of_gram d (toCoordinates d V) p
  rw [fromCoordinates_toCoordinates]
  exact (gram_pair_of_mem_firstOrder _ V hV).1 p

/-- Every literal derivative-kernel vector satisfies the existing scalar
pairEquation, with the original shift orientation and phaseWeight. -/
theorem pairEquations_of_mem_firstOrder (d : PhaseTriple) (V : Family)
    (hV : V ∈ firstOrderSpace (monomialFamily d)) :
    ∀ b a a', ThreeCycleFourier.pairEquation (ThreeCycleFourier.phaseWeight d.val)
      (offDiagonalCoordinates (toCoordinates d V)) b a a' = 0 := by
  intro b a a'
  have hb : b ≠ b + 1 := (by decide : ∀ b : Index, b ≠ b + 1) b
  have hpq : (a, b) ≠ (a', b + 1) := fun h => hb (congrArg Prod.snd h)
  calc
    _ = Matrix.trace
        ((fromCoordinates d (toCoordinates d V) (a, b)).conjTranspose *
            monomialFamily d (a', b + 1) +
          (monomialFamily d (a, b)).conjTranspose *
            fromCoordinates d (toCoordinates d V) (a', b + 1)) :=
      (pair_trace_eq_scalar d (toCoordinates d V) b a a'
        (toCoordinates_antiHermitian_of_mem_firstOrder d V hV (a, b))).symm
    _ = 0 := by
      rw [fromCoordinates_toCoordinates]
      exact (gram_pair_of_mem_firstOrder _ V hV).2 _ _ hpq

/-- A direct consumer of the accepted scalar reconstruction, now fed by the
actual original derivative kernel instead of an assumed scalar solution. -/
theorem offDiagonal_reconstruction_of_mem_firstOrder (d : PhaseTriple) (V : Family)
    (hV : V ∈ firstOrderSpace (monomialFamily d)) :
    ThreeCycleFourier.ResonanceSupported d
        (ThreeCycleFourier.forward (offDiagonalCoordinates (toCoordinates d V)) 0) ∧
      offDiagonalCoordinates (toCoordinates d V) =
        ThreeCycleFourier.inverse
          (ThreeCycleFourier.reconstruct d
            (ThreeCycleFourier.forward (offDiagonalCoordinates (toCoordinates d V)) 0)) :=
  (ThreeCycleFourier.pairEquations_iff_reconstruction d _).mp
    (pairEquations_of_mem_firstOrder d V hV)

end UnitaryErrorBases.ThreeCycleMatrix

/-
Remaining original Challenge definitions, importing the accepted six-definition
ChallengeUEBDefinitions owner. The two blocks below are byte-identical excerpts
from frozen ChallengeInterfaceProbe.lean (SHA256
291001bd5d684d2c84054a2bad0e2d1aa59ff672787c9ba2e9fa90eb2ce03c0c).
Only module imports/public exposure change. No original equation, phase condition,
ambient carrier, norm scope or endpoint definition is changed.
First-party extraction; upstream imports retain the attribution and Apache-2.0
provenance recorded in ChallengeUEBDefinitions. No release license is assigned.
-/
module

public import ChallengeUEBDefinitions
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

open scoped Matrix.Norms.Elementwise
@[expose] public section
noncomputable section

namespace UnitaryErrorBases

/-- Matrix unitarity, scalar determinant and ordered pair residuals. -/
abbrev Residual := (Label → Mat) × (Label → ℂ) × (Label → Label → ℂ)

/-- The specified primitive cube root of unity. -/
def omega : ℂ := (-1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2

/-- The cyclic permutation matrix sending the j-th basis vector to j+1. -/
def shift : Mat := fun i j => if i = j + 1 then 1 else 0

/-- The diagonal clock matrix with successive powers of omega. -/
def clock : Mat := Matrix.diagonal (fun j => omega ^ j.val)

/-- Three unit complex phases whose product is one. -/
abbrev PhaseTriple :=
  {d : Index → ℂ // (∀ j, Complex.normSq (d j) = 1) ∧ ∏ j, d j = 1}

/-- The phase diagonal in block two, and the identity in other blocks. -/
def phaseMatrix (d : PhaseTriple) (b : Index) : Mat :=
  Matrix.diagonal (fun j => if b = 2 then d.val j else 1)

/-- The order of factors fixes the cyclic-index convention. -/
def monomialFamily (d : PhaseTriple) : Family := fun p =>
  shift ^ p.2.val * phaseMatrix d p.2 * clock ^ p.1.val

/-- Original unitarity, determinant-one and all pair-orthogonality residuals. -/
def residual (U : Family) : Residual :=
  (fun p => (U p).conjTranspose * U p - 1,
   fun p => (U p).det - 1,
   fun p q => if p = q then 0 else Matrix.trace ((U p).conjTranspose * U q))

/-- The kernel of the real derivative in the full matrix-family ambient. -/
def firstOrderSpace (U : Family) : Submodule ℝ Family :=
  (fderiv ℝ residual U).toLinearMap.ker

/-- Every ambient variation is allowed; no support restriction is imposed. -/
def SatisfiesFirstOrder (U V : Family) : Prop :=
  (∀ p, (U p).conjTranspose * V p + (V p).conjTranspose * U p = 0) ∧
  (∀ p, Matrix.trace ((U p).conjTranspose * V p) = 0) ∧
  (∀ p q, p ≠ q →
    Matrix.trace ((V p).conjTranspose * U q + (U p).conjTranspose * V q) = 0)

/-- Indices where the cubed phase equals one. -/
abbrev ResonantIndex (d : PhaseTriple) := {j : Index // d.val j ^ 3 = 1}

/-- The number of resonant phase indices. -/
def resonanceCount (d : PhaseTriple) : ℕ := by
  classical
  exact Fintype.card (ResonantIndex d)

/-- Six real modes, six complex modes, and one complex mode per resonance. -/
abbrev NormalForm (d : PhaseTriple) :=
  (Fin 6 → ℝ) × (Fin 6 → ℂ) × (ResonantIndex d → ℂ)

end UnitaryErrorBases

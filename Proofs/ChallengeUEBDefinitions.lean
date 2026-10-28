module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-
# Shared unitary-error-basis definitions

Exact first-party source extraction from experimental/challenge/
ChallengeInterfaceProbe.lean, SHA256
291001bd5d684d2c84054a2bad0e2d1aa59ff672787c9ba2e9fa90eb2ce03c0c:
physical lines 49–56 and 81–88, including their documentation. The six
fully qualified declaration names, types and bodies are unchanged. The
public/expose module packaging is recorded separately from byte parity.

This module defines these shared globals once in the proof import graph.
A standalone statement must reproduce their exact definitions without importing
a second declaration of the same names. No analytic, residual, derivative
or dimension definition is extracted.

The four imports below are dependencies of the original source and pinned
mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55:
https://github.com/leanprover-community/mathlib4. Their source and Apache-2.0
notices remain unchanged. No mathlib proof body is copied, and no release
license is assigned to first-party contributions. Thanks to the Lean and
mathlib contributors for the matrix and modular-index interfaces.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/


@[expose] public section
noncomputable section

namespace UnitaryErrorBases

-- BEGIN EXACT PROBE LINES 49–56
/-- Cyclic row, column and phase index of order three. -/
abbrev Index := ZMod 3
/-- Complex three-by-three matrices. -/
abbrev Mat := Matrix Index Index ℂ
/-- The nine ordered matrix labels, with clock index first. -/
abbrev Label := Index × Index
/-- An unrestricted labelled family of nine complex matrices. -/
abbrev Family := Label → Mat
-- END EXACT PROBE LINES 49–56

-- BEGIN EXACT PROBE LINES 81–88
/-- A unitary matrix of determinant one. -/
def IsSpecialUnitary (U : Mat) : Prop :=
  U.conjTranspose * U = 1 ∧ U.det = 1

/-- Nine determinant-one unitaries orthogonal for the trace pairing. -/
def IsUnitaryErrorBasis (U : Family) : Prop :=
  (∀ p, IsSpecialUnitary (U p)) ∧
  ∀ p q, p ≠ q → Matrix.trace ((U p).conjTranspose * U q) = 0
-- END EXACT PROBE LINES 81–88

end UnitaryErrorBases

/- Declaration types and axiom dependencies of the six extracted definitions. -/


#check @UnitaryErrorBases.Index
#print axioms UnitaryErrorBases.Index
#check @UnitaryErrorBases.Mat
#print axioms UnitaryErrorBases.Mat
#check @UnitaryErrorBases.Label
#print axioms UnitaryErrorBases.Label
#check @UnitaryErrorBases.Family
#print axioms UnitaryErrorBases.Family
#check @UnitaryErrorBases.IsSpecialUnitary
#print axioms UnitaryErrorBases.IsSpecialUnitary
#check @UnitaryErrorBases.IsUnitaryErrorBasis
#print axioms UnitaryErrorBases.IsUnitaryErrorBasis

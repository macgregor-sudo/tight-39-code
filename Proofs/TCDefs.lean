module

public import NativeTrialityReuseInnerDerivation
public import NativeComplementaryConstruction
public import CodeFramePartition

@[expose] public section

/-!
# Tight codes and shared native definitions

Definitions only. Everything is stated on the compact `Glennie.Albert` with its own
`Glennie.jordan`, `Glennie.trace` (unnormalized: `trace 1 = 3`), `Glennie.inner x y =
trace (jordan x y)`, unit `1` and `Glennie.Frame`. A pure point is exactly a Jordan idempotent of
trace one; no quartet, unitary parametrization or phase restriction is imposed.

The only topology used is the product topology on the 27 native upper coordinates
`NativePolynomial.upperCoordinates` (`upperCoordinateEquiv : Albert ≃ₗ[ℝ] (Fin 27 → ℝ)`), taken
pointwise on labelled 39-point configurations. No topology or norm is put on `Glennie.Albert`.
-/

noncomputable section

namespace CKM.NativeTightCode

open Glennie

/-- A native pure point: `p ∘ p = p` and `trace p = 1`. -/
def IsPure (p : Albert) : Prop := jordan p p = p ∧ trace p = 1

/-- The distinct-pair overlap bound: `⟨P i, P j⟩ ≤ 1/3` whenever `i ≠ j`. -/
def OverlapBound {N : ℕ} (P : Fin N → Albert) : Prop :=
  ∀ i j, i ≠ j → inner (P i) (P j) ≤ (1 / 3 : ℝ)

/-- The (uncentered) native Gram matrix `G i j = ⟨P i, P j⟩`. -/
def gram {N : ℕ} (P : Fin N → Albert) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => inner (P i) (P j)

/-- The centered point `p - (1/3) • 1` (traceless when `trace p = 1`). -/
def centered (p : Albert) : Albert := p - (1 / 3 : ℝ) • (1 : Albert)

/-- The centered Gram matrix `H i j = ⟨P i - 1/3, P j - 1/3⟩`. -/
def centeredGram {N : ℕ} (P : Fin N → Albert) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => inner (centered (P i)) (centered (P j))

/-- The chordal distance `ρ(p, q) = sqrt (⟨p - q, p - q⟩ / 2)` (Cohn–Kumar–Minton §2.1
normalization), built from the native trace pairing — not from any coordinate norm. -/
def chordalDist (p q : Albert) : ℝ := Real.sqrt (inner (p - q) (p - q) / 2)

/-- Labelled 39-point configurations in the 27 native upper coordinates. -/
abbrev CodeCoords := Fin 39 → Fin 27 → ℝ

/-- The native point with coordinates `C i`. -/
def codePoint (C : CodeCoords) (i : Fin 39) : Albert :=
  NativePolynomial.upperCoordinateEquiv.symm (C i)

/-- The coordinates of a labelled native configuration. -/
def codeCoords (P : Fin 39 → Albert) : CodeCoords :=
  fun i => NativePolynomial.upperCoordinates (P i)

/-- The locus of labelled 39-point pure codes satisfying the overlap bound. -/
def tightLocus : Set CodeCoords :=
  {C | (∀ i, IsPure (codePoint C i)) ∧ OverlapBound (codePoint C)}

/-- The labelled partition relation: equal labels, or zero overlap. -/
def zeroRel (C : CodeCoords) (i j : Fin 39) : Prop :=
  i = j ∨ inner (codePoint C i) (codePoint C j) = 0

end CKM.NativeTightCode

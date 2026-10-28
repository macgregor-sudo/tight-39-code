module

public import MonoSound
public import QuadricRelations

@[expose] public section

/-!
# A6 compact route — statement D7 (lane STEP67), fixed by INTEG

Mathlib-light closure (base `MonoSound` + `QuadricRelations` only). Lane STEP67 proves `step67_bound : StmtD7`
(namespace `A6Compact`), importing this file (never `A6Interface`). `ChainMid.quadricRelations` is the ONE definition
(MONO's former copy `Mono.quadricRelations` is gone from the base; `MonoSound.finrank_le_card` is stated with it).
-/

open MvPolynomial Module

namespace A6Compact

/-- (D7) the Hilbert function of `F[y₁..y₂₄]/(t)` is at most `4·C(m+5,5) + 1540·C(m+4,4)` in every degree. -/
abbrev StmtD7 : Prop :=
  ∀ m, finrank F (homogeneousSubmodule (Fin 24) F m ⧸ ChainMid.quadricRelations MonoSound.t m) ≤
    4 * (m + 5).choose 5 + 1540 * (m + 4).choose 4

end A6Compact

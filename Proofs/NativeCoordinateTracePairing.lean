module

public import NativeCoordinateProductTrace

@[expose] public section

/-!
The original coordinate pairing is the actual native Albert trace pairing.
The order is diagonal0,1,2, then native upper01,02,12 in the existing eight
quaternion-pair components. Weights1 and2 are the already defined integral
trace weights. Neither cyclic coordinates nor a gauge change is inserted.

The proof combines the existing native trace/inner coordinate theorem with
the exact finite coordinate sum. It uses no idempotency, norm, frame, phase
or equation hypothesis. This elementary adapter makes no novelty claim.
First-party theorem composition; no upstream proof body copied. Inherited
Apache-2.0/native provenance remains in THIRD_PARTY_NOTICES.md#native-albert-code and
imports, https://github.com/macgregor-sudo/compact-albert-recognition at
40d3b344180d9ddb78aaa2876873377c1e631515. Lean4.35.0-rc2; mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55. Thanks to their contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke,1676. No release license is selected here.
-/

noncomputable section

namespace NativePolynomial.CoordinateMaps

/-- The existing weighted upper-coordinate sum is the original native product trace. -/
theorem coordinatePairing_upperCoordinates_eq_native_trace (x y : Glennie.Albert) :
    coordinatePairing (upperCoordinates x) (upperCoordinates y) =
      Glennie.trace (Glennie.jordan x y) := by
  change coordinatePairing (upperCoordinates x) (upperCoordinates y) = Glennie.inner x y
  rw [Glennie.inner_coordinates]
  norm_num [coordinatePairing, IntegralStructureConstants.coordinateTraceWeight,
    Fin.sum_univ_succ, upperCoordinates, Glennie.octDot_coordinates] <;> ring

end NativePolynomial.CoordinateMaps

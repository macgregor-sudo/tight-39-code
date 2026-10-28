module

public import NativeExactCKMConfiguration

/-!
Small source-only path test for the exact CKM shared frames0–3. It reuses
only the accepted native coordinate points and the unchanged original point
packing. The phase-family binder fixes the original outcome order before
any further frame proof. No cross-frame or solution assertion is made.
First-party proof; no third-party proof body copied. Imported native/mathlib
notices and pins remain in their source modules.
-/

@[expose] public section
noncomputable section

namespace QuadraticCertificate.ExactCKMSharedFrames

open CompactAlbert NativePolynomial
open NativePolynomial.ConfigurationResiduals
open UnitaryErrorBases.ComplexQuartet
open ExactCKMConfiguration

/-- The actual original points0,1,2 retain the coordinate outcome order. -/
theorem nativePoint_coordinate_eq_literal :
    (fun t : Fin 3 => nativePoint (framePointIndex 0 t)) =
      literalNativeCoordinatePoint := by
  funext t
  fin_cases t <;> rfl

/-- One native coordinate frame proof, using the actual Jordan components. -/
theorem literalNativeCoordinate_frame : Glennie.Frame literalNativeCoordinatePoint := by
  constructor
  · intro i
    fin_cases i <;> norm_num [literalNativeCoordinatePoint, Glennie.trace]
  · intro i
    fin_cases i <;> apply Glennie.Albert.extExplicit <;>
      norm_num [literalNativeCoordinatePoint, Glennie.jordan_d0, Glennie.jordan_d1,
        Glennie.jordan_d2, Glennie.jordan_o01, Glennie.jordan_o02, Glennie.jordan_o12,
        Glennie.octDot, Glennie.octMul, Glennie.octConj, Glennie.octRe]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> try contradiction
    all_goals apply Glennie.Albert.extExplicit <;>
      norm_num [literalNativeCoordinatePoint, Glennie.jordan_d0, Glennie.jordan_d1,
        Glennie.jordan_d2, Glennie.jordan_o01, Glennie.jordan_o02, Glennie.jordan_o12,
        Glennie.octDot, Glennie.octMul, Glennie.octConj, Glennie.octRe]
  · apply Glennie.Albert.extExplicit <;> norm_num [literalNativeCoordinatePoint]

/-- Exact shared configuration frame0, with no other-frame premise. -/
theorem nativePoint_coordinate_frame :
    Glennie.Frame (fun t : Fin 3 => nativePoint (framePointIndex 0 t)) := by
  rw [nativePoint_coordinate_eq_literal]
  exact literalNativeCoordinate_frame

/-- Original frames1+s have phase label s and unchanged outcome t. -/
def sharedPhaseFrameLabel (s : Fin 3) : Fin 13 := ⟨1 + s.val, by omega⟩

theorem nativePoint_phase_eq_literal (s : Fin 3) :
    (fun t : Fin 3 => nativePoint (framePointIndex (sharedPhaseFrameLabel s) t)) =
      (fun t : Fin 3 => literalNativePhasePoint (s.val : PhaseIndex) (t.val : PhaseIndex)) := by
  funext t
  fin_cases s <;> fin_cases t <;> rfl

end QuadraticCertificate.ExactCKMSharedFrames

#print axioms QuadraticCertificate.ExactCKMSharedFrames.nativePoint_coordinate_frame
#print axioms QuadraticCertificate.ExactCKMSharedFrames.nativePoint_phase_eq_literal

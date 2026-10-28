module

public import NativeRightSU3Action
public import NativeActualStateEquivalence

@[expose] public section

/-!
Actual existence of the common-right SU(3) action fixing original anchors0–11.
The already accepted NativeRightSU3Action faithfully adapts the pinned native
sector-left construction: M↦hM with B=M† gives B↦Bh†; it takes h=R† and exposes
the actual action B↦BR directly. This module reuses that construction, product
proof and real-linear equivalence; only the actual-label binding is new.
No alternate native carrier, automorphism, trace/metric premise or framework.
Inherited Apache-2.0 source attribution and notices remain in that owner.
Thanks to its native-model, Lean and Mathlib contributors. “If I have seen further
it is by standing on the sholders of Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
namespace CompactAlbert
open ActualQuartetStates
open QuadraticCertificate.ExactCKMConfiguration
open QuadraticCertificate.ExactCKMSharedFrames

private theorem right_multiply_fixes_actual_anchors (R : TitsComplexMatrix)
    (i : Fin 39) (hi : i.val < 12) :
    nativeRightMultiply R (nativePoint i) = nativePoint i := by
  rcases (actual_anchor_labels i).mp hi with ⟨t, rfl⟩ | ⟨s, t, rfl⟩
  · rw [congrFun nativePoint_coordinate_eq_literal t,
      literalNativeCoordinatePoint_eq_included]
    exact nativeRightMultiply_includeHermitianMatrix R _
  · rw [congrFun (nativePoint_phase_eq_literal s) t,
      literalNativePhasePoint_eq_included]
    exact nativeRightMultiply_includeHermitianMatrix R _

/-- Every determinant-one right unitary has an actual real-linear native Jordan
automorphism fixing the original twelve canonical labels, with the displayed
right action on every native matrix pair. This is existence, not topology. -/
theorem native_anchor_fixer_converse (R : TitsComplexMatrix)
    (hR : R * R.conjTranspose = (1 : TitsComplexMatrix)) (hdet : R.det = 1) :
    ∃ f : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert,
      (∀ x y : Glennie.Albert,
        f (Glennie.jordan x y) = Glennie.jordan (f x) (f y)) ∧
      (∀ i : Fin 39, i.val < 12 → f (nativePoint i) = nativePoint i) ∧
      ∀ x : Glennie.Albert,
        nativeTitsMatrixPair (f x) =
          ((nativeTitsMatrixPair x).1, (nativeTitsMatrixPair x).2 * R) := by
  refine ⟨nativeRightSU3Equiv R hR hdet, ?_, ?_, ?_⟩
  · exact nativeRightMultiply_jordan R hR hdet
  · exact right_multiply_fixes_actual_anchors R
  · exact nativeRightMultiply_pair R

end CompactAlbert

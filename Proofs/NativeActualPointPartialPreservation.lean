module

public import NativeCanonicalPartialPreservation
public import NativeExactCKMAllF

@[expose] public section

/-!
# Partial-action preservation at the literal exact real CKM point

The configuration below is the upper-coordinate view of the EXISTING
ExactCKMConfiguration.nativePoint, with its retained exact rational phases
(3+4i)/5, (5+12i)/13, (15+8i)/17, (21+20i)/29 and original grouped labels.
The accepted pointValues theorem proves equality of its point-first packing
with the accepted pointCoordinates. The accepted shared-frame and literal
binder equalities discharge all twelve canonical anchors. The accepted all-F
theorem supplies the original input equations; none is a caller premise.

The main endpoint therefore assumes only VVᴴ=I and det V=1. It preserves
every one of the SAME2184 real native residuals at h=1/2,t=1/3. No equality
to the separately named complex PointBridge.P is imported or claimed. This
is not the unphased code, an orbit/dimension statement or an exhaustion result.

First-party composition of accepted declarations, with no copied upstream
implementation or new scientific premise. Native source attribution,
Apache-2.0 notices and mathlib pins remain in the unchanged imported owners.
The actual-point import must use the independently admitted coherent cold
source/object closure; no standalone native wrapper is co-imported here.
Thanks to the CKM construction, native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace NativePolynomial.PartialAction.Actual

open CompactAlbert ConfigurationResiduals ConfigurationResidualIndices
open ConfigurationResiduals.MixedCoefficients
open QuadraticCertificate QuadraticCertificate.ExactCKMConfiguration

/-- The existing literal real native point, in its existing upper coordinates. -/
def actualConfiguration (i : Fin 39) : NativeVector ℝ :=
  upperCoordinates (nativePoint i)

/-- Exact equality with the accepted point-value view, rather than a new point. -/
theorem actualConfiguration_eq_pointValues (i : Fin 39) :
    actualConfiguration i = pointValues pointCoordinates i :=
  (pointValues_pointCoordinates i).symm

/-- The accepted1053 coordinates use precisely the original point-first pack. -/
theorem pack_actualConfiguration : pack actualConfiguration = pointCoordinates := by
  funext v
  obtain ⟨ik, hik⟩ := (finProdFinEquiv : Fin 39 × Fin 27 ≃ Fin 1053).surjective v
  rcases ik with ⟨i, k⟩
  have hIndex : variableIndex i k = v := by
    rw [← hik]
    apply Fin.ext
    change 27 * i.val + k.val = k.val + 27 * i.val
    omega
  rw [← hIndex, pack_variableIndex]
  exact (congrFun (pointValues_pointCoordinates i) k).symm

/-- The exact grouped first12 labels are the actual included complex quartet. -/
theorem actual_canonical_anchors : CanonicalAnchors actualConfiguration where
  coordinate a := by
    change fromUpperCoordinates (upperCoordinates (nativePoint (framePointIndex 0 a))) = _
    rw [fromUpperCoordinates_upperCoordinates,
      congrFun ExactCKMSharedFrames.nativePoint_coordinate_eq_literal a,
      literalNativeCoordinatePoint_eq_included]
  phase s a := by
    change fromUpperCoordinates (upperCoordinates
      (nativePoint (framePointIndex (canonicalPhaseFrame s) a))) = _
    rw [fromUpperCoordinates_upperCoordinates]
    change nativePoint (framePointIndex (ExactCKMSharedFrames.sharedPhaseFrameLabel s) a) = _
    rw [congrFun (ExactCKMSharedFrames.nativePoint_phase_eq_literal s) a,
      literalNativePhasePoint_eq_included]

/-- Every original input row is supplied by the accepted literal-point theorem. -/
theorem actual_input_all_fRows (r : Fin 2184) :
    MvPolynomial.eval (pack actualConfiguration)
      (ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r) = 0 := by
  rw [pack_actualConfiguration]
  exact ExactCKMAllF.all_fRow_eval_zero r

/-- Transform the existing native point itself, then take its upper coordinates. -/
def transformedConfiguration (V : TitsComplexMatrix) (i : Fin 39) : NativeVector ℝ :=
  upperCoordinates (nativePartialLeft V (nativePoint i))

theorem transformedConfiguration_eq_coordinate_action (V : TitsComplexMatrix) :
    transformedConfiguration V = fun i => coordinatePartialLeft V (actualConfiguration i) := by
  funext i
  simp only [transformedConfiguration, actualConfiguration, coordinatePartialLeft_apply,
    fromUpperCoordinates_upperCoordinates]

/-- The actual twelve anchor values are fixed; no unitary premise is needed. -/
theorem actual_anchors_fixed (V : TitsComplexMatrix) (i : Fin 39) (hi : i.val < 12) :
    transformedConfiguration V i = actualConfiguration i := by
  rw [transformedConfiguration_eq_coordinate_action]
  exact canonical_anchors_fixed actual_canonical_anchors V i hi

theorem actual_native_anchors_fixed (V : TitsComplexMatrix) (i : Fin 39) (hi : i.val < 12) :
    nativePartialLeft V (nativePoint i) = nativePoint i := by
  apply upperCoordinateEquiv.injective
  exact actual_anchors_fixed V i hi

/-- Every SAME original numbered real residual vanishes after the canonical
partial action at the accepted exact rational-phase native configuration.
Only the two special-unitary matrix conditions are caller hypotheses. -/
theorem actual_all_fRows_partial_left (V : TitsComplexMatrix)
    (hV : V * V.conjTranspose = (1 : TitsComplexMatrix)) (hd : V.det = 1) :
    ∀ r : Fin 2184, MvPolynomial.eval (pack (transformedConfiguration V))
      (ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r) = 0 := by
  rw [transformedConfiguration_eq_coordinate_action]
  exact all_fRows_canonical_partial_left actual_input_all_fRows actual_canonical_anchors V hV hd

end NativePolynomial.PartialAction.Actual

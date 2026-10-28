module

public import PointShape
public import NativeExactCKMConfiguration

/-!
# The accepted real CKM point equals the ring-generic shape at real constants

`nativePoint_shape`: `upperCoordinates (nativePoint i) = shape realConsts i`,
proved once per point TYPE (coordinate anchor; the generic native outer
product; octonion product/conjugate/norm in coordinates), with no case split
over the 39 points. `complex_coords` then complexifies by `shape_map`.

First-party composition over the accepted definitions; no borrowed text.
-/

@[expose] public section
noncomputable section

namespace FourSheets.PointStructure

open FourSheets.PointShape NativePolynomial CompactAlbert
open QuadraticCertificate.ExactCKMConfiguration
open UnitaryErrorBases.ComplexQuartet UnitaryErrorBases.ThreeCycleFourier

/-- Native octonion coordinates in `upperCoordinates` order. -/
def octCoords (x : Glennie.Octonion) : Fin 8 → ℝ :=
  ![x.1.re, x.1.imI, x.1.imJ, x.1.imK, x.2.re, x.2.imI, x.2.imJ, x.2.imK]

theorem octCoords_mul (x y : Glennie.Octonion) :
    octCoords (Glennie.octMul x y) = omul (octCoords x) (octCoords y) := by
  funext k
  fin_cases k <;>
    simp [octCoords, omul, join, qmul, qstar, lo, hi, Glennie.octMul]

theorem octCoords_conj (x : Glennie.Octonion) :
    octCoords (Glennie.octConj x) = oconj (octCoords x) := by
  funext k
  fin_cases k <;> simp [octCoords, oconj, join, qstar, lo, hi, Glennie.octConj]

theorem octNormSq_eq (x : Glennie.Octonion) :
    Glennie.octNormSq x = onormSq (octCoords x) := by
  simp [Glennie.octNormSq, Quaternion.normSq_def', onormSq, octCoords]
  ring

theorem octCoords_smul (r : ℝ) (x : Glennie.Octonion) (j : Fin 8) :
    octCoords (r • x) j = r * octCoords x j := by
  fin_cases j <;> simp [octCoords]

/-- One generic lemma for every outer-product point. -/
theorem upper_outer (u w : Glennie.Octonion) :
    upperCoordinates (nativeOuterProductThird u w) =
      outerVec (1/3) (octCoords u) (octCoords w) := by
  have h1 := octCoords_conj u
  have h2 := octCoords_conj w
  have h3 := octCoords_mul u (Glennie.octConj w)
  rw [h2] at h3
  funext k
  simp only [outerVec]
  rw [← h3, ← h1, ← h2, ← octNormSq_eq, ← octNormSq_eq]
  fin_cases k <;> simp [upperCoordinates, nativeOuterProductThird, octCoords] <;> ring

theorem upper_coordinatePoint (t : Fin 3) :
    upperCoordinates (literalNativeCoordinatePoint t) = coordVec t := by
  funext k
  fin_cases t <;> fin_cases k <;>
    simp [upperCoordinates, literalNativeCoordinatePoint, coordVec]

theorem octCoords_complex (z : ℂ) :
    octCoords (complexOctonion z) = zvec z.re z.im := by
  funext j
  fin_cases j <;> simp [octCoords, complexOctonion, zvec]

theorem octCoords_basis (b : Fin 8) :
    octCoords (nativeOctonionBasis b) = basisVec b := by
  funext j
  fin_cases b <;> fin_cases j <;>
    simp [octCoords, nativeOctonionBasis, nativeCoordinateBasis, fromUpperCoordinates,
      firstUpperCoordinateIndex, basisVec]

/-- The real scalar inputs of the accepted point. -/
def realConsts : Consts ℝ :=
  ⟨1/3, fun r => (character r).re, fun r => (character r).im,
    fun p => (exactPhases p).re, fun p => (exactPhases p).im⟩

theorem charVec_real (r : ZMod 3) :
    charVec realConsts r = octCoords (complexOctonion (character r)) := by
  rw [octCoords_complex]; rfl

theorem phasedVec_real (p : Fin 4) (r : ZMod 3) :
    phasedVec realConsts p r = octCoords (complexOctonion (exactPhases p * character r)) := by
  rw [octCoords_complex, Complex.mul_re, Complex.mul_im]; rfl

theorem family_shape (q : Fin 4) (s t : PhaseIndex) :
    upperCoordinates (nativeFamilyPoint q s t) = familyShape realConsts q s t := by
  unfold nativeFamilyPoint familyShape literalNativePhasePoint literalNativeRawComplexPoint
  split_ifs <;>
    simp only [upper_outer, octCoords_mul, octCoords_basis, charVec_real, phasedVec_real] <;> rfl

/-- The accepted point, all 39 points at once, equals the generic shape. -/
theorem nativePoint_shape (i : Fin 39) :
    upperCoordinates (nativePoint i) = shape realConsts i := by
  unfold nativePoint shape
  split_ifs
  · exact upper_coordinatePoint _
  · exact family_shape _ _ _

/-- Complexified coordinates of the accepted point. -/
theorem complex_coords (i : Fin 39) (k : Fin 27) :
    ((upperCoordinates (nativePoint i) k : ℝ) : ℂ) =
      shape (realConsts.map Complex.ofRealHom) i k := by
  rw [nativePoint_shape]
  exact shape_map Complex.ofRealHom realConsts i k

end FourSheets.PointStructure

#print axioms FourSheets.PointStructure.nativePoint_shape
#print axioms FourSheets.PointStructure.complex_coords

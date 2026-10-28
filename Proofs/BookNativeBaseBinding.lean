module

public import BookNativeBaseData
public import NativeStressConsumer

/-!
Exact equality between the independently transcribed Book D1 base and the
existing real native seed. The accepted P_literal theorem fixes the field map
and original packing; pack_actualConfiguration identifies the existing seed.
The original2184-row solution is reused only after proving this exact equality.
No D1 comparison, seed equation, tangent identity or stress premise is assumed.
First-party composition. Imported source attribution and license notices remain
with the unchanged modules; this file copies no upstream implementation.
-/

@[expose] public section
noncomputable section

namespace Option2.BookNativeBase

open Option2.NativeStress
open QuadraticCertificate.ExactCKMConfiguration

/-- The literal Book base interpreted in the original real1053-coordinate space. -/
def bookBase : NativeAmbient := fun v => (Q12.toComplex (bookQ12 v)).re

/-- All original1053 complex coordinates agree, retaining Q12.toComplex. -/
theorem bookComplex_eq_pointCoordinates (v : Fin 1053) :
    Q12.toComplex (bookQ12 v) = ((pointCoordinates v : ℝ) : ℂ) := by
  simpa only [bookQ12, bookPointQ12_eq] using
    (congrFun FourSheets.PointQ12.P_literal v).symm

/-- Realness follows from the accepted literal point bridge, not D1 metadata. -/
theorem bookBase_complex (v : Fin 1053) :
    (bookBase v : ℂ) = Q12.toComplex (bookQ12 v) := by
  rw [bookBase, bookComplex_eq_pointCoordinates]
  simp only [Complex.ofReal_re]

theorem bookBase_eq_pointCoordinates : bookBase = pointCoordinates := by
  funext v
  exact congrArg Complex.re (bookComplex_eq_pointCoordinates v)

/-- Exact source-bound Book base = the existing accepted native seed. -/
theorem bookBase_eq_originalSeed : bookBase = originalSeed := by
  rw [bookBase_eq_pointCoordinates, originalSeed,
    NativePolynomial.PartialAction.Actual.pack_actualConfiguration]

/-- Every original residual at h=1/2,t=1/3 vanishes at the literal Book base. -/
theorem bookBase_originalF_zero (r : Fin 2184) : originalF bookBase r = 0 := by
  rw [bookBase_eq_originalSeed]
  exact seed_residual_zero r

theorem originalF_bookBase : originalF bookBase = 0 := by
  funext r
  exact bookBase_originalF_zero r

end Option2.BookNativeBase

#print axioms Option2.BookNativeBase.bookBase_eq_originalSeed
#print axioms Option2.BookNativeBase.bookBase_originalF_zero
#print axioms Option2.BookNativeBase.originalF_bookBase

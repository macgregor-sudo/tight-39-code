module

public import HTPhaseCompleteKernel

@[expose] public section

/-!
# Seed normalization of the phase equivalence

At the accepted seed `exactPhases` the phase-native construction reproduces the accepted fixed-seed objects:
`normalProjXi exactPhases = normalProjection` (same construction), the projected phase direction equals the
projected accepted `realV` (via the accepted D6/axis binding `projectedBook_axis`), and the good-phase
equivalence `bookPhaseEquiv exactPhases_good` IS the accepted `bookNormalKernelEquiv`.
This fixes the Book normalization of the phase blocks at the seed by the accepted data, not by a dimension count.
-/

set_option Elab.async false
noncomputable section

namespace Option2.NativeStress.HTPhaseComplete

open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open Option2.NativeStress.BookHT
open Option2.NativeStress.BookHT.TangentCoordinates (realV)
open Option2.NativeStress.BookHT.NativeNormalKernelBridge
  (exactPhases_good normalProjection bookDirection bookDirection_apply projectedBook_axis
    projectedSimultaneousFamily bookNormalKernelEquiv bookNormalKernelEquiv_apply unpackNative)
open QuadraticCertificate.ExactCKMConfiguration (exactPhases)
open Option2.NativeStress.BookHT.TangentCoordinates (exactPhases_unit)

theorem normalProjXi_exactPhases :
    normalProjXi exactPhases exactPhases_unit = normalProjection := rfl

/-- At the seed, the projected phase direction is the projected accepted Book `realV`. -/
theorem normalProj_familyDirection_seed (z : Blocks) :
    normalProjXi exactPhases exactPhases_unit (familyDirection exactPhases exactPhases_unit z) =
      normalProjection (unpackNative (realV z)) := by
  have hz : z = ∑ H : Fin 4, Pi.single H (z H) := (Finset.univ_sum_single z).symm
  rw [← bookDirection_apply, hz, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [familyDirection_single, ← projSimFam_apply, projectedBook_axis]
  rfl

/-- **Seed normalization**: the phase equivalence at the seed is the accepted fixed-seed equivalence. -/
theorem bookPhaseEquiv_exactPhases :
    bookPhaseEquiv exactPhases_good = bookNormalKernelEquiv := by
  apply ContinuousLinearEquiv.ext
  funext p
  apply Subtype.ext
  rw [bookPhaseEquiv_apply, bookNormalKernelEquiv_apply, unpack_phaseV,
    normalProj_familyDirection_seed]

end Option2.NativeStress.HTPhaseComplete

#print axioms Option2.NativeStress.HTPhaseComplete.normalProjXi_exactPhases
#print axioms Option2.NativeStress.HTPhaseComplete.normalProj_familyDirection_seed
#print axioms Option2.NativeStress.HTPhaseComplete.bookPhaseEquiv_exactPhases

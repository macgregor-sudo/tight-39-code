module

public import NativeExactCKMSharedPhaseFrames
public import NativeExactCKMCDFrames

/-!
# All thirteen original CKM frames

This is a finite dispatch over the original frame labels. The frame identities
come from the separately checked shared, q1, q2, and q3 native constructions;
no cross-frame equation or full code solution is asserted here.
-/

@[expose] public section
noncomputable section

namespace QuadraticCertificate.ExactCKMAllFrames

open CompactAlbert NativePolynomial
open NativePolynomial.ConfigurationResiduals
open QuadraticCertificate.ExactCKMConfiguration

/-- Every original labelled triple is a Jordan frame in its original point order. -/
theorem nativePoint_all_frames (f : Fin 13) :
    Glennie.Frame (fun t : Fin 3 => nativePoint (framePointIndex f t)) := by
  fin_cases f
  · simpa [ExactCKMSharedFrames.sharedFrameLabel] using
      ExactCKMSharedFrames.nativePoint_shared_frames (0 : Fin 4)
  · simpa [ExactCKMSharedFrames.sharedFrameLabel] using
      ExactCKMSharedFrames.nativePoint_shared_frames (1 : Fin 4)
  · simpa [ExactCKMSharedFrames.sharedFrameLabel] using
      ExactCKMSharedFrames.nativePoint_shared_frames (2 : Fin 4)
  · simpa [ExactCKMSharedFrames.sharedFrameLabel] using
      ExactCKMSharedFrames.nativePoint_shared_frames (3 : Fin 4)
  · simpa [ExactCKMThreeHiddenFrames.qOneFrameLabel] using
      ExactCKMThreeHiddenFrames.nativePoint_qOne_frames (0 : Fin 3)
  · simpa [ExactCKMThreeHiddenFrames.qOneFrameLabel] using
      ExactCKMThreeHiddenFrames.nativePoint_qOne_frames (1 : Fin 3)
  · simpa [ExactCKMThreeHiddenFrames.qOneFrameLabel] using
      ExactCKMThreeHiddenFrames.nativePoint_qOne_frames (2 : Fin 3)
  · simpa [ExactCKMABFrames.qTwoFrameLabel] using
      ExactCKMABFrames.nativePoint_qTwo_frames (0 : Fin 3)
  · simpa [ExactCKMABFrames.qTwoFrameLabel] using
      ExactCKMABFrames.nativePoint_qTwo_frames (1 : Fin 3)
  · simpa [ExactCKMABFrames.qTwoFrameLabel] using
      ExactCKMABFrames.nativePoint_qTwo_frames (2 : Fin 3)
  · simpa [ExactCKMCDFrames.qThreeFrameLabel] using
      ExactCKMCDFrames.nativePoint_qThree_frames (0 : Fin 3)
  · simpa [ExactCKMCDFrames.qThreeFrameLabel] using
      ExactCKMCDFrames.nativePoint_qThree_frames (1 : Fin 3)
  · simpa [ExactCKMCDFrames.qThreeFrameLabel] using
      ExactCKMCDFrames.nativePoint_qThree_frames (2 : Fin 3)

end QuadraticCertificate.ExactCKMAllFrames

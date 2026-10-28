module

public import EFLiteral
public import NativeOrbitErrorTransfer

@[expose] public section

/-!
Canonical cross-overlap domains in the actual native configuration topology.
The imported native and exact-frame sources retain their provenance and notices.
No exact-frame, freeness, uniform-phase radius, or energy hypothesis is needed.
-/
set_option Elab.async false
noncomputable section
namespace CKM.NativeOverlapLossHook
open NativePolynomial NativeFirstOrder NativeGroupSlice NativeTightCode
  NativeExactFrameEnergy NativeOrbitErrorTransfer SupportedStress.NativeFrames

theorem cross_overlap_eq_coordinatePairing (C : Cfg) (k : ThirteenCrossPair) :
    thirteenCrossOverlap (framesOf literalLabel (codePoint C)) k =
      CoordinateMaps.coordinatePairing (C (literalLabel.symm (k.1.val.1, k.2.1)))
        (C (literalLabel.symm (k.1.val.2, k.2.2))) := by
  have h (i : Fin 39) : C i = upperCoordinates (codePoint C i) :=
    (upperCoordinateEquiv.apply_symm_apply (C i)).symm
  rw [h (literalLabel.symm (k.1.val.1, k.2.1)),
    h (literalLabel.symm (k.1.val.2, k.2.2)),
    CoordinateMaps.coordinatePairing_upperCoordinates_eq_native_trace]
  rfl

theorem continuous_cross_overlap (k : ThirteenCrossPair) :
    Continuous (fun C : Cfg => thirteenCrossOverlap
      (framesOf literalLabel (codePoint C)) k) := by
  simp_rw [cross_overlap_eq_coordinatePairing]
  unfold CoordinateMaps.coordinatePairing
  fun_prop

theorem cross_overlap_actC {A : CEnd} (hA : A ∈ autC)
    (C : Cfg) (k : ThirteenCrossPair) :
    thirteenCrossOverlap (framesOf literalLabel (codePoint (actC A C))) k =
      thirteenCrossOverlap (framesOf literalLabel (codePoint C)) k := by
  simp only [cross_overlap_eq_coordinatePairing, actC_apply, autC_pairing hA]

theorem cross_overlap_literal (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (k : ThirteenCrossPair) :
    thirteenCrossOverlap (framesOf literalLabel (codePoint (literalCfg ξ))) k = 1/3 := by
  have hp : codePoint (literalCfg ξ) = literalPoint ξ := by
    funext i
    exact upperCoordinateEquiv.symm_apply_apply (literalPoint ξ i)
  rw [hp]
  exact literal_cross ξ hξ k

/-- One open domain contains the whole native orbit; every canonical cross
pair lies in the prescribed open set containing `1/3`. -/
theorem native_cross_overlap_neighborhood (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (U : Set ℝ) (hU : IsOpen U) (hbase : (1/3 : ℝ) ∈ U) :
    ∃ N : Set Cfg, IsOpen N ∧ nativeOrbit ξ ⊆ N ∧
      literalCfg ξ ∈ N ∧ ∀ C ∈ N, ∀ k : ThirteenCrossPair,
        thirteenCrossOverlap (framesOf literalLabel (codePoint C)) k ∈ U := by
  let N : Set Cfg := {C | ∀ k : ThirteenCrossPair,
    thirteenCrossOverlap (framesOf literalLabel (codePoint C)) k ∈ U}
  have ho : IsOpen N := by
    simpa only [N, Set.preimage, Set.iInter_setOf] using
      (isOpen_iInter_of_finite fun k => hU.preimage (continuous_cross_overlap k))
  have hp : literalCfg ξ ∈ N := by
    intro k
    rw [cross_overlap_literal ξ hξ k]
    exact hbase
  refine ⟨N, ho, ?_, hp, fun _ h => h⟩
  intro C hC
  obtain ⟨A, hA, P, hP, rfl⟩ := (mem_saturation _ _).mp hC
  have he : P = literalCfg ξ := hP
  subst P
  intro k
  rw [cross_overlap_actC hA]
  exact hp k

#print axioms native_cross_overlap_neighborhood
end CKM.NativeOverlapLossHook

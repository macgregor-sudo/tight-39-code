module

public import BookNativeSheetFamilies
public import NativeHFixedBaseConsumer

@[expose] public section

/-! Compatibility of native family and anchor constructions.
The original native quartet labels agree with the fixed-anchor stress selector. -/
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Option2.NativeStress.BookHT.SheetHStress
open CKM.NativeFirstOrder CKM.NativeFourFamily CKM.NativeGroupSlice
open SheetReduction TangentCoordinates NativeNormalKernelBridge
open NativePolynomial QuadraticCertificate.ExactCKMConfiguration
open AnchorSupport AnchorRowSupport AnalyticDerivative PolynomialJets
open scoped BigOperators

theorem anchorRelabel_symm_lt (H : Fin 4) (p : Fin 39) (hp : AnchorPoint H p) :
    ((anchorRelabel H).symm p).val < 12 := by
  revert hp p H
  unfold AnchorPoint
  decide +kernel

theorem preCfg_anchor_point (H : Fin 4) (g h : UnitaryErrorBases.Mat)
    (d : UnitaryErrorBases.PhaseTriple) (p : Fin 39) (hp : AnchorPoint H p) :
    preCfg exactPhases H g h d p = literalCfg exactPhases p := by
  rw [← preCfg_base exactPhases_unit H]
  change upperCoordinates (prePoint exactPhases H g h d p) =
    upperCoordinates (prePoint exactPhases H 1 1 (anchorTriple exactPhases exactPhases_unit H) p)
  unfold prePoint
  rw [stdAnchored, dif_pos (anchorRelabel_symm_lt H p hp),
    stdAnchored, dif_pos (anchorRelabel_symm_lt H p hp)]

/-- Every actual fixed-anchor coordinate is preserved, with no phase or tangent surrogate. -/
theorem preMap_anchor_coordinate (H : Fin 4) (p : PreParam) (v : Fin 1053)
    (hv : AnchorCoordinate H v) :
    PartialAction.pack (preMap exactPhases exactPhases_unit H p) v =
      PartialAction.pack (literalCfg exactPhases) v := by
  have hp : AnchorPoint H (Fin.divNat (n := 27) v) := by
    change v.val / 27 / 3 = 0 ∨
      (1 + 3 * H.val ≤ v.val / 27 / 3 ∧ v.val / 27 / 3 ≤ 3 + 3 * H.val)
    simpa only [AnchorCoordinate, Nat.div_div_eq_div_mul] using hv
  exact congrFun (preCfg_anchor_point H _ _ _ (Fin.divNat (n := 27) v) hp)
    (Fin.modNat (m := 39) v)

/-- The actual supplied H covector kills the full original derivative along the raw family. -/
theorem raw_component_annihilates (H : Fin 4) (a : Fin 3) (p : PreParam) :
    (stressCovector (NativeH.weightC H a)).comp
      (fderiv ℝ AnalyticDerivative.originalF (preMap exactPhases exactPhases_unit H p)) = 0 := by
  apply stress_comp_fderiv_originalF_eq_zero (literalCfg exactPhases)
    (preMap exactPhases exactPhases_unit H p) (NativeH.weightC H a) H
  · intro r
    exact congrFun (originalF_literalCfg exactPhases exactPhases_unit) r
  · intro c
    change (∑ r : Fin 2184, NativeH.weightC H a r * equationLinearMatrix
      (translatedRow (fun v => ((PartialAction.pack (literalCfg exactPhases) v : ℝ) : ℂ))) r c) = 0
    rw [TangentCoordinates.pack_literalCfg_exactPhases]
    exact NativeH.Equilibrium.book_h_equilibrium H a c
  · exact NativeH.hasAnchorSupport _ H a
  · exact preMap_anchor_coordinate H p

end Option2.NativeStress.BookHT.SheetHStress

module

public import BookNativeReducedQuadraticTransfer
public import NativeHFixedBaseConsumer
public import NativeTEquilibriumEndpoint

@[expose] public section

/-! Literal H/T row covectors, actual equilibrium, and an exact reproduction-only assembly boundary. -/
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Option2.NativeStress.BookHT.ReducedQuadratic
open SheetReduction NativeNormalKernelBridge TangentCoordinates
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeSliceImplicitReduction
open NativePolynomial QuadraticCertificate.ExactCKMConfiguration
open AnalyticDerivative PolynomialJets AnchorSupport
open scoped BigOperators

/-- The same twelve T contractions as residualT, now with their real continuous-linear interface. -/
def selectedT : Residual →L[ℝ] Blocks :=
  ContinuousLinearMap.pi fun i =>
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun a => stressCovector (NativeT.weightT i a))

theorem selectedT_apply (q : Residual) (i : Fin 4) (a : Fin 3) :
    selectedT q i a = ∑ r : Fin 2184, NativeT.weightT i a r * (q r : ℂ) :=
  stressCovector_apply (NativeT.weightT i a) q

theorem H_component_annihilates (i : Fin 4) (a : Fin 3) :
    (stressCovector (NativeH.weightC i a)).comp
      (fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases)) = 0 := by
  apply stress_comp_fderiv_originalF_eq_zero (literalCfg exactPhases) (literalCfg exactPhases)
    (NativeH.weightC i a) i
  · intro r
    exact congrFun (originalF_literalCfg exactPhases exactPhases_unit) r
  · intro c
    change (∑ r : Fin 2184, NativeH.weightC i a r * equationLinearMatrix
      (translatedRow (fun v => ((PartialAction.pack (literalCfg exactPhases) v : ℝ) : ℂ))) r c) = 0
    rw [TangentCoordinates.pack_literalCfg_exactPhases]
    exact NativeH.Equilibrium.book_h_equilibrium i a c
  · exact NativeH.hasAnchorSupport _ i a
  · intro v hv; rfl

theorem T_component_annihilates (i : Fin 4) (a : Fin 3) :
    (stressCovector (NativeT.weightT i a)).comp
      (fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases)) = 0 := by
  ext W
  change stressCovector (NativeT.weightT i a)
    (fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases) W) = 0
  rw [← packed_originalF_derivative, TangentCoordinates.pack_literalCfg_exactPhases]
  exact congrArg (fun L : (Fin 1053 → ℝ) →L[ℝ] ℂ => L (PartialAction.pack W))
    (NativeT.stressCovector_at_bookBase i a)

theorem selectedH_annihilates : NativeH.residualContraction.comp
    (fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases)) = 0 := by
  ext W i a
  exact congrArg (fun L : Cfg →L[ℝ] ℂ => L W) (H_component_annihilates i a)

theorem selectedT_annihilates : selectedT.comp
    (fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases)) = 0 := by
  ext W i a
  exact congrArg (fun L : Cfg →L[ℝ] ℂ => L W) (T_component_annihilates i a)

/-- The selected H reduced quadratic, conditional only on the exact native H reproduction. -/
theorem selectedH_reduced_of_reproduction
    (hrepro : ∀ z, NativeH.residualContraction (Option2.NativeStress.originalF
      (Option2.BookNativeBase.bookBase + realV z)) = H z) (z : Blocks) :
    NativeH.residualContraction (reducedQuadratic z) = H z :=
  stress_reducedQuadratic_of_reproduction NativeH.residualContraction H selectedH_annihilates hrepro z

/-- The selected T reduced quadratic, conditional only on the exact native T reproduction. -/
theorem selectedT_reduced_of_reproduction
    (hrepro : ∀ z, selectedT (Option2.NativeStress.originalF
      (Option2.BookNativeBase.bookBase + realV z)) = T z) (z : Blocks) :
    selectedT (reducedQuadratic z) = T z :=
  stress_reducedQuadratic_of_reproduction selectedT T selectedT_annihilates hrepro z

/-- No annihilation, desired cone, rank or R premise remains: only the two displayed reproductions. -/
theorem actual_reduced_zero_cone_of_reproduction
    (hreproH : ∀ z, NativeH.residualContraction (Option2.NativeStress.originalF
      (Option2.BookNativeBase.bookBase + realV z)) = H z)
    (hreproT : ∀ z, selectedT (Option2.NativeStress.originalF
      (Option2.BookNativeBase.bookBase + realV z)) = T z) (z : Blocks) :
    reducedQuadratic z = 0 ↔ ∃ i, FourBlock.OnAxis i z :=
  reducedQuadratic_zero_cone_of_reproduction NativeH.residualContraction selectedT
    selectedH_annihilates selectedT_annihilates hreproH hreproT z

end Option2.NativeStress.BookHT.ReducedQuadratic

module

public import NativePhaseEntireFamilies
public import NativeRealSliceDerivative

@[expose] public section

/-! The actual raw-family derivative in the explicit entire-extension
coordinates. Parameter inversion is the existing derivation-coordinate
equivalence and the two sum/product coordinate equivalences. -/

noncomputable section
namespace Option2.NativeStress.PhaseBranchDerivativeA6
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open PhaseEntireFamilyA6 PhaseBookComplexificationA6 RealSliceDerivativeA6
open NativePolynomial
open scoped BigOperators Topology

theorem realDer_eq_derivCoordinates (x : ParamIndex → ℝ) :
    realDer x = derivCoordinates (fun j => x (Sum.inl j)) := by
  have hx : (∑ j : Fin 52, x (Sum.inl j) • Pi.single j (1 : ℝ)) =
      (fun j => x (Sum.inl j)) := by
    funext j
    simp [Pi.single_apply]
  simpa only [realDer, derivBasis, map_sum, map_smul] using congrArg derivCoordinates hx

/-- The SAME realParam used by the entire extension is an actual equivalence. -/
def realParamEquiv : (ParamIndex → ℝ) ≃ₗ[ℝ] RawParam62 :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin 52) (Fin 8 ⊕ Fin 2) ℝ ℝ).trans
    (derivCoordinates.prodCongr
      (LinearEquiv.sumArrowLequivProdArrow (Fin 8) (Fin 2) ℝ ℝ))

theorem realParamEquiv_apply (x : ParamIndex → ℝ) : realParamEquiv x = realParam x := by
  apply Prod.ext
  · exact (realDer_eq_derivCoordinates x).symm
  · rfl

def realParamCLM : (ParamIndex → ℝ) →L[ℝ] RawParam62 :=
  ⟨realParamEquiv.toLinearMap, by
    exact LinearMap.continuous_of_finiteDimensional (𝕜 := ℝ)
      (E := ParamIndex → ℝ) (F' := RawParam62) realParamEquiv.toLinearMap⟩

theorem realParamCLM_apply (x : ParamIndex → ℝ) : realParamCLM x = realParam x :=
  realParamEquiv_apply x

def packedRawFamily (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4)
    (x : ParamIndex → ℝ) : Fin 1053 → ℝ :=
  PartialAction.pack (rawMap62 ξ hξ H (realParam x))

def packedRawDerivative (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    (ParamIndex → ℝ) →L[ℝ] (Fin 1053 → ℝ) :=
  packCLM.comp ((rawDer62 ξ hξ H).comp realParamCLM)

private theorem hasFDerivAt_after_clm {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : F → G) (f' : F →L[ℝ] G) (e : E →L[ℝ] F)
    (hf : HasFDerivAt f f' (e 0)) :
    HasFDerivAt (fun x => f (e x)) (f'.comp e) 0 := by
  exact hf.comp 0 e.hasFDerivAt

theorem hasFDerivAt_packedRawFamily (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    HasFDerivAt (packedRawFamily ξ hξ H) (packedRawDerivative ξ hξ H) 0 := by
  have hraw : HasFDerivAt (rawMap62 ξ hξ H) (rawDer62 ξ hξ H) (realParamCLM 0) := by
    simpa only [map_zero] using (hasStrictFDerivAt_rawMap62 hξ H).hasFDerivAt
  have hc := hasFDerivAt_after_clm (rawMap62 ξ hξ H) (rawDer62 ξ hξ H) realParamCLM hraw
  have hcomp : HasFDerivAt (fun x => rawMap62 ξ hξ H (realParamCLM x))
      ((rawDer62 ξ hξ H).comp realParamCLM) (0 : ParamIndex → ℝ) := by
    simpa only [Function.comp_def] using hc
  have h : HasFDerivAt (fun x => packCLM (rawMap62 ξ hξ H (realParamCLM x)))
      (packedRawDerivative ξ hξ H) (0 : ParamIndex → ℝ) :=
    packCLM.hasFDerivAt.comp (0 : ParamIndex → ℝ) hcomp
  have hfun : (fun x => packCLM (rawMap62 ξ hξ H (realParamCLM x))) =
      packedRawFamily ξ hξ H := by
    funext x
    rw [realParamCLM_apply, packCLM_apply]
    rfl
  rw [hfun] at h
  exact h

theorem packedRawDerivative_injective (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    Function.Injective (packedRawDerivative ξ hξ H) := by
  intro x y h
  apply realParamEquiv.injective
  apply rawDer62_injective hξ H
  apply PhaseRankA6.packEquiv.injective
  exact h

/-- Every actual anchor's complex derivative, identified with the proved A5
real derivative rather than an assumed complex rank witness. -/
theorem rawExtension_fderiv_eq_complexMap (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (fderiv ℂ (PhaseEntireFamiliesA6.rawExtension H ξ hξ) 0).toLinearMap =
      complexMap (packedRawDerivative ξ hξ H).toLinearMap := by
  apply real_slice_fderiv_eq_complexMap
    (PhaseEntireFamiliesA6.rawExtension H ξ hξ) (packedRawFamily ξ hξ H)
    (packedRawDerivative ξ hξ H) (PhaseEntireFamiliesA6.rawExtension_entire H ξ hξ 0)
    (hasFDerivAt_packedRawFamily ξ hξ H)
  exact Filter.Eventually.of_forall (PhaseEntireFamiliesA6.rawExtension_real H ξ hξ)

theorem rawExtension_fderiv_injective (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Function.Injective (fderiv ℂ (PhaseEntireFamiliesA6.rawExtension H ξ hξ) 0) := by
  change Function.Injective (fderiv ℂ (PhaseEntireFamiliesA6.rawExtension H ξ hξ) 0).toLinearMap
  rw [rawExtension_fderiv_eq_complexMap]
  exact complexMap_injective_of_injective (packedRawDerivative ξ hξ H).toLinearMap
    (packedRawDerivative_injective ξ hξ H)

#print axioms Option2.NativeStress.PhaseBranchDerivativeA6.hasFDerivAt_packedRawFamily
#print axioms Option2.NativeStress.PhaseBranchDerivativeA6.rawExtension_fderiv_injective
end Option2.NativeStress.PhaseBranchDerivativeA6

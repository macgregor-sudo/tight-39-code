module

public import A3Interfaces
public import A3PolyCalc

@[expose] public section

/-!
# The Fréchet kernel of the original residual equals the native first-order system

Generic in the configuration: at any real zero of all 2184 original rows, the kernel of the real
derivative of `originalF` is real-linearly equivalent, by decoding each point's 27 coordinates, to the
native first-order system of the decoded configuration.
-/

noncomputable section

namespace CKM.NativeFirstOrder

open NativePolynomial NativePolynomial.ConfigurationResiduals

/-- The decoding map on variations: each point's 27 coordinates to a native Albert element. -/
def decodeVariation : PartialAction.Configuration ℝ ≃ₗ[ℝ] (Fin 39 → Glennie.Albert) :=
  LinearEquiv.piCongrRight fun _ => upperCoordinateEquiv.symm

theorem decodeVariation_apply (u : PartialAction.Configuration ℝ) (i : Fin 39) :
    decodeVariation u i = fromUpperCoordinates (u i) := rfl

/-- `pack` as a continuous real-linear map `Configuration ℝ → (Fin 1053 → ℝ)`. -/
def packCLM : PartialAction.Configuration ℝ →L[ℝ] (Fin 1053 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := PartialAction.pack
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem packCLM_apply (C : PartialAction.Configuration ℝ) : packCLM C = PartialAction.pack C := rfl

/-- Explicit Fréchet derivative of the original residual map. -/
theorem hasFDerivAt_originalF (C : PartialAction.Configuration ℝ) :
    HasFDerivAt Option2.NativeStress.AnalyticDerivative.originalF
      (ContinuousLinearMap.pi fun r : Fin 2184 =>
        (∑ j, MvPolynomial.eval (PartialAction.pack C)
            (MvPolynomial.pderiv j (fRow (1/2 : ℝ) (1/3 : ℝ) r)) •
          (ContinuousLinearMap.proj j : (Fin 1053 → ℝ) →L[ℝ] ℝ)).comp packCLM) C :=
  hasFDerivAt_pi.2 fun r =>
    (PolyCalcReal.hasFDerivAt_eval (fRow (1/2 : ℝ) (1/3 : ℝ) r) (packCLM C)).comp C
      packCLM.hasFDerivAt

theorem pointValues_pack (C : PartialAction.Configuration ℝ) :
    MixedCoefficients.pointValues (PartialAction.pack C) = C :=
  funext fun i => funext fun k => PartialAction.pack_variableIndex C i k

theorem mem_ker_fderiv_originalF_iff (C : PartialAction.Configuration ℝ)
    (hC : ∀ r : Fin 2184, MvPolynomial.eval (PartialAction.pack C) (fRow (1/2 : ℝ) (1/3 : ℝ) r) = 0)
    (u : PartialAction.Configuration ℝ) :
    u ∈ LinearMap.ker (fderiv ℝ Option2.NativeStress.AnalyticDerivative.originalF C).toLinearMap ↔
      decodeVariation u ∈ firstOrderSystem (fun i => fromUpperCoordinates (C i)) := by
  have key := FirstCoefficients.original_all_fRows_linearMatrix_zero_iff_native
    (PartialAction.pack C) (PartialAction.pack u) hC
  simp only [PolynomialJets.equationLinearMatrix, PolyCalcReal.translate_coeff_single,
    pointValues_pack] at key
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, (hasFDerivAt_originalF C).fderiv,
    mem_firstOrderSystem, funext_iff]
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply, Pi.zero_apply,
    sum_apply, smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, packCLM_apply, IsFirstOrder, decodeVariation_apply]
  exact key

/-- The literal tangent space is equivalent to the native first-order system of the literal family. -/
theorem tangentSpace_equiv (ξ : Fin 4 → ℂ)
    (hξ : ∀ r : Fin 2184,
      MvPolynomial.eval (PartialAction.pack (literalCfg ξ)) (fRow (1/2 : ℝ) (1/3 : ℝ) r) = 0) :
    Nonempty (tangentSpace ξ ≃ₗ[ℝ] firstOrderSystem (literalPoint ξ)) := by
  have hp : (fun i => fromUpperCoordinates (literalCfg ξ i)) = literalPoint ξ :=
    funext fun i => fromUpperCoordinates_upperCoordinates (literalPoint ξ i)
  refine ⟨decodeVariation.ofSubmodules _ _ ?_⟩
  ext x
  rw [Submodule.mem_map_equiv, tangentSpace, mem_ker_fderiv_originalF_iff _ hξ,
    LinearEquiv.apply_symm_apply, hp]

end CKM.NativeFirstOrder

module

public import NativePhaseBranchDerivative
public import NativePhaseEntireAnalytic
public import AnalyticPullback
public import PolyCalcGerm
public import AssemblyPlumbing

@[expose] public section

/-! Actual fixed-phase A5 families give centered complex analytic germs.
The original translated residual ideal is retained, without radicalization.
This supplies branch maps, not their pairwise distinction or exhaustiveness. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Option2.NativeStress.PhaseAnalyticBranchesA6
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open PhaseEntireFamilyA6 PhaseEntireFamiliesA6 PhaseBranchDerivativeA6
open PhaseHilbertA6 PhaseJetBoundA6 NativePolynomial ConvergentResidualJets
open AnalyticDerivative
open scoped Topology

private theorem derivative_sub_const {m n : ℕ} (f : (Fin m → ℂ) → (Fin n → ℂ))
    (A : (Fin m → ℂ) →L[ℂ] (Fin n → ℂ)) (h : HasFDerivAt f A 0)
    (c : Fin n → ℂ) : HasFDerivAt (fun z => f z - c) A 0 := h.sub_const c

def paramIndexEquiv : ParamIndex ≃ Fin 62 :=
  (Equiv.sumCongr (Equiv.refl (Fin 52)) finSumFinEquiv).trans finSumFinEquiv

def paramCoordinates : (Fin 62 → ℂ) ≃ₗ[ℂ] (ParamIndex → ℂ) where
  toFun z := z ∘ paramIndexEquiv
  invFun z := z ∘ paramIndexEquiv.symm
  left_inv z := by funext i; simp
  right_inv z := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def paramCoordinatesCLM : (Fin 62 → ℂ) →L[ℂ] (ParamIndex → ℂ) :=
  paramCoordinates.toLinearMap.toContinuousLinearMap

@[simp] theorem paramCoordinatesCLM_apply (z : Fin 62 → ℂ) :
    paramCoordinatesCLM z = paramCoordinates z := rfl

def branch (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (z : Fin 62 → ℂ) : Fin 1053 → ℂ :=
  PhaseEntireFamiliesA6.rawExtension H ξ hξ (paramCoordinatesCLM z) -
    complexPack (literalCfg ξ)

theorem rawExtension_zero (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    PhaseEntireFamiliesA6.rawExtension H ξ hξ 0 = complexPack (literalCfg ξ) := by
  have hp : realParam (0 : ParamIndex → ℝ) = 0 := by
    exact (realParamEquiv_apply 0).symm.trans realParamEquiv.map_zero
  have hr : rawMap62 ξ hξ H (0 : RawParam62) = literalCfg ξ := by
    change actC (groupChart 0) (preMap ξ hξ H 0) = literalCfg ξ
    rw [groupChart_zero, actC_one, preMap_zero hξ H]
    rfl
  have h := PhaseEntireFamiliesA6.rawExtension_real H ξ hξ (0 : ParamIndex → ℝ)
  simp only [Pi.zero_apply, Complex.ofReal_zero, hp, hr] at h
  exact h

theorem branch_zero (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    branch H ξ hξ 0 = 0 := by
  simp only [branch, map_zero, rawExtension_zero, sub_self]

theorem branch_entire (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Differentiable ℂ (branch H ξ hξ) :=
  ((PhaseEntireFamiliesA6.rawExtension_entire H ξ hξ).comp
    paramCoordinatesCLM.differentiable).sub_const _

theorem branch_analyticAt (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    AnalyticAt ℂ (branch H ξ hξ) 0 := by
  have h := (PhaseEntireAnalyticA6.rawExtension_analyticAt H ξ hξ 0).comp_of_eq
    (paramCoordinatesCLM.analyticAt 0) (map_zero paramCoordinatesCLM)
  exact h.sub analyticAt_const

def branchDerivative (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (Fin 62 → ℂ) →L[ℂ] (Fin 1053 → ℂ) :=
  (fderiv ℂ (PhaseEntireFamiliesA6.rawExtension H ξ hξ) 0).comp paramCoordinatesCLM

theorem branch_hasFDerivAt (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    HasFDerivAt (branch H ξ hξ) (branchDerivative H ξ hξ) 0 := by
  have h := (PhaseEntireFamiliesA6.rawExtension_entire H ξ hξ 0).hasFDerivAt
  have hc := h.comp (0 : Fin 62 → ℂ) paramCoordinatesCLM.hasFDerivAt
  have hs := derivative_sub_const
    (fun x => PhaseEntireFamiliesA6.rawExtension H ξ hξ (paramCoordinatesCLM x))
    (branchDerivative H ξ hξ) hc (complexPack (literalCfg ξ))
  exact hs

theorem branchDerivative_injective (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Function.Injective (branchDerivative H ξ hξ) :=
  (rawExtension_fderiv_injective H ξ hξ).comp paramCoordinates.injective

theorem branchDerivative_leftInverse (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    ∃ L : (Fin 1053 → ℂ) →L[ℂ] (Fin 62 → ℂ),
      L.comp (branchDerivative H ξ hξ) = ContinuousLinearMap.id ℂ _ := by
  obtain ⟨L,hL⟩ := (branchDerivative H ξ hξ).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (branchDerivative_injective H ξ hξ))
  refine ⟨L.toContinuousLinearMap, ?_⟩
  ext z k
  exact congrFun (congrArg (fun f : (Fin 62 → ℂ) →ₗ[ℂ] (Fin 62 → ℂ) => f z) hL) k

def branchPullback (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    GermRing 1053 →ₐ[ℂ] GermRing 62 :=
  AnalyticPullback.pullback (branch H ξ hξ) (branch_analyticAt H ξ hξ)
    (branch_zero H ξ hξ)

theorem branchPullback_surjective (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Function.Surjective (branchPullback H ξ hξ) := by
  obtain ⟨L,hL⟩ := branchDerivative_leftInverse H ξ hξ
  exact AnalyticPullback.surjective_pullback _ _ _ (branch_hasFDerivAt H ξ hξ) hL

theorem branch_original_rows (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (r : Fin 2184) (z : Fin 62 → ℂ) :
    MvPolynomial.eval (branch H ξ hξ z) (nativeRows ξ r) = 0 := by
  unfold nativeRows PolynomialJets.translate
  rw [← MvPolynomial.eval_assoc]
  have he : (MvPolynomial.eval (branch H ξ hξ z) ∘
      (fun j => MvPolynomial.X j + MvPolynomial.C
        ((PartialAction.pack (literalCfg ξ) j : ℝ) : ℂ))) =
      PhaseEntireFamiliesA6.rawExtension H ξ hξ (paramCoordinatesCLM z) := by
    funext j
    simp only [Function.comp_apply, map_add, MvPolynomial.eval_X, MvPolynomial.eval_C,
      branch, Pi.sub_apply]
    change (_ - complexPack (literalCfg ξ) j) + complexPack (literalCfg ξ) j = _
    exact sub_add_cancel _ _
  rw [he]
  exact PhaseEntireFamiliesA6.rawExtension_original_rows H ξ hξ r _

theorem branchPullback_polynomial_zero (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (r : Fin 2184) : branchPullback H ξ hξ (polynomialGerm 1053 (nativeRows ξ r)) = 0 := by
  rw [branchPullback, AnalyticPullback.pullback_polynomialGerm]
  let c : Fin 1053 → (Fin 62 → ℂ) → ℂ := fun j z => branch H ξ hξ z j
  have hc : ∀ j, AnalyticAt ℂ (c j) 0 := fun j =>
    AnalyticPullback.analyticAt_apply _ (branch_analyticAt H ξ hξ) (branch_zero H ξ hξ) j
  have he := PolyCalc.ofAnalyticAt_aeval c hc (nativeRows ξ r)
    (PolyCalc.analyticAt_aeval c hc (nativeRows ξ r))
  change MvPolynomial.aeval
    (fun j => PolyCalc.toGerm 62 (PolyCalc.analyticElt 62 (c j) (hc j))) (nativeRows ξ r) = 0
  rw [← he, AnalyticPullback.ofAnalyticAt_eq_zero_iff]
  exact Filter.Eventually.of_forall fun z => by
    change MvPolynomial.aeval (branch H ξ hξ z) (nativeRows ξ r) = 0
    rw [MvPolynomial.aeval_def, Algebra.algebraMap_self]
    exact branch_original_rows H ξ hξ r z

theorem nativePhaseAnalyticIdeal_le_branchKernel (H : Fin 4) (ξ : Fin 4 → ℂ)
    (hξ : IsUnitPhase ξ) :
    nativePhaseAnalyticIdeal ξ ≤ RingHom.ker (branchPullback H ξ hξ).toRingHom :=
  FourSheets.Plumbing.map_span_le_ker _ _ _ (branchPullback_polynomial_zero H ξ hξ)

theorem nativePhaseAnalyticIdeal_le_fourBranchKernels (ξ : Fin 4 → ℂ)
    (hξ : IsUnitPhase ξ) :
    nativePhaseAnalyticIdeal ξ ≤ ⨅ H : Fin 4, RingHom.ker (branchPullback H ξ hξ).toRingHom :=
  le_iInf (fun H => nativePhaseAnalyticIdeal_le_branchKernel H ξ hξ)

#print axioms Option2.NativeStress.PhaseAnalyticBranchesA6.branchPullback_surjective
#print axioms Option2.NativeStress.PhaseAnalyticBranchesA6.nativePhaseAnalyticIdeal_le_fourBranchKernels
end Option2.NativeStress.PhaseAnalyticBranchesA6


module

public import NativePhaseAnalyticBranches

@[expose] public section

/-! Distinct actual A5 branches at a good phase have incomparable pullback
kernels. Separation comes from the accepted ten-dimensional normal family
tangents with four-dimensional pairwise intersection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Option2.NativeStress.PhaseBranchSeparationA6
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open PhaseEntireFamilyA6 PhaseBranchDerivativeA6 PhaseAnalyticBranchesA6
open PhaseBookComplexificationA6 HTPhaseComplete

theorem normalProj_rawDer62 {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ)
    (H : Fin 4) (p : RawParam62) :
    normalProjXi ξ hξ (rawDer62 ξ hξ H p) = sliceFamDer ξ hξ H p.2 := by
  have ho : normalProjXi ξ hξ (orbitMapC ξ (p.1 : CEnd)) = 0 :=
    (normalProj_eq_zero_iff hξ _).2 ⟨p.1, p.1.property, rfl⟩
  rw [rawDer62_apply hξ H, rawDer_apply hξ H, map_add, ho, zero_add,
    HTPhaseComplete.sliceFamDer_apply hξ H]

theorem fixQ_le_of_raw_range_le {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (H H' : Fin 4)
    (h : LinearMap.range (rawDer62 ξ hξ.1 H).toLinearMap ≤
      LinearMap.range (rawDer62 ξ hξ.1 H').toLinearMap) :
    fixQ ξ H ≤ fixQ ξ H' := by
  intro v hv
  rw [← range_sliceFamDer hξ H] at hv
  obtain ⟨n, ⟨p, rfl⟩, rfl⟩ := hv
  obtain ⟨q,hq⟩ := h (LinearMap.mem_range.mpr
    ⟨((0 : derC),p), rfl⟩)
  have hp := congrArg (normalProjXi ξ hξ.1) hq
  change normalProjXi ξ hξ.1 (rawDer62 ξ hξ.1 H' q) =
    normalProjXi ξ hξ.1 (rawDer62 ξ hξ.1 H (0,p)) at hp
  rw [normalProj_rawDer62, normalProj_rawDer62] at hp
  rw [← range_sliceFamDer hξ H']
  exact ⟨sliceFamDer ξ hξ.1 H' q.2, ⟨q.2,rfl⟩, congrArg Subtype.val hp⟩

theorem raw_range_not_le {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    {H H' : Fin 4} (hne : H ≠ H') :
    ¬ LinearMap.range (rawDer62 ξ hξ.1 H).toLinearMap ≤
      LinearMap.range (rawDer62 ξ hξ.1 H').toLinearMap := by
  intro h
  have hi := fixQ_le_of_raw_range_le hξ H H' h
  have he : fixQ ξ H = fixQK ξ := by
    rw [← fixQ_inf_fixQ hne, inf_eq_left.mpr hi]
  have hd := finrank_fixQ hξ H
  rw [he, finrank_fixQK hξ] at hd
  norm_num at hd

theorem branchDerivative_complexMap (H : Fin 4) (ξ : Fin 4 → ℂ)
    (hξ : IsUnitPhase ξ) (z : Fin 62 → ℂ) :
    branchDerivative H ξ hξ z =
      complexMap (packedRawDerivative ξ hξ H).toLinearMap (paramCoordinates z) := by
  change (fderiv ℂ (PhaseEntireFamiliesA6.rawExtension H ξ hξ) 0).toLinearMap
    (paramCoordinates z) = _
  rw [rawExtension_fderiv_eq_complexMap]

/-- Taking real parts recovers inclusion of the actual real raw derivatives;
no complex linearity of the original real parameter map is assumed. -/
theorem raw_range_le_of_branch_range_le {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ)
    (H H' : Fin 4)
    (h : LinearMap.range (branchDerivative H ξ hξ).toLinearMap ≤
      LinearMap.range (branchDerivative H' ξ hξ).toLinearMap) :
    LinearMap.range (rawDer62 ξ hξ H).toLinearMap ≤
      LinearMap.range (rawDer62 ξ hξ H').toLinearMap := by
  rintro v ⟨p,rfl⟩
  let x : ParamIndex → ℝ := realParamEquiv.symm p
  let z : Fin 62 → ℂ := paramCoordinates.symm (fun k => (x k : ℂ))
  obtain ⟨w,hw⟩ := h (LinearMap.mem_range.mpr ⟨z,rfl⟩)
  have he : complexMap (packedRawDerivative ξ hξ H').toLinearMap (paramCoordinates w) =
      complexMap (packedRawDerivative ξ hξ H).toLinearMap (fun k => (x k : ℂ)) := by
    simpa only [ContinuousLinearMap.coe_coe, branchDerivative_complexMap, z,
      LinearEquiv.apply_symm_apply] using hw
  have hr := congrArg (fun y : Fin 1053 → ℂ => fun k => (y k).re) he
  rw [complexMap_re, complexMap_re] at hr
  simp only [Complex.ofReal_re] at hr
  change packedRawDerivative ξ hξ H' (fun k => (paramCoordinates w k).re) =
    packedRawDerivative ξ hξ H x at hr
  refine ⟨realParamEquiv (fun k => (paramCoordinates w k).re), ?_⟩
  apply PhaseRankA6.packEquiv.injective
  change packedRawDerivative ξ hξ H' (fun k => (paramCoordinates w k).re) =
    PhaseRankA6.packEquiv (rawDer62 ξ hξ H p)
  rw [hr]
  change PhaseRankA6.packEquiv (rawDer62 ξ hξ H (realParamEquiv x)) = _
  rw [LinearEquiv.apply_symm_apply]

theorem branch_range_not_le {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    {H H' : Fin 4} (hne : H ≠ H') :
    ¬ LinearMap.range (branchDerivative H ξ hξ.1).toLinearMap ≤
      LinearMap.range (branchDerivative H' ξ hξ.1).toLinearMap :=
  fun h => raw_range_not_le hξ hne (raw_range_le_of_branch_range_le hξ.1 H H' h)

/-- Kernel inclusion reverses tangent-range inclusion, contradicting the
actual A5 normal-tangent separation for distinct anchor labels. -/
theorem branchKernel_not_le {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    {H H' : Fin 4} (hne : H ≠ H') :
    ¬ RingHom.ker (branchPullback H ξ hξ.1).toRingHom ≤
      RingHom.ker (branchPullback H' ξ hξ.1).toRingHom := by
  intro h
  obtain ⟨L,hL⟩ := branchDerivative_leftInverse H ξ hξ.1
  have hr := AnalyticPullback.range_le_of_ker_le
    (branch H ξ hξ.1) (branch_analyticAt H ξ hξ.1) (branch_zero H ξ hξ.1)
    (branch_hasFDerivAt H ξ hξ.1) hL
    (branch H' ξ hξ.1) (branch_analyticAt H' ξ hξ.1) (branch_zero H' ξ hξ.1)
    (branch_hasFDerivAt H' ξ hξ.1) h
  exact branch_range_not_le hξ hne.symm hr

theorem branchKernels_incomparable {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    {H H' : Fin 4} (hne : H ≠ H') :
    (¬ RingHom.ker (branchPullback H ξ hξ.1).toRingHom ≤
      RingHom.ker (branchPullback H' ξ hξ.1).toRingHom) ∧
    (¬ RingHom.ker (branchPullback H' ξ hξ.1).toRingHom ≤
      RingHom.ker (branchPullback H ξ hξ.1).toRingHom) :=
  ⟨branchKernel_not_le hξ hne, branchKernel_not_le hξ hne.symm⟩

#print axioms Option2.NativeStress.PhaseBranchSeparationA6.raw_range_not_le
#print axioms Option2.NativeStress.PhaseBranchSeparationA6.branchKernels_incomparable
end Option2.NativeStress.PhaseBranchSeparationA6

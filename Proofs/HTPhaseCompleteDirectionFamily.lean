module

public import HTPhaseCompleteDirection

@[expose] public section

/-!
# `Vxi` against the actual A5 family variation at every unit phase

* `Vxi_axis`: on Book block `H`, `Vxi ξ (single H u) = pack (preVar ξ hξ H (X, X, 0))`,
  `X = axisParameters H u` (the accepted seed parameter map, unchanged);
* `Vxi_family`, `unpack_Vxi`: the packed family-variation identities;
* `preVar_simultaneous_eq`: the simultaneous direction `(X, X, 0)` is the slice-family direction
  `(X, 0, 0)` MINUS the exhibited orbit vector `orbitMapC ξ (gaugeDer H X)` (`gaugeDer H X ∈ derC`);
* `Vxi_axis_slice`: through the actual derivative `sliceRepDer` of the slice coordinate,
  `sliceRepDer (unpack (Vxi ξ (single H u))) = sliceFamDer ξ hξ H (axisParameters H u, 0)`.
No GoodPhase hypothesis is used; all statements hold for `IsUnitPhase ξ`. First-party.
-/

set_option Elab.async false
set_option maxRecDepth 2000
noncomputable section

namespace Option2.NativeStress.HTPhaseComplete

open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open Option2.NativeStress.BookHT Option2.NativeStress.BookHT.TangentCoordinates
open Option2.NativeStress.BookHT.NativeNormalKernelBridge
open QuadraticCertificate.ExactCKMConfiguration
open NativePolynomial
open scoped ComplexConjugate

/-- Actual simultaneous family derivative of anchor `H`, packed. -/
def famL (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) : (Fin 8 → ℝ) →L[ℝ] (Fin 1053 → ℝ) :=
  packCLM.comp ((preDer ξ hξ H).comp simultaneousParameters)

theorem famL_apply (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) (X : Fin 8 → ℝ) :
    famL ξ hξ H X = PartialAction.pack (preVar ξ hξ H (X, X, 0)) := by
  change PartialAction.pack (preDer ξ hξ H (X, X, 0)) = _
  rw [preDer_apply]

theorem colRe_famL (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (j : Fin 24) :
    colRe ξ hξ j = famL ξ hξ (d6Sheet (eigenIndex j))
      (rootRealParam ⟨(eigenIndex j).val % 6, by omega⟩) := by
  rw [famL_apply]; rfl

theorem colIm_famL (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (j : Fin 24) :
    colIm ξ hξ j = famL ξ hξ (d6Sheet (eigenIndex j))
      (rootImagParam ⟨(eigenIndex j).val % 6, by omega⟩) := by
  rw [famL_apply]; rfl

private theorem map_single' (F : (Fin 8 → ℝ) →L[ℝ] (Fin 1053 → ℝ))
    (m : Fin 8) (a : ℝ) : F (Pi.single m a) = a • F (Pi.single m 1) := by
  rw [← map_smul]
  congr 1
  ext k
  simp [Pi.single_apply, ite_mul, mul_ite]

private theorem map_half' (F : (Fin 8 → ℝ) →L[ℝ] (Fin 1053 → ℝ)) (m : Fin 8) :
    F (Pi.single m (1/2 : ℝ)) = (1/2 : ℝ) • F (Pi.single m 1) := map_single' F m _
private theorem map_neg_half' (F : (Fin 8 → ℝ) →L[ℝ] (Fin 1053 → ℝ)) (m : Fin 8) :
    F (Pi.single m (-(1/2) : ℝ)) = (-(1/2) : ℝ) • F (Pi.single m 1) := map_single' F m _

set_option maxHeartbeats 800000 in
/-- Book block `H` of the phase direction is the actual simultaneous family of anchor `H`, through the
accepted parameter map `axisParameters` — at every unit phase. -/
theorem Vxi_axis (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) (u : BookHT.Triple) :
    Vxi ξ hξ (Pi.single H u) = famL ξ hξ H (axisParameters H u) := by
  rw [Vxi_apply]
  simp only [colRe_famL, colIm_famL]
  fin_cases H <;>
    norm_num [Fin.sum_univ_succ, Dictionary.realCoordinates, eigenIndex, d6Sheet,
      rootRealParam, rootImagParam, Pi.single_apply, axisParameters, map_add,
      map_half', map_neg_half', map_smul, map_zero, zero_smul, sub_zero, zero_sub, Complex.neg_re,
      Complex.neg_im, Complex.conj_re, Complex.conj_im]
  all_goals module

theorem Vxi_family (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : BookHT.Blocks) :
    Vxi ξ hξ z = ∑ H : Fin 4, PartialAction.pack
      (preVar ξ hξ H (axisParameters H (z H), axisParameters H (z H), 0)) := by
  conv_lhs => rw [← Finset.univ_sum_single z, map_sum]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [Vxi_axis, famL_apply]

theorem unpack_Vxi (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : BookHT.Blocks) :
    unpackNative (Vxi ξ hξ z) = ∑ H : Fin 4,
      preVar ξ hξ H (axisParameters H (z H), axisParameters H (z H), 0) := by
  rw [Vxi_family, map_sum]
  simp only [unpackNative_pack]

/-! ## Gauge comparison with the slice family -/

/-- The simultaneous direction = slice-family direction − an exhibited orbit vector. -/
theorem preVar_simultaneous_eq (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) (X : Fin 8 → ℝ) :
    preVar ξ hξ H (X, X, 0) = preVar ξ hξ H (X, 0, 0) - orbitMapC ξ (gaugeDer H X) := by
  have he := orbitMapC_gaugeDer hξ H X
  rw [← preDer_apply, ← preDer_apply,
    show (X, X, (0 : Fin 2 → ℝ)) = (X, 0, 0) + (0, X, 0) by simp, map_add,
    eq_neg_of_add_eq_zero_right he, sub_eq_add_neg]

theorem unpack_Vxi_axis (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) (u : BookHT.Triple) :
    unpackNative (Vxi ξ hξ (Pi.single H u)) =
      preVar ξ hξ H (axisParameters H u, 0, 0) - orbitMapC ξ (gaugeDer H (axisParameters H u)) ∧
    gaugeDer H (axisParameters H u) ∈ derC := by
  refine ⟨?_, gaugeDer_mem_derC H _⟩
  rw [Vxi_axis, famL_apply, unpackNative_pack, preVar_simultaneous_eq]

/-- The slice coordinate has a strict derivative at the literal point that kills every orbit
direction (it is the `N`-component of `sliceDiff⁻¹`, inverse function theorem). -/
theorem sliceRep_deriv_exists (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    ∃ L : Cfg →L[ℝ] ↥(normalC ξ), HasStrictFDerivAt (sliceRep ξ hξ) L (literalCfg ξ) ∧
      ∀ D : ↥derC, L (orbitMapC ξ (D : CEnd)) = 0 := by
  have hs : HasStrictFDerivAt (slicePH ξ hξ).symm
      ((sliceDiff ξ hξ).symm : Cfg →L[ℝ] ↥derC × ↥(normalC ξ)) (literalCfg ξ) := by
    rw [← sliceChart_zero ξ]
    exact (hasStrictFDerivAt_sliceChart ξ hξ).to_localInverse
  show ∃ L : Cfg →L[ℝ] ↥(normalC ξ),
    HasStrictFDerivAt (fun y => ((slicePH ξ hξ).symm y).2) L (literalCfg ξ) ∧
      ∀ D : ↥derC, L (orbitMapC ξ (D : CEnd)) = 0
  refine ⟨_, (hasStrictFDerivAt_snd (𝕜 := ℝ) (E := ↥derC) (F := ↥(normalC ξ))).comp _ hs,
    fun D => ?_⟩
  have h : (sliceDiff ξ hξ).symm (orbitMapC ξ (D : CEnd)) = (D, 0) := by
    rw [ContinuousLinearEquiv.symm_apply_eq, sliceDiff_apply, Submodule.coe_zero, add_zero]
  change ((sliceDiff ξ hξ).symm (orbitMapC ξ (D : CEnd))).2 = 0
  rw [h]

/-- The actual derivative of the slice coordinate at the literal point. -/
def sliceRepDer (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Cfg →L[ℝ] ↥(normalC ξ) :=
  fderiv ℝ (sliceRep ξ hξ) (literalCfg ξ)

theorem hasStrictFDerivAt_sliceRep (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    HasStrictFDerivAt (sliceRep ξ hξ) (sliceRepDer ξ hξ) (literalCfg ξ) := by
  obtain ⟨L, hL, -⟩ := sliceRep_deriv_exists ξ hξ
  rw [sliceRepDer, hL.hasFDerivAt.fderiv]
  exact hL

theorem sliceRepDer_orbit (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (D : ↥derC) :
    sliceRepDer ξ hξ (orbitMapC ξ (D : CEnd)) = 0 := by
  obtain ⟨L, hL, hO⟩ := sliceRep_deriv_exists ξ hξ
  rw [sliceRepDer, hL.hasFDerivAt.fderiv]
  exact hO D

private def sliceEmbed : SliceParam →L[ℝ] PreParam :=
  (ContinuousLinearMap.fst ℝ (Fin 8 → ℝ) (Fin 2 → ℝ)).prod
    ((0 : SliceParam →L[ℝ] (Fin 8 → ℝ)).prod (ContinuousLinearMap.snd ℝ (Fin 8 → ℝ) (Fin 2 → ℝ)))

theorem sliceFamDer_apply' (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) (p : SliceParam) :
    sliceFamDer ξ hξ H p = sliceRepDer ξ hξ (preVar ξ hξ H (p.1, 0, p.2)) := by
  have hP := hasStrictFDerivAt_preMap hξ H
  have h0 : preMap ξ hξ H (sliceEmbed 0) = literalCfg ξ := by
    rw [map_zero]; exact preMap_zero hξ H
  have hL := hasStrictFDerivAt_sliceRep ξ hξ
  rw [← h0] at hL
  rw [← map_zero sliceEmbed] at hP
  have hc := hL.comp (0 : SliceParam) (hP.comp (0 : SliceParam) sliceEmbed.hasStrictFDerivAt)
  have hd : sliceFamDer ξ hξ H =
      (sliceRepDer ξ hξ).comp ((preDer ξ hξ H).comp sliceEmbed) := hc.hasFDerivAt.fderiv
  rw [hd]
  change sliceRepDer ξ hξ (preDer ξ hξ H (p.1, 0, p.2)) = _
  rw [preDer_apply]

/-- Book block `H` of `Vxi` maps, under the actual slice-coordinate derivative, to the actual
derivative of `sliceFam ξ H` at parameter `(axisParameters H u, 0)`. -/
theorem Vxi_axis_slice (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) (u : BookHT.Triple) :
    sliceRepDer ξ hξ (unpackNative (Vxi ξ hξ (Pi.single H u))) =
      sliceFamDer ξ hξ H (axisParameters H u, 0) := by
  rw [(unpack_Vxi_axis ξ hξ H u).1, map_sub,
    sliceRepDer_orbit ξ hξ ⟨gaugeDer H (axisParameters H u), gaugeDer_mem_derC H _⟩, sub_zero,
    sliceFamDer_apply']

end Option2.NativeStress.HTPhaseComplete

open Option2.NativeStress.HTPhaseComplete
#print axioms Vxi_axis
#print axioms Vxi_family
#print axioms unpack_Vxi
#print axioms preVar_simultaneous_eq
#print axioms unpack_Vxi_axis
#print axioms hasStrictFDerivAt_sliceRep
#print axioms sliceRepDer_orbit
#print axioms sliceFamDer_apply'
#print axioms Vxi_axis_slice

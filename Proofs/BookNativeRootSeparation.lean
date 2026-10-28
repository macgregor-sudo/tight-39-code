module

public import BookNativeCartanCompensation

@[expose] public section

/-! Actual derivative of the Cartan compensation and native off-diagonal
root separation from orbit plus common tangent. No rank premise is added. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.BookHT.NativeNormalKernelBridge
open TangentCoordinates CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeFourFamily.CartanSuccessor
open NativePolynomial QuadraticCertificate.ExactCKMConfiguration
open scoped Topology

theorem normalProjection_eq_sliceDiff :
    normalProjection =
      (ContinuousLinearMap.snd ℝ derC (normalC exactPhases)).comp
        (sliceDiff exactPhases exactPhases_unit).symm.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro w
  let p := (sliceDiff exactPhases exactPhases_unit).symm w
  have hp : orbitMapC exactPhases (p.1 : CEnd) + (p.2 : Cfg) = w := by
    exact (sliceDiff_apply exactPhases exactPhases_unit p).symm.trans
      ((sliceDiff exactPhases exactPhases_unit).apply_symm_apply w)
  have ho : normalProjection (orbitMapC exactPhases (p.1 : CEnd)) = 0 :=
    (normalProjection_eq_zero_iff _).2 ⟨p.1, p.1.property, rfl⟩
  change normalProjection w = p.2
  rw [← hp, map_add, ho, normalProjection_normal, zero_add]

theorem sliceRep_hasStrictFDerivAt_normalProjection :
    HasStrictFDerivAt (sliceRep exactPhases exactPhases_unit)
      normalProjection (literalCfg exactPhases) := by
  have hi : HasStrictFDerivAt (slicePH exactPhases exactPhases_unit).symm
      ((sliceDiff exactPhases exactPhases_unit).symm :
        Cfg →L[ℝ] derC × normalC exactPhases) (literalCfg exactPhases) := by
    rw [← sliceChart_zero exactPhases]
    exact (hasStrictFDerivAt_sliceChart exactPhases exactPhases_unit).to_localInverse
  rw [normalProjection_eq_sliceDiff]
  exact HasStrictFDerivAt.comp (𝕜 := ℝ) (E := Cfg)
    (F := ↥derC × ↥(normalC exactPhases)) (G := ↥(normalC exactPhases))
    (literalCfg exactPhases)
    (hasStrictFDerivAt_snd (𝕜 := ℝ) (E := ↥derC) (F := ↥(normalC exactPhases))) hi

def rootFamilyEmbed : SliceParam →L[ℝ] PreParam :=
  (ContinuousLinearMap.fst ℝ (Fin 8 → ℝ) (Fin 2 → ℝ)).prod
    ((0 : SliceParam →L[ℝ] (Fin 8 → ℝ)).prod
      (ContinuousLinearMap.snd ℝ (Fin 8 → ℝ) (Fin 2 → ℝ)))

theorem sliceFamDer_eq_normalProjection (H : Fin 4) :
    sliceFamDer exactPhases exactPhases_unit H =
      normalProjection.comp ((preDer exactPhases exactPhases_unit H).comp rootFamilyEmbed) := by
  have hpre : HasStrictFDerivAt
      (fun p : SliceParam => preMap exactPhases exactPhases_unit H (rootFamilyEmbed p))
      ((preDer exactPhases exactPhases_unit H).comp rootFamilyEmbed) 0 := by
    have hp := hasStrictFDerivAt_preMap exactPhases_unit H
    rw [← map_zero rootFamilyEmbed] at hp
    exact hp.comp 0 rootFamilyEmbed.hasStrictFDerivAt
  have hrep : HasStrictFDerivAt (sliceRep exactPhases exactPhases_unit) normalProjection
      (preMap exactPhases exactPhases_unit H (rootFamilyEmbed 0)) := by
    simpa only [map_zero, preMap_zero exactPhases_unit H] using
      sliceRep_hasStrictFDerivAt_normalProjection
  exact (hasStrictFDerivAt_sliceFam exactPhases_unit H).hasFDerivAt.unique
    (HasStrictFDerivAt.comp (𝕜 := ℝ) (E := SliceParam) (F := Cfg)
      (G := ↥(normalC exactPhases))
      (f := fun p : SliceParam => preMap exactPhases exactPhases_unit H (rootFamilyEmbed p))
      0 hrep hpre).hasFDerivAt

theorem exists_common_derivative_cartan (H : Fin 4) :
    ∃ (K : (Fin 4 → ℝ) →L[ℝ] (Fin 8 → ℝ)) (E : (Fin 4 → ℝ) →L[ℝ] (Fin 2 → ℝ)),
      (∀ θ m, m ≠ 2 → m ≠ 7 → K θ m = 0) ∧
      ∀ θ, sliceCommonDer exactPhases exactPhases_unit θ =
        sliceFamDer exactPhases exactPhases_unit H (K θ, E θ) := by
  obtain ⟨A, k, e, hA, hA0, hAaut, hk, hk0, he, he0, hcartan, hcomp⟩ :=
    exists_compensation_cartan exactPhases_unit H
  obtain ⟨Wg, hWg, Wy, hWy, hinv⟩ := exists_sliceRep_invariant exactPhases_unit
  have hAev : ∀ᶠ θ in 𝓝 (0 : Fin 4 → ℝ), A θ ∈ Wg :=
    hA.continuousAt.preimage_mem_nhds (by rw [hA0]; exact hWg)
  have hpre : ContinuousAt
      (fun θ => preMap exactPhases exactPhases_unit H (rootFamilyEmbed (k θ, e θ))) 0 := by
    have h1 : ContinuousAt (fun θ => rootFamilyEmbed (k θ, e θ)) 0 :=
      rootFamilyEmbed.continuous.continuousAt.comp (hk.continuousAt.prodMk he.continuousAt)
    have h2 : rootFamilyEmbed (k 0, e 0) = 0 := by rw [hk0, he0]; rfl
    exact (analyticAt_preMap exactPhases_unit H).continuousAt.comp_of_eq h1 h2
  have hpre0 : preMap exactPhases exactPhases_unit H (rootFamilyEmbed (k 0, e 0)) =
      literalCfg exactPhases := by
    rw [hk0, he0, Prod.mk_zero_zero, map_zero, preMap_zero]
  have hpev : ∀ᶠ θ in 𝓝 (0 : Fin 4 → ℝ),
      preMap exactPhases exactPhases_unit H (rootFamilyEmbed (k θ, e θ)) ∈ Wy :=
    hpre.preimage_mem_nhds (by rw [hpre0]; exact hWy)
  have hgerm : (fun θ => sliceFam exactPhases exactPhases_unit H (k θ, e θ)) =ᶠ[𝓝 0]
      sliceCommon exactPhases exactPhases_unit := by
    filter_upwards [hAev, hpev] with θ h1 h2
    change sliceRep exactPhases exactPhases_unit
      (preMap exactPhases exactPhases_unit H (k θ, 0, e θ)) =
      sliceRep exactPhases exactPhases_unit (literalCfg (commonPhase exactPhases θ))
    rw [hcomp θ]
    exact (hinv _ ⟨hAaut θ, h1⟩ _ h2).symm
  have hψ : HasFDerivAt (fun θ => (k θ, e θ))
      ((fderiv ℝ k 0).prod (fderiv ℝ e 0)) 0 :=
    hk.differentiableAt.hasFDerivAt.prodMk he.differentiableAt.hasFDerivAt
  have hf : HasFDerivAt (sliceFam exactPhases exactPhases_unit H)
      (sliceFamDer exactPhases exactPhases_unit H) (k 0, e 0) := by
    rw [hk0, he0, Prod.mk_zero_zero]
    exact (hasStrictFDerivAt_sliceFam exactPhases_unit H).hasFDerivAt
  have hchain : HasFDerivAt (sliceCommon exactPhases exactPhases_unit)
      ((sliceFamDer exactPhases exactPhases_unit H).comp
        ((fderiv ℝ k 0).prod (fderiv ℝ e 0))) 0 :=
    (HasFDerivAt.comp (𝕜 := ℝ) (E := Fin 4 → ℝ) (F := SliceParam)
      (G := ↥(normalC exactPhases))
      (f := fun θ => (k θ, e θ)) (g := sliceFam exactPhases exactPhases_unit H)
      0 hf hψ).congr_of_eventuallyEq hgerm.symm
  have hd := hchain.unique (hasStrictFDerivAt_sliceCommon exactPhases_unit).hasFDerivAt
  refine ⟨fderiv ℝ k 0, fderiv ℝ e 0, fderiv_cartan_support hk hcartan, ?_⟩
  intro θ
  exact (congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] normalC exactPhases => L θ) hd).symm

/-- The precise actual off-diagonal root family has zero intersection with the common tangent. -/
theorem projected_offDiagonal_inter_common (H : Fin 4) (X : Fin 8 → ℝ)
    (h2 : X 2 = 0) (h7 : X 7 = 0)
    (hcommon : (projectedSimultaneousFamily H X : Cfg) ∈ fixQK exactPhases) : X = 0 := by
  rw [← range_sliceCommonDer exactPhases_good] at hcommon
  obtain ⟨n, ⟨θ, rfl⟩, he⟩ := hcommon
  have heN : sliceCommonDer exactPhases exactPhases_unit θ = projectedSimultaneousFamily H X :=
    Subtype.ext he
  obtain ⟨K, E, hK, hder⟩ := exists_common_derivative_cartan H
  have hleft : sliceFamDer exactPhases exactPhases_unit H (X, 0) =
      projectedSimultaneousFamily H X := by
    rw [sliceFamDer_eq_normalProjection]
    change normalProjection (preDer exactPhases exactPhases_unit H (X, 0, 0)) = _
    rw [preDer_apply, projectedSimultaneousFamily_eq_left]
  have hpair : (X, (0 : Fin 2 → ℝ)) = (K θ, E θ) :=
    sliceFamDer_injective exactPhases_unit H (hleft.trans (heN.symm.trans (hder θ)))
  have hX : X = K θ := congrArg Prod.fst hpair
  funext m
  by_cases hm2 : m = 2
  · subst m; exact h2
  by_cases hm7 : m = 7
  · subst m; exact h7
  rw [hX]
  exact hK θ m hm2 hm7

end Option2.NativeStress.BookHT.NativeNormalKernelBridge
#check Option2.NativeStress.BookHT.NativeNormalKernelBridge.exists_common_derivative_cartan
#check Option2.NativeStress.BookHT.NativeNormalKernelBridge.projected_offDiagonal_inter_common
#print axioms Option2.NativeStress.BookHT.NativeNormalKernelBridge.exists_common_derivative_cartan
#print axioms Option2.NativeStress.BookHT.NativeNormalKernelBridge.projected_offDiagonal_inter_common

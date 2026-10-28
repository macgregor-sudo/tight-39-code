module

public import A5Analytic
public import A5Rank
public import A5PhaseIndep
public import A5Comp
public import A5KLin

@[expose] public section

/-!
# Slice representatives of the families (piece SLICEA)

`sliceRep` is the `N`-coordinate of the group/slice chart's inverse. Near `P` and for `A ∈ G` near
`1`, `sliceRep (A • y) = sliceRep y` (compose with the local inverse of `groupChart`, uniqueness of
`slicePH` preimages). The slice families are analytic with injective derivatives: an `N`-zero
derivative direction `(X, e)` of `sliceFam` gives an element `(-D, X, 0, e)` of `ker rawDer`,
which is zero (`rawDer_eq_zero_iff`); for `sliceCommon` use `phase_indep_mod_orbit`. The explicit
compensations (`exists_compensation`) give the slice inclusion `sliceCommon = sliceFam ∘ ψ` and the
raw inclusion `commonMap = rawMap62 ∘ Γ` (with `Γ` built from the analytic local inverse of
`groupChart`, `exists_groupChart_local`).
-/

noncomputable section

open CKM.NativeFirstOrder CKM.NativeGroupSlice CompactAlbert UnitaryErrorBases
open scoped Matrix Topology

namespace CKM.NativeFourFamily


/-! ## Helpers: the slice coordinate near `P` -/

/-- The inverse slice chart has strict derivative `sliceDiff⁻¹` at `P` (inverse function theorem,
`HasStrictFDerivAt.to_localInverse`; `slicePH` is GS's `ophOf` of the strict derivative). -/
private theorem sliceA_hasStrictFDerivAt_symm {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    HasStrictFDerivAt (slicePH ξ₀ hξ₀).symm
      ((sliceDiff ξ₀ hξ₀).symm : Cfg →L[ℝ] ↥derC × ↥(normalC ξ₀)) (literalCfg ξ₀) := by
  rw [← sliceChart_zero ξ₀]
  exact (hasStrictFDerivAt_sliceChart ξ₀ hξ₀).to_localInverse

/-- The slice coordinate has a strict derivative at `P` (the `N`-component of `sliceDiff⁻¹`) whose
kernel consists of orbit directions. (Elaborated against an expected type with the projection's
domain given explicitly: this avoids unifying the two topologies on `derC × N`.) -/
private theorem sliceA_rep_deriv {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    ∃ L : Cfg →L[ℝ] ↥(normalC ξ₀), HasStrictFDerivAt (sliceRep ξ₀ hξ₀) L (literalCfg ξ₀) ∧
      ∀ w, L w = 0 → ∃ D : ↥derC, w = orbitMapC ξ₀ (D : CEnd) := by
  show ∃ L : Cfg →L[ℝ] ↥(normalC ξ₀),
    HasStrictFDerivAt (fun y => ((slicePH ξ₀ hξ₀).symm y).2) L (literalCfg ξ₀) ∧
      ∀ w, L w = 0 → ∃ D : ↥derC, w = orbitMapC ξ₀ (D : CEnd)
  refine ⟨_, (hasStrictFDerivAt_snd (𝕜 := ℝ) (E := ↥derC) (F := ↥(normalC ξ₀))).comp _
    (sliceA_hasStrictFDerivAt_symm hξ₀), fun w hw => ⟨((sliceDiff ξ₀ hξ₀).symm w).1, ?_⟩⟩
  have h2 : ((sliceDiff ξ₀ hξ₀).symm w).2 = 0 := hw
  have h1 := (sliceDiff ξ₀ hξ₀).apply_symm_apply w
  rw [sliceDiff_apply, h2, Submodule.coe_zero, add_zero] at h1
  exact h1.symm

private theorem sliceA_analyticAt_rep {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    AnalyticAt ℝ (sliceRep ξ₀ hξ₀) (literalCfg ξ₀) :=
  analyticAt_snd.comp (analyticAt_slicePH_symm ξ₀ hξ₀)

/-- Chain rule for slice coordinates of a map through `P`. -/
private theorem sliceA_hasStrictFDerivAt_comp {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀)
    {L : Cfg →L[ℝ] ↥(normalC ξ₀)} (hL : HasStrictFDerivAt (sliceRep ξ₀ hξ₀) L (literalCfg ξ₀))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → Cfg} {f' : E →L[ℝ] Cfg} {x : E}
    (hfx : f x = literalCfg ξ₀) (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (fun p => sliceRep ξ₀ hξ₀ (f p)) (L.comp f') x := by
  have h := hL
  rw [← hfx] at h
  exact h.comp x hf

/-- Analyticity of slice coordinates of a map through `P`. -/
private theorem sliceA_analyticAt_comp {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → Cfg} {x : E}
    (hfx : f x = literalCfg ξ₀) (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun p => sliceRep ξ₀ hξ₀ (f p)) x :=
  (sliceA_analyticAt_rep hξ₀).comp_of_eq hf hfx

/-- The slice-family embedding `(X, e) ↦ (X, 0, e)`. -/
private def sliceA_embed : SliceParam →L[ℝ] PreParam :=
  (ContinuousLinearMap.fst ℝ (Fin 8 → ℝ) (Fin 2 → ℝ)).prod
    ((0 : SliceParam →L[ℝ] (Fin 8 → ℝ)).prod (ContinuousLinearMap.snd ℝ (Fin 8 → ℝ) (Fin 2 → ℝ)))

private theorem sliceA_embed_apply (p : SliceParam) : sliceA_embed p = (p.1, 0, p.2) := rfl

private theorem sliceA_sliceFam_eq {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    sliceFam ξ₀ hξ₀ H = fun p => sliceRep ξ₀ hξ₀ (preMap ξ₀ hξ₀ H (sliceA_embed p)) := rfl

private theorem sliceA_preMap_embed_zero {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    preMap ξ₀ hξ₀ H (sliceA_embed 0) = literalCfg ξ₀ := by
  rw [map_zero]
  exact preMap_zero hξ₀ H

private theorem sliceA_literalPhase_zero (ξ₀ : Fin 4 → ℂ) :
    (fun θ => literalCfg (commonPhase ξ₀ θ)) 0 = literalCfg ξ₀ := by
  show literalCfg (commonPhase ξ₀ 0) = literalCfg ξ₀
  rw [commonPhase_zero]

private theorem sliceA_hasStrictFDerivAt_sliceFam' {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀)
    (H : Fin 4) {L : Cfg →L[ℝ] ↥(normalC ξ₀)}
    (hL : HasStrictFDerivAt (sliceRep ξ₀ hξ₀) L (literalCfg ξ₀)) :
    HasStrictFDerivAt (sliceFam ξ₀ hξ₀ H) (L.comp ((preDer ξ₀ hξ₀ H).comp sliceA_embed)) 0 := by
  rw [sliceA_sliceFam_eq]
  have h := hasStrictFDerivAt_preMap hξ₀ H
  rw [← map_zero sliceA_embed] at h
  exact sliceA_hasStrictFDerivAt_comp hξ₀ hL (sliceA_preMap_embed_zero hξ₀ H)
    (h.comp 0 sliceA_embed.hasStrictFDerivAt)

/-! ## The holes -/

theorem sliceRep_literalCfg {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    sliceRep ξ₀ hξ₀ (literalCfg ξ₀) = 0 := by
  show ((slicePH ξ₀ hξ₀).symm (literalCfg ξ₀)).2 = 0
  rw [slicePH_symm_literalCfg]
  rfl

theorem commonMap_zero {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) : commonMap ξ₀ 0 = literalCfg ξ₀ := by
  show actC (groupChart 0) (literalCfg (commonPhase ξ₀ 0)) = literalCfg ξ₀
  rw [groupChart_zero, actC_one, commonPhase_zero]
  rfl

theorem sliceCommon_zero {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) : sliceCommon ξ₀ hξ₀ 0 = 0 := by
  show sliceRep ξ₀ hξ₀ (literalCfg (commonPhase ξ₀ 0)) = 0
  rw [commonPhase_zero]
  exact sliceRep_literalCfg hξ₀

theorem sliceFam_zero {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) : sliceFam ξ₀ hξ₀ H 0 = 0 := by
  rw [sliceA_sliceFam_eq]
  show sliceRep ξ₀ hξ₀ (preMap ξ₀ hξ₀ H (sliceA_embed 0)) = 0
  rw [sliceA_preMap_embed_zero]
  exact sliceRep_literalCfg hξ₀

/-- **Slice representatives are `G`-invariant near `P`.** For `A ∈ G` near `1` and `y` near `P`,
`y = χ(D) • (P + n)` gives `A • y = χ(inv (A χ(D))) • (P + n)` (group closure and the analytic local
inverse `inv` of the group chart), and uniqueness of `slicePH` preimages on its source gives the same
slice coordinate `n`. -/
theorem exists_sliceRep_invariant {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    ∃ Wg ∈ 𝓝 (1 : CEnd), ∃ Wy ∈ 𝓝 (literalCfg ξ₀), ∀ A ∈ autC ∩ Wg, ∀ y ∈ Wy,
      sliceRep ξ₀ hξ₀ (actC A y) = sliceRep ξ₀ hξ₀ y := by
  obtain ⟨U, W, inv, -, h0U, hWo, h1W, -, -, hinvg, hinvD, hinvan⟩ := exists_groupChart_local
  have hinv1 : inv 1 = 0 := by
    have := hinvD 0 h0U
    rwa [groupChart_zero] at this
  have hT := literalCfg_mem_slicePH_target ξ₀ hξ₀
  have hsymm0 := slicePH_symm_literalCfg ξ₀ hξ₀
  let m : CEnd × Cfg → CEnd := fun z => z.1 * groupChart ((slicePH ξ₀ hξ₀).symm z.2).1
  have hs : ContinuousAt (fun z : CEnd × Cfg => (slicePH ξ₀ hξ₀).symm z.2) (1, literalCfg ξ₀) :=
    ContinuousAt.comp (f := fun z : CEnd × Cfg => z.2) (g := (slicePH ξ₀ hξ₀).symm)
      ((slicePH ξ₀ hξ₀).continuousAt_symm hT) continuous_snd.continuousAt
  have hm : ContinuousAt m (1, literalCfg ξ₀) :=
    continuous_fst.continuousAt.mul
      ((analyticAt_groupChart _).continuousAt.comp (continuous_fst.continuousAt.comp hs))
  have hm1 : m (1, literalCfg ξ₀) = 1 := by
    show 1 * groupChart ((slicePH ξ₀ hξ₀).symm (literalCfg ξ₀)).1 = 1
    rw [hsymm0, Prod.fst_zero, groupChart_zero, one_mul]
  let q : CEnd × Cfg → ↥derC × ↥(normalC ξ₀) := fun z => (inv (m z), ((slicePH ξ₀ hξ₀).symm z.2).2)
  have hq : ContinuousAt q (1, literalCfg ξ₀) :=
    ((hinvan 1 h1W).continuousAt.comp_of_eq hm hm1).prodMk (continuous_snd.continuousAt.comp hs)
  have hq0 : q (1, literalCfg ξ₀) = 0 := by
    show (inv (m (1, literalCfg ξ₀)), ((slicePH ξ₀ hξ₀).symm (literalCfg ξ₀)).2) = 0
    rw [hm1, hinv1, hsymm0]
    rfl
  have hN : {z : CEnd × Cfg | z.2 ∈ (slicePH ξ₀ hξ₀).target ∧ m z ∈ W ∧
      q z ∈ (slicePH ξ₀ hξ₀).source} ∈ 𝓝 ((1 : CEnd), literalCfg ξ₀) := by
    refine Filter.inter_mem ?_ (Filter.inter_mem ?_ ?_)
    · exact continuous_snd.continuousAt.preimage_mem_nhds
        ((slicePH ξ₀ hξ₀).open_target.mem_nhds hT)
    · exact hm.preimage_mem_nhds (hWo.mem_nhds (by rw [hm1]; exact h1W))
    · exact hq.preimage_mem_nhds ((slicePH ξ₀ hξ₀).open_source.mem_nhds
        (by rw [hq0]; exact zero_mem_slicePH_source ξ₀ hξ₀))
  obtain ⟨Wg, hWg, Wy, hWy, hprod⟩ := mem_nhds_prod_iff.1 hN
  refine ⟨Wg, hWg, Wy, hWy, ?_⟩
  rintro A ⟨hA, hAg⟩ y hy
  obtain ⟨hyT, hmW, hqS⟩ := hprod (Set.mk_mem_prod hAg hy)
  have hmaut : m (A, y) ∈ autC := mul_mem_autOf hA (groupChart_mem_autC _)
  obtain ⟨-, hgi⟩ := hinvg _ ⟨hmaut, hmW⟩
  have hey : slicePH ξ₀ hξ₀ (q (A, y)) = actC A y := by
    rw [slicePH_coe]
    show actC (groupChart (inv (m (A, y)))) (literalCfg ξ₀ + ↑((slicePH ξ₀ hξ₀).symm y).2) =
      actC A y
    rw [hgi]
    show actC (A * groupChart ((slicePH ξ₀ hξ₀).symm y).1)
      (literalCfg ξ₀ + ↑((slicePH ξ₀ hξ₀).symm y).2) = actC A y
    rw [actC_mul, ContinuousLinearMap.comp_apply]
    congr 1
    exact (slicePH ξ₀ hξ₀).right_inv hyT
  have hl := (slicePH ξ₀ hξ₀).left_inv hqS
  rw [hey] at hl
  show ((slicePH ξ₀ hξ₀).symm (actC A y)).2 = ((slicePH ξ₀ hξ₀).symm y).2
  rw [hl]

theorem eventually_eq_actC_sliceRep {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    ∀ᶠ y in 𝓝 (literalCfg ξ₀), ∃ D : ↥derC,
      y = actC (groupChart D) (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ y)) := by
  filter_upwards [(slicePH ξ₀ hξ₀).open_target.mem_nhds (literalCfg_mem_slicePH_target ξ₀ hξ₀)]
    with y hy
  exact ⟨((slicePH ξ₀ hξ₀).symm y).1, ((slicePH ξ₀ hξ₀).right_inv hy).symm⟩

theorem analyticAt_sliceFam {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    AnalyticAt ℝ (sliceFam ξ₀ hξ₀ H) 0 := by
  rw [sliceA_sliceFam_eq]
  have h := analyticAt_preMap hξ₀ H
  rw [← map_zero sliceA_embed] at h
  exact sliceA_analyticAt_comp hξ₀ (sliceA_preMap_embed_zero hξ₀ H)
    (h.comp (sliceA_embed.analyticAt 0))

theorem hasStrictFDerivAt_sliceFam {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    HasStrictFDerivAt (sliceFam ξ₀ hξ₀ H) (sliceFamDer ξ₀ hξ₀ H) 0 :=
  (analyticAt_sliceFam hξ₀ H).hasStrictFDerivAt

/-- An `N`-zero direction `(X, e)` of the slice family gives `(-D, X, 0, e) ∈ ker rawDer`, hence
`(X, e) = 0` by `rawDer_eq_zero_iff`. -/
theorem sliceFamDer_injective {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    Function.Injective (sliceFamDer ξ₀ hξ₀ H) := by
  obtain ⟨L, hL, hL0⟩ := sliceA_rep_deriv hξ₀
  have hder : sliceFamDer ξ₀ hξ₀ H = L.comp ((preDer ξ₀ hξ₀ H).comp sliceA_embed) :=
    (sliceA_hasStrictFDerivAt_sliceFam' hξ₀ H hL).hasFDerivAt.fderiv
  refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  rw [hder, ContinuousLinearMap.comp_apply] at hv
  obtain ⟨D, hD⟩ := hL0 _ hv
  have hraw : rawDer ξ₀ hξ₀ H (-D, sliceA_embed v) = 0 := by
    rw [rawDer_apply]
    show orbitMapC ξ₀ ((-D : ↥derC) : CEnd) + preDer ξ₀ hξ₀ H (sliceA_embed v) = 0
    rw [ContinuousLinearMap.comp_apply] at hD
    rw [hD, Submodule.coe_neg, map_neg, neg_add_cancel]
  obtain ⟨k, -, hk⟩ := (rawDer_eq_zero_iff hξ₀ H _).1 hraw
  rw [sliceA_embed_apply] at hk
  have h1 : v.1 = 0 := congrArg Prod.fst hk
  have h2 : v.2 = 0 := congrArg (fun z : PreParam => z.2.2) hk
  exact Prod.ext h1 h2

theorem analyticAt_sliceCommon {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    AnalyticAt ℝ (sliceCommon ξ₀ hξ₀) 0 :=
  sliceA_analyticAt_comp hξ₀ (sliceA_literalPhase_zero ξ₀) (analyticAt_literalPhase hξ₀)

theorem hasStrictFDerivAt_sliceCommon {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    HasStrictFDerivAt (sliceCommon ξ₀ hξ₀) (sliceCommonDer ξ₀ hξ₀) 0 :=
  (analyticAt_sliceCommon hξ₀).hasStrictFDerivAt

/-- An `N`-zero direction `θ` of the common slice family has `phaseDer θ ∈ O`, hence `θ = 0`
(`phase_indep_mod_orbit`). -/
theorem sliceCommonDer_injective {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    Function.Injective (sliceCommonDer ξ₀ hξ₀) := by
  obtain ⟨L, hL, hL0⟩ := sliceA_rep_deriv hξ₀
  have hder : sliceCommonDer ξ₀ hξ₀ = L.comp (phaseDer ξ₀) :=
    (sliceA_hasStrictFDerivAt_comp hξ₀ hL (f := fun θ => literalCfg (commonPhase ξ₀ θ))
      (sliceA_literalPhase_zero ξ₀) (hasStrictFDerivAt_literalPhase hξ₀)).hasFDerivAt.fderiv
  refine (injective_iff_map_eq_zero _).2 fun θ hθ => ?_
  rw [hder, ContinuousLinearMap.comp_apply] at hθ
  obtain ⟨D, hD⟩ := hL0 _ hθ
  have h : orbitMapC ξ₀ ((-D : ↥derC) : CEnd) + phaseDer ξ₀ θ = 0 := by
    rw [hD, Submodule.coe_neg, map_neg, neg_add_cancel]
  exact (phase_indep_mod_orbit hξ₀ _ (-D).2 θ h).2

/-- The common slice germ lies in every slice family germ, through an analytic reparametrization. -/
theorem exists_slice_inclusion {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    ∃ ψ : (Fin 4 → ℝ) → SliceParam, AnalyticAt ℝ ψ 0 ∧ ψ 0 = 0 ∧
      ∀ᶠ θ in 𝓝 (0 : Fin 4 → ℝ), sliceFam ξ₀ hξ₀ H (ψ θ) = sliceCommon ξ₀ hξ₀ θ := by
  obtain ⟨A, k, e, hA, hA0, hAaut, hk, hk0, he, he0, hcomp⟩ := exists_compensation hξ₀ H
  obtain ⟨Wg, hWg, Wy, hWy, hinv⟩ := exists_sliceRep_invariant hξ₀
  refine ⟨fun θ => (k θ, e θ), hk.prod he, ?_, ?_⟩
  · show (k 0, e 0) = 0
    rw [hk0, he0]
    rfl
  have hAev : ∀ᶠ θ in 𝓝 (0 : Fin 4 → ℝ), A θ ∈ Wg :=
    hA.continuousAt.preimage_mem_nhds (by rw [hA0]; exact hWg)
  have hpre : ContinuousAt (fun θ => preMap ξ₀ hξ₀ H (sliceA_embed (k θ, e θ))) 0 := by
    have h1 : ContinuousAt (fun θ => sliceA_embed (k θ, e θ)) 0 :=
      sliceA_embed.continuous.continuousAt.comp (hk.continuousAt.prodMk he.continuousAt)
    have h2 : sliceA_embed (k 0, e 0) = 0 := by
      rw [hk0, he0, ← map_zero sliceA_embed]
      rfl
    exact (analyticAt_preMap hξ₀ H).continuousAt.comp_of_eq h1 h2
  have hpre0 : preMap ξ₀ hξ₀ H (sliceA_embed (k 0, e 0)) = literalCfg ξ₀ := by
    rw [hk0, he0]
    exact sliceA_preMap_embed_zero hξ₀ H
  have hpev : ∀ᶠ θ in 𝓝 (0 : Fin 4 → ℝ), preMap ξ₀ hξ₀ H (sliceA_embed (k θ, e θ)) ∈ Wy :=
    hpre.preimage_mem_nhds (by rw [hpre0]; exact hWy)
  filter_upwards [hAev, hpev] with θ h1 h2
  show sliceRep ξ₀ hξ₀ (preMap ξ₀ hξ₀ H (sliceA_embed (k θ, e θ))) =
    sliceRep ξ₀ hξ₀ (literalCfg (commonPhase ξ₀ θ))
  rw [hcomp θ, ← sliceA_embed_apply (k θ, e θ)]
  exact (hinv _ ⟨hAaut θ, h1⟩ _ h2).symm

/-- The common raw germ lies in every raw family germ, through an analytic reparametrization. -/
theorem exists_common_in_raw {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    ∃ Γ : CommonParam → RawParam62, AnalyticAt ℝ Γ 0 ∧ Γ 0 = 0 ∧
      ∀ᶠ p in 𝓝 (0 : CommonParam), commonMap ξ₀ p = rawMap62 ξ₀ hξ₀ H (Γ p) := by
  obtain ⟨A, k, e, hA, hA0, hAaut, hk, hk0, he, he0, hcomp⟩ := exists_compensation hξ₀ H
  obtain ⟨U, W, inv, -, h0U, hWo, h1W, -, -, hinvg, hinvD, hinvan⟩ := exists_groupChart_local
  have hinv1 : inv 1 = 0 := by
    have := hinvD 0 h0U
    rwa [groupChart_zero] at this
  let m : CommonParam → CEnd := fun p => groupChart p.1 * A p.2
  have hm : AnalyticAt ℝ m 0 :=
    (AnalyticAt.comp (g := groupChart) (f := fun p : CommonParam => p.1)
      (analyticAt_groupChart _) analyticAt_fst).mul
      (AnalyticAt.comp (g := A) (f := fun p : CommonParam => p.2) hA analyticAt_snd)
  have hm0 : m 0 = 1 := by
    show groupChart (0 : CommonParam).1 * A (0 : CommonParam).2 = 1
    rw [Prod.fst_zero, Prod.snd_zero, groupChart_zero, hA0, one_mul]
  refine ⟨fun p => (inv (m p), k p.2, e p.2), ?_, ?_, ?_⟩
  · exact ((hinvan 1 h1W).comp_of_eq hm hm0).prod
      ((AnalyticAt.comp (g := k) (f := fun p : CommonParam => p.2) hk analyticAt_snd).prod
        (AnalyticAt.comp (g := e) (f := fun p : CommonParam => p.2) he analyticAt_snd))
  · show (inv (m 0), k (0 : CommonParam).2, e (0 : CommonParam).2) = 0
    rw [hm0, hinv1, Prod.snd_zero, hk0, he0]
    rfl
  filter_upwards [hm.continuousAt.preimage_mem_nhds (hWo.mem_nhds (by rw [hm0]; exact h1W))]
    with p hp
  have hmaut : m p ∈ autC := mul_mem_autOf (groupChart_mem_autC _) (hAaut _)
  obtain ⟨-, hgi⟩ := hinvg _ ⟨hmaut, hp⟩
  show actC (groupChart p.1) (literalCfg (commonPhase ξ₀ p.2)) =
    actC (groupChart (inv (m p))) (preMap ξ₀ hξ₀ H (k p.2, 0, e p.2))
  rw [hgi, hcomp p.2]
  show _ = actC (groupChart p.1 * A p.2) _
  rw [actC_mul, ContinuousLinearMap.comp_apply]

theorem isGermSubset_common_raw {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    IsGermSubset (commonMap ξ₀) 0 (rawMap62 ξ₀ hξ₀ H) 0 := by
  obtain ⟨Γ, hΓ, hΓ0, hev⟩ := exists_common_in_raw hξ₀ H
  intro V hV
  refine ⟨{p | commonMap ξ₀ p = rawMap62 ξ₀ hξ₀ H (Γ p)} ∩ Γ ⁻¹' V,
    Filter.inter_mem hev (hΓ.continuousAt.preimage_mem_nhds (by rw [hΓ0]; exact hV)), ?_⟩
  rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
  exact ⟨Γ p, hp2, hp1.symm⟩

end CKM.NativeFourFamily

#print axioms CKM.NativeFourFamily.sliceRep_literalCfg
#print axioms CKM.NativeFourFamily.commonMap_zero
#print axioms CKM.NativeFourFamily.sliceCommon_zero
#print axioms CKM.NativeFourFamily.sliceFam_zero
#print axioms CKM.NativeFourFamily.exists_sliceRep_invariant
#print axioms CKM.NativeFourFamily.eventually_eq_actC_sliceRep
#print axioms CKM.NativeFourFamily.analyticAt_sliceFam
#print axioms CKM.NativeFourFamily.hasStrictFDerivAt_sliceFam
#print axioms CKM.NativeFourFamily.sliceFamDer_injective
#print axioms CKM.NativeFourFamily.analyticAt_sliceCommon
#print axioms CKM.NativeFourFamily.hasStrictFDerivAt_sliceCommon
#print axioms CKM.NativeFourFamily.sliceCommonDer_injective
#print axioms CKM.NativeFourFamily.exists_slice_inclusion
#print axioms CKM.NativeFourFamily.exists_common_in_raw
#print axioms CKM.NativeFourFamily.isGermSubset_common_raw

module

public import HTPhaseCompleteNormal

@[expose] public section

/-!
# Good-phase Book/common equivalence onto the actual normal kernel

For every `ξ` with `IsGoodPhase ξ`:

* `bookPhaseEquiv hξ : fixQK ξ × Blocks ≃L[ℝ] tanN ξ`, the concrete map
  `(c, z) ↦ c + Πξ (unpack (phaseV ξ z))` (`bookPhaseEquiv_apply`, `rfl`);
* `bookPhaseKernelEquiv hξ : fixQK ξ × Blocks ≃L[ℝ] normalKernel ξ`, the same ambient vector through the
  accepted `kernelEquivTanN`;
* for every anchor `H`, a constructed parameter equivalence
  `axisParamEquiv hξ H : (Fin 4 → ℝ) × Triple ≃L[ℝ] SliceParam` with
  `sliceFamDer ξ H (axisParamEquiv (θ, u)) = sliceCommonDer ξ θ + Πξ (unpack (phaseV ξ (single H u)))`,
  built from the actual all-unit Cartan compensation (`exists_compensation_cartan`) and the actual common
  derivative; hence `range (sliceFamDer ξ H) = fixQK ξ + Πξ Vξ(axis H)`.

Dimension counts are used only to promote proved injectivity/surjectivity of these explicit maps. The proof is
the fixed-seed proof pattern (BookNativeNormalKernelEquivalence) with every seed-only input replaced by
its phase-native counterpart; no isometry, norm comparison or phase-uniform constant is assumed.
-/

set_option Elab.async false
noncomputable section

namespace Option2.NativeStress.HTPhaseComplete

open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeFourFamily.CartanSuccessor
open Option2.NativeStress.BookHT
open Option2.NativeStress.BookHT.NativeNormalKernelBridge
  (axisParameters axisParameters_cartan axisInverse axisInverse_axisParameters unpackNative
    unpackNative_pack rootFamilyEmbed finrank_triple_real finrank_blocks_real)
open CKM.NativeSliceNormalSplitting (normalKernel kernelEquivTanN kernelEquivTanN_coe)
open scoped Topology

/-! ## 1. The actual common derivative inside each family (all unit phases) -/

/-- From the accepted all-unit Cartan compensation: the actual common slice derivative is the actual family
slice derivative at Cartan-supported left parameters. -/
theorem common_derivative_cartan {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    ∃ (K : (Fin 4 → ℝ) →L[ℝ] (Fin 8 → ℝ)) (E : (Fin 4 → ℝ) →L[ℝ] (Fin 2 → ℝ)),
      (∀ θ m, m ≠ 2 → m ≠ 7 → K θ m = 0) ∧
      ∀ θ, sliceCommonDer ξ hξ θ = sliceFamDer ξ hξ H (K θ, E θ) := by
  obtain ⟨A, k, e, hA, hA0, hAaut, hk, hk0, he, he0, hcartan, hcomp⟩ :=
    exists_compensation_cartan hξ H
  obtain ⟨Wg, hWg, Wy, hWy, hinv⟩ := exists_sliceRep_invariant hξ
  have hAev : ∀ᶠ θ in 𝓝 (0 : Fin 4 → ℝ), A θ ∈ Wg :=
    hA.continuousAt.preimage_mem_nhds (by rw [hA0]; exact hWg)
  have hpre : ContinuousAt (fun θ => preMap ξ hξ H (rootFamilyEmbed (k θ, e θ))) 0 := by
    have h1 : ContinuousAt (fun θ => rootFamilyEmbed (k θ, e θ)) 0 :=
      rootFamilyEmbed.continuous.continuousAt.comp (hk.continuousAt.prodMk he.continuousAt)
    have h2 : rootFamilyEmbed (k 0, e 0) = 0 := by rw [hk0, he0]; rfl
    exact (analyticAt_preMap hξ H).continuousAt.comp_of_eq h1 h2
  have hpre0 : preMap ξ hξ H (rootFamilyEmbed (k 0, e 0)) = literalCfg ξ := by
    rw [hk0, he0, Prod.mk_zero_zero, map_zero, preMap_zero]
  have hpev : ∀ᶠ θ in 𝓝 (0 : Fin 4 → ℝ), preMap ξ hξ H (rootFamilyEmbed (k θ, e θ)) ∈ Wy :=
    hpre.preimage_mem_nhds (by rw [hpre0]; exact hWy)
  have hgerm : (fun θ => sliceFam ξ hξ H (k θ, e θ)) =ᶠ[𝓝 0] sliceCommon ξ hξ := by
    filter_upwards [hAev, hpev] with θ h1 h2
    change sliceRep ξ hξ (preMap ξ hξ H (k θ, 0, e θ)) =
      sliceRep ξ hξ (literalCfg (commonPhase ξ θ))
    rw [hcomp θ]
    exact (hinv _ ⟨hAaut θ, h1⟩ _ h2).symm
  have hψ : HasFDerivAt (fun θ => (k θ, e θ)) ((fderiv ℝ k 0).prod (fderiv ℝ e 0)) 0 :=
    hk.differentiableAt.hasFDerivAt.prodMk he.differentiableAt.hasFDerivAt
  have hf : HasFDerivAt (sliceFam ξ hξ H) (sliceFamDer ξ hξ H) (k 0, e 0) := by
    rw [hk0, he0, Prod.mk_zero_zero]
    exact (hasStrictFDerivAt_sliceFam hξ H).hasFDerivAt
  have hchain : HasFDerivAt (sliceCommon ξ hξ)
      ((sliceFamDer ξ hξ H).comp ((fderiv ℝ k 0).prod (fderiv ℝ e 0))) 0 :=
    (HasFDerivAt.comp (𝕜 := ℝ) (E := Fin 4 → ℝ) (F := SliceParam) (G := ↥(normalC ξ))
      (f := fun θ => (k θ, e θ)) (g := sliceFam ξ hξ H) 0 hf hψ).congr_of_eventuallyEq hgerm.symm
  have hd := hchain.unique (hasStrictFDerivAt_sliceCommon hξ).hasFDerivAt
  refine ⟨fderiv ℝ k 0, fderiv ℝ e 0, fderiv_cartan_support hk hcartan, ?_⟩
  intro θ
  exact (congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] normalC ξ => L θ) hd).symm

/-- The chosen actual compensation derivative (left Cartan part `K`, torus part `E`). -/
def cartanK {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) : (Fin 4 → ℝ) →L[ℝ] (Fin 8 → ℝ) :=
  Classical.choose (common_derivative_cartan hξ H)

def cartanE {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) : (Fin 4 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  Classical.choose (Classical.choose_spec (common_derivative_cartan hξ H))

theorem cartanK_support {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) (θ : Fin 4 → ℝ)
    (m : Fin 8) (h2 : m ≠ 2) (h7 : m ≠ 7) : cartanK hξ H θ m = 0 :=
  (Classical.choose_spec (Classical.choose_spec (common_derivative_cartan hξ H))).1 θ m h2 h7

theorem sliceCommonDer_eq_cartan {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4)
    (θ : Fin 4 → ℝ) :
    sliceCommonDer ξ hξ θ = sliceFamDer ξ hξ H (cartanK hξ H θ, cartanE hξ H θ) :=
  (Classical.choose_spec (Classical.choose_spec (common_derivative_cartan hξ H))).2 θ

/-! ## 2. Off-diagonal axes meet the common tangent only in zero (good phases) -/

theorem offDiagonal_inter_common {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (H : Fin 4)
    (X : Fin 8 → ℝ) (h2 : X 2 = 0) (h7 : X 7 = 0)
    (hcommon : (sliceFamDer ξ hξ.1 H (X, 0) : Cfg) ∈ fixQK ξ) : X = 0 := by
  rw [← range_sliceCommonDer hξ] at hcommon
  obtain ⟨n, ⟨θ, rfl⟩, he⟩ := hcommon
  have heN : sliceCommonDer ξ hξ.1 θ = sliceFamDer ξ hξ.1 H (X, 0) := Subtype.ext he
  have hpair : (X, (0 : Fin 2 → ℝ)) = (cartanK hξ.1 H θ, cartanE hξ.1 H θ) :=
    sliceFamDer_injective hξ.1 H (heN.symm.trans (sliceCommonDer_eq_cartan hξ.1 H θ))
  have hX : X = cartanK hξ.1 H θ := congrArg Prod.fst hpair
  funext m
  by_cases hm2 : m = 2
  · subst m; exact h2
  by_cases hm7 : m = 7
  · subst m; exact h7
  rw [hX]
  exact cartanK_support hξ.1 H θ m hm2 hm7

theorem projBook_axis_mem_fixQ {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (H : Fin 4) (u : Triple) :
    (projBook ξ hξ.1 (Pi.single H u) : Cfg) ∈ fixQ ξ H := by
  rw [← range_sliceFamDer hξ H, projBook_axis]
  exact ⟨_, ⟨(axisParameters H u, 0), rfl⟩, rfl⟩

theorem projBook_axis_inter_common {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (H : Fin 4) (u : Triple)
    (hu : (projBook ξ hξ.1 (Pi.single H u) : Cfg) ∈ fixQK ξ) : u = 0 := by
  rw [projBook_axis] at hu
  have hz := offDiagonal_inter_common hξ H (axisParameters H u)
    (axisParameters_cartan H u).1 (axisParameters_cartan H u).2 hu
  rw [← axisInverse_axisParameters H u, hz]
  ext j
  fin_cases H <;> fin_cases j <;> simp [axisInverse] <;> rfl

/-! ## 3. Each family: common tangent plus its six real Book axes (good phases) -/

theorem fixQK_le_fixQ (ξ : Fin 4 → ℂ) (H : Fin 4) : fixQK ξ ≤ fixQ ξ H := by
  rw [fixQK_eq_iInf]
  exact iInf_le _ H

def familyAmbient {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    (fixQK ξ × Triple) →L[ℝ] Cfg :=
  (fixQK ξ).subtypeL.coprod
    ((tanN ξ).subtypeL.comp ((projBook ξ hξ).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => Triple) H)))

def familyCommonMap {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (H : Fin 4) :
    (fixQK ξ × Triple) →L[ℝ] fixQ ξ H :=
  (familyAmbient hξ.1 H).codRestrict (fixQ ξ H) (by
    rintro ⟨c, u⟩
    exact (fixQ ξ H).add_mem (fixQK_le_fixQ ξ H c.property) (projBook_axis_mem_fixQ hξ H u))

theorem familyCommonMap_coe {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (H : Fin 4) (c : fixQK ξ)
    (u : Triple) :
    (familyCommonMap hξ H (c, u) : Cfg) = (c : Cfg) + (projBook ξ hξ.1 (Pi.single H u) : Cfg) := rfl

theorem familyCommonMap_injective {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (H : Fin 4) :
    Function.Injective (familyCommonMap hξ H) := by
  refine (injective_iff_map_eq_zero _).2 ?_
  rintro ⟨c, u⟩ hcu
  have he : (c : Cfg) + (projBook ξ hξ.1 (Pi.single H u) : Cfg) = 0 := congrArg Subtype.val hcu
  have hc : (projBook ξ hξ.1 (Pi.single H u) : Cfg) ∈ fixQK ξ := by
    rw [eq_neg_of_add_eq_zero_right he]
    exact (fixQK ξ).neg_mem c.property
  have hu := projBook_axis_inter_common hξ H u hc
  subst u
  have hc0 : c = 0 := by
    apply Subtype.ext
    simpa using he
  exact Prod.ext hc0 rfl

theorem familyCommonMap_bijective {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (H : Fin 4) :
    Function.Bijective (familyCommonMap hξ H) := by
  have hd : Module.finrank ℝ (fixQK ξ × Triple) = Module.finrank ℝ (fixQ ξ H) := by
    rw [Module.finrank_prod, finrank_fixQK hξ, finrank_triple_real, finrank_fixQ hξ H]
  exact ⟨familyCommonMap_injective hξ H,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).1 (familyCommonMap_injective hξ H)⟩

/-! ## 4. The joint map and the equivalence (good phases) -/

def commonInclusion (ξ : Fin 4 → ℂ) : fixQK ξ →L[ℝ] tanN ξ :=
  (fixQK ξ).subtypeL.codRestrict (tanN ξ) (fun c => c.property.1.1)

/-- The concrete Book/common map at phase `ξ` (defined at every unit phase). -/
def bookPhaseMap {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) : (fixQK ξ × Blocks) →L[ℝ] tanN ξ :=
  (commonInclusion ξ).coprod (projBook ξ hξ)

theorem bookPhaseMap_coe {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (c : fixQK ξ) (z : Blocks) :
    (bookPhaseMap hξ (c, z) : Cfg) =
      (c : Cfg) + (normalProjXi ξ hξ (unpackNative (phaseV ξ hξ z)) : Cfg) := by
  change (c : Cfg) + (projBook ξ hξ z : Cfg) = _
  rw [projBook_coe]

/-- Joint surjectivity from the accepted total span `⨆ H, fixQ ξ H = tanN ξ`. -/
theorem bookPhaseMap_surjective {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    Function.Surjective (bookPhaseMap hξ.1) := by
  let M : (fixQK ξ × Blocks) →L[ℝ] Cfg := (tanN ξ).subtypeL.comp (bookPhaseMap hξ.1)
  have hspan : tanN ξ ≤ LinearMap.range M.toLinearMap := by
    rw [← iSup_fixQ hξ.1]
    apply iSup_le
    intro H w hw
    obtain ⟨⟨c, u⟩, he⟩ := (familyCommonMap_bijective hξ H).2 ⟨w, hw⟩
    refine ⟨(c, Pi.single H u), ?_⟩
    exact congrArg Subtype.val he
  intro n
  obtain ⟨p, hp⟩ := hspan n.property
  exact ⟨p, Subtype.ext hp⟩

theorem bookPhaseMap_bijective {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    Function.Bijective (bookPhaseMap hξ.1) := by
  have hd : Module.finrank ℝ (fixQK ξ × Blocks) = Module.finrank ℝ (tanN ξ) := by
    rw [Module.finrank_prod, finrank_fixQK hξ, finrank_blocks_real, finrank_tanN hξ]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).2
    (bookPhaseMap_surjective hξ), bookPhaseMap_surjective hξ⟩

/-- **The good-phase equivalence** `fixQK ξ × Blocks ≃L[ℝ] tanN ξ`, the concrete map. -/
def bookPhaseEquiv {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) : (fixQK ξ × Blocks) ≃L[ℝ] tanN ξ :=
  (LinearEquiv.ofBijective (bookPhaseMap hξ.1).toLinearMap
    (bookPhaseMap_bijective hξ)).toContinuousLinearEquiv

theorem bookPhaseEquiv_toContinuousLinearMap {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    (bookPhaseEquiv hξ).toContinuousLinearMap = bookPhaseMap hξ.1 := rfl

/-- The ambient formula `c + Πξ (unpack (Vξ z))`. -/
theorem bookPhaseEquiv_apply {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (c : fixQK ξ) (z : Blocks) :
    (bookPhaseEquiv hξ (c, z) : Cfg) =
      (c : Cfg) + (normalProjXi ξ hξ.1 (unpackNative (phaseV ξ hξ.1 z)) : Cfg) :=
  bookPhaseMap_coe hξ.1 c z

/-- The same equivalence onto the actual normal kernel, through the accepted `kernelEquivTanN`. -/
def bookPhaseKernelEquiv {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    (fixQK ξ × Blocks) ≃L[ℝ] normalKernel ξ :=
  (bookPhaseEquiv hξ).trans (LinearEquiv.toContinuousLinearEquiv (𝕜 := ℝ) (E := ↥(tanN ξ))
    (F := ↥(normalKernel ξ)) (kernelEquivTanN ξ).symm)

theorem bookPhaseKernelEquiv_apply {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (c : fixQK ξ)
    (z : Blocks) :
    (((bookPhaseKernelEquiv hξ (c, z) : normalKernel ξ) : normalC ξ) : Cfg) =
      (c : Cfg) + (normalProjXi ξ hξ.1 (unpackNative (phaseV ξ hξ.1 z)) : Cfg) := by
  rw [← bookPhaseEquiv_apply hξ c z]
  rfl

/-- Phase-dependent bounds, derived from the native maps only (no uniformity claimed). -/
theorem bookPhaseEquiv_bounds {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : fixQK ξ × Blocks,
      ‖bookPhaseEquiv hξ p‖ ≤ C * ‖p‖ ∧ ‖p‖ ≤ C * ‖bookPhaseEquiv hξ p‖ := by
  let A : (fixQK ξ × Blocks) →L[ℝ] tanN ξ := (bookPhaseEquiv hξ).toContinuousLinearMap
  let B : tanN ξ →L[ℝ] (fixQK ξ × Blocks) := (bookPhaseEquiv hξ).symm.toContinuousLinearMap
  have hA := norm_nonneg A
  have hB := norm_nonneg B
  refine ⟨‖A‖ + ‖B‖ + 1, by positivity, fun p => ⟨?_, ?_⟩⟩
  · calc ‖bookPhaseEquiv hξ p‖ = ‖A p‖ := rfl
      _ ≤ ‖A‖ * ‖p‖ := A.le_opNorm p
      _ ≤ (‖A‖ + ‖B‖ + 1) * ‖p‖ := by gcongr; linarith
  · calc ‖p‖ = ‖B (A p)‖ := by
          rw [show B (A p) = p from (bookPhaseEquiv hξ).symm_apply_apply p]
      _ ≤ ‖B‖ * ‖A p‖ := B.le_opNorm _
      _ ≤ (‖A‖ + ‖B‖ + 1) * ‖A p‖ := by gcongr; linarith
      _ = (‖A‖ + ‖B‖ + 1) * ‖bookPhaseEquiv hξ p‖ := rfl

/-! ## 5. Per-axis parameter equivalence with the actual slice families (good phases) -/

/-- Constructed parameter map: `(θ, u) ↦ (cartanK θ + axisParameters H u, cartanE θ)`. -/
def axisParamMap {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    ((Fin 4 → ℝ) × Triple) →L[ℝ] SliceParam :=
  ((cartanK hξ H).comp (ContinuousLinearMap.fst ℝ _ _) +
      (axisLin H).comp (ContinuousLinearMap.snd ℝ _ _)).prod
    ((cartanE hξ H).comp (ContinuousLinearMap.fst ℝ _ _))

theorem axisParamMap_apply {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) (θ : Fin 4 → ℝ)
    (u : Triple) :
    axisParamMap hξ H (θ, u) = (cartanK hξ H θ + axisParameters H u, cartanE hξ H θ) := rfl

/-- **Family/derivative compatibility**: the actual slice-family derivative at the constructed parameters is the
actual common derivative plus the projected Book axis direction (every unit phase). -/
theorem sliceFamDer_axisParamMap {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4)
    (θ : Fin 4 → ℝ) (u : Triple) :
    (sliceFamDer ξ hξ H (axisParamMap hξ H (θ, u)) : Cfg) =
      (sliceCommonDer ξ hξ θ : Cfg) + (normalProjXi ξ hξ (unpackNative (phaseV ξ hξ (Pi.single H u))) : Cfg) := by
  rw [axisParamMap_apply, ← projBook_coe, projBook_axis, sliceCommonDer_eq_cartan hξ H θ,
    show (cartanK hξ H θ + axisParameters H u, cartanE hξ H θ) =
      (cartanK hξ H θ, cartanE hξ H θ) + (axisParameters H u, (0 : Fin 2 → ℝ)) by simp,
    map_add, Submodule.coe_add]

theorem axisParamMap_injective {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (H : Fin 4) :
    Function.Injective (axisParamMap hξ.1 H) := by
  refine (injective_iff_map_eq_zero _).2 ?_
  rintro ⟨θ, u⟩ h0
  have hs := sliceFamDer_axisParamMap hξ.1 H θ u
  rw [h0, map_zero, Submodule.coe_zero, ← projBook_coe] at hs
  have hθmem : (sliceCommonDer ξ hξ.1 θ : Cfg) ∈ fixQK ξ := by
    rw [← range_sliceCommonDer hξ]
    exact ⟨_, ⟨θ, rfl⟩, rfl⟩
  have hm : familyCommonMap hξ H (⟨_, hθmem⟩, u) = 0 := by
    apply Subtype.ext
    rw [familyCommonMap_coe]
    exact hs.symm
  have hp := familyCommonMap_injective hξ H (hm.trans (map_zero _).symm)
  have hu : u = 0 := congrArg Prod.snd hp
  have hθ0 : sliceCommonDer ξ hξ.1 θ = 0 := by
    have := congrArg (fun q => ((q.1 : fixQK ξ) : Cfg)) hp
    exact Subtype.ext this
  have hθ : θ = 0 := sliceCommonDer_injective hξ.1 (hθ0.trans (map_zero _).symm)
  rw [hθ, hu]
  rfl

/-- The constructed per-anchor parameter equivalence. -/
def axisParamEquiv {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (H : Fin 4) :
    ((Fin 4 → ℝ) × Triple) ≃L[ℝ] SliceParam :=
  (LinearEquiv.ofBijective (axisParamMap hξ.1 H).toLinearMap (by
    have hd : Module.finrank ℝ ((Fin 4 → ℝ) × Triple) = Module.finrank ℝ SliceParam := by
      rw [Module.finrank_prod, Module.finrank_prod, finrank_triple_real]
      simp
    exact ⟨axisParamMap_injective hξ H,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).1
        (axisParamMap_injective hξ H)⟩)).toContinuousLinearEquiv

theorem axisParamEquiv_apply {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (H : Fin 4) (θ : Fin 4 → ℝ)
    (u : Triple) :
    axisParamEquiv hξ H (θ, u) = (cartanK hξ.1 H θ + axisParameters H u, cartanE hξ.1 H θ) := rfl

/-- Derivative of the actual slice family read through the constructed parameter equivalence. -/
theorem sliceFamDer_comp_axisParamEquiv {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (H : Fin 4)
    (θ : Fin 4 → ℝ) (u : Triple) :
    (sliceFamDer ξ hξ.1 H (axisParamEquiv hξ H (θ, u)) : Cfg) =
      (sliceCommonDer ξ hξ.1 θ : Cfg) +
        (normalProjXi ξ hξ.1 (unpackNative (phaseV ξ hξ.1 (Pi.single H u))) : Cfg) :=
  sliceFamDer_axisParamMap hξ.1 H θ u

/-- **Range identity**: the common-plus-axis-`H` image is exactly the derivative range of the actual
`sliceFam ξ H` (and equals the accepted `fixQ ξ H`). -/
theorem range_sliceFamDer_eq_common_axis {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (H : Fin 4) :
    (LinearMap.range (sliceFamDer ξ hξ.1 H : SliceParam →ₗ[ℝ] ↥(normalC ξ))).map
        (normalC ξ).subtype =
      LinearMap.range (familyAmbient hξ.1 H).toLinearMap ∧
    LinearMap.range (familyAmbient hξ.1 H).toLinearMap = fixQ ξ H := by
  have h2 : LinearMap.range (familyAmbient hξ.1 H).toLinearMap = fixQ ξ H := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      exact (familyCommonMap hξ H p).property
    · intro w hw
      obtain ⟨p, hp⟩ := (familyCommonMap_bijective hξ H).2 ⟨w, hw⟩
      exact ⟨p, congrArg Subtype.val hp⟩
  exact ⟨(range_sliceFamDer hξ H).trans h2.symm, h2⟩


/-! ## 6. The actual common derivative parametrizes the common tangent; fixQK-form of the axis equivalence -/

/-- `θ ↦ sliceCommonDer ξ θ`, valued in `fixQK ξ` (accepted `range_sliceCommonDer`). -/
def commonParamMap {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) : (Fin 4 → ℝ) →L[ℝ] fixQK ξ :=
  ((normalC ξ).subtypeL.comp (sliceCommonDer ξ hξ.1)).codRestrict (fixQK ξ) (fun θ => by
    rw [← range_sliceCommonDer hξ]
    exact ⟨_, ⟨θ, rfl⟩, rfl⟩)

theorem commonParamMap_bijective {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    Function.Bijective (commonParamMap hξ) := by
  have hinj : Function.Injective (commonParamMap hξ) := by
    intro a b h
    have h1 : ((commonParamMap hξ a : fixQK ξ) : Cfg) = commonParamMap hξ b := congrArg Subtype.val h
    exact sliceCommonDer_injective hξ.1 (Subtype.ext h1)
  have hd : Module.finrank ℝ (Fin 4 → ℝ) = Module.finrank ℝ (fixQK ξ) := by
    rw [finrank_fixQK hξ]; simp
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).1 hinj⟩

/-- The actual common derivative as an equivalence `ℝ⁴ ≃L fixQK ξ`. -/
def commonParamEquiv {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) : (Fin 4 → ℝ) ≃L[ℝ] fixQK ξ :=
  (LinearEquiv.ofBijective (commonParamMap hξ).toLinearMap
    (commonParamMap_bijective hξ)).toContinuousLinearEquiv

theorem commonParamEquiv_apply {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (θ : Fin 4 → ℝ) :
    (commonParamEquiv hξ θ : Cfg) = (sliceCommonDer ξ hξ.1 θ : Cfg) := rfl

/-- The constructed parameter equivalence read with the common tangent itself as first factor. -/
def axisSliceEquiv {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (H : Fin 4) :
    (fixQK ξ × Triple) ≃L[ℝ] SliceParam :=
  ((commonParamEquiv hξ).symm.prodCongr (ContinuousLinearEquiv.refl ℝ Triple)).trans
    (axisParamEquiv hξ H)

theorem sliceFamDer_axisSliceEquiv {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (H : Fin 4)
    (c : fixQK ξ) (u : Triple) :
    (sliceFamDer ξ hξ.1 H (axisSliceEquiv hξ H (c, u)) : Cfg) =
      (c : Cfg) + (normalProjXi ξ hξ.1 (unpackNative (phaseV ξ hξ.1 (Pi.single H u))) : Cfg) := by
  have h := sliceFamDer_comp_axisParamEquiv hξ H ((commonParamEquiv hξ).symm c) u
  rw [← commonParamEquiv_apply hξ, ContinuousLinearEquiv.apply_symm_apply] at h
  exact h


/-! ## 7. Every unit phase (resonant included): per-family injectivity, no exhaustion -/

/-- At every unit phase the constructed parameter map is injective (Cartan support + accepted injectivity). -/
theorem axisParamMap_injective_unit {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    Function.Injective (axisParamMap hξ H) := by
  refine (injective_iff_map_eq_zero _).2 ?_
  rintro ⟨θ, u⟩ h0
  rw [axisParamMap_apply] at h0
  have hX : cartanK hξ H θ + axisParameters H u = 0 := congrArg Prod.fst h0
  have hE : cartanE hξ H θ = 0 := congrArg Prod.snd h0
  have hA : axisParameters H u = 0 := by
    funext m
    by_cases hm2 : m = 2
    · subst m; exact (axisParameters_cartan H u).1
    by_cases hm7 : m = 7
    · subst m; exact (axisParameters_cartan H u).2
    have h1 := congrFun hX m
    rw [Pi.add_apply, cartanK_support hξ H θ m hm2 hm7, zero_add] at h1
    exact h1
  have hu : u = 0 := axisLin_injective H (by rw [axisLin_apply, hA, map_zero])
  have hK : cartanK hξ H θ = 0 := by rw [hA, add_zero] at hX; exact hX
  have hc : sliceCommonDer ξ hξ θ = 0 := by
    rw [sliceCommonDer_eq_cartan hξ H θ, hK, hE, Prod.mk_zero_zero, map_zero]
  have hθ : θ = 0 := sliceCommonDer_injective hξ (hc.trans (map_zero _).symm)
  rw [hθ, hu]
  rfl

/-- At every unit phase, the actual common derivative plus the projected `H`-axis is injective on
`ℝ⁴ × Triple` (its image is the 10-dimensional `range sliceFamDer ξ H`). Joint injectivity over all four
anchors and exhaustion of `tanN ξ` are NOT claimed at resonances (there `dim tanN ξ = 28 + 2 Σ r_H`). -/
theorem common_axis_injective_unit {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    Function.Injective fun p : (Fin 4 → ℝ) × Triple =>
      (sliceCommonDer ξ hξ p.1 : Cfg) +
        (normalProjXi ξ hξ (unpackNative (phaseV ξ hξ (Pi.single H p.2))) : Cfg) := by
  intro p q h
  simp only at h
  rw [← sliceFamDer_axisParamMap, ← sliceFamDer_axisParamMap] at h
  exact axisParamMap_injective_unit hξ H (sliceFamDer_injective hξ H (Subtype.ext h))

end Option2.NativeStress.HTPhaseComplete

#check @Option2.NativeStress.HTPhaseComplete.bookPhaseEquiv
#check @Option2.NativeStress.HTPhaseComplete.bookPhaseEquiv_apply
#check @Option2.NativeStress.HTPhaseComplete.bookPhaseKernelEquiv_apply
#check @Option2.NativeStress.HTPhaseComplete.axisParamEquiv
#check @Option2.NativeStress.HTPhaseComplete.sliceFamDer_comp_axisParamEquiv
#check @Option2.NativeStress.HTPhaseComplete.range_sliceFamDer_eq_common_axis
#print axioms Option2.NativeStress.HTPhaseComplete.common_derivative_cartan
#print axioms Option2.NativeStress.HTPhaseComplete.offDiagonal_inter_common
#print axioms Option2.NativeStress.HTPhaseComplete.familyCommonMap_bijective
#print axioms Option2.NativeStress.HTPhaseComplete.bookPhaseMap_bijective
#print axioms Option2.NativeStress.HTPhaseComplete.bookPhaseEquiv
#print axioms Option2.NativeStress.HTPhaseComplete.bookPhaseEquiv_apply
#print axioms Option2.NativeStress.HTPhaseComplete.bookPhaseKernelEquiv
#print axioms Option2.NativeStress.HTPhaseComplete.bookPhaseKernelEquiv_apply
#print axioms Option2.NativeStress.HTPhaseComplete.bookPhaseEquiv_bounds
#print axioms Option2.NativeStress.HTPhaseComplete.sliceFamDer_axisParamMap
#print axioms Option2.NativeStress.HTPhaseComplete.axisParamEquiv
#print axioms Option2.NativeStress.HTPhaseComplete.sliceFamDer_comp_axisParamEquiv
#print axioms Option2.NativeStress.HTPhaseComplete.range_sliceFamDer_eq_common_axis
#print axioms Option2.NativeStress.HTPhaseComplete.commonParamEquiv
#print axioms Option2.NativeStress.HTPhaseComplete.commonParamEquiv_apply
#print axioms Option2.NativeStress.HTPhaseComplete.axisSliceEquiv
#print axioms Option2.NativeStress.HTPhaseComplete.sliceFamDer_axisSliceEquiv
#print axioms Option2.NativeStress.HTPhaseComplete.axisParamMap_injective_unit
#print axioms Option2.NativeStress.HTPhaseComplete.common_axis_injective_unit

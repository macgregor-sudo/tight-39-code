module

public import BookNativeNormalKernelEquivalence
public import NativeSliceNormalSplitting

@[expose] public section

/-!
# Phase-native normal projection, family direction and Book axes

At an arbitrary unit phase `ξ`:

* `normalProjXi ξ hξ` is the actual projection of `Cfg` onto `normalC ξ` along the actual orbit tangent
  `orbitC ξ` (the same construction as the fixed-seed `normalProjection`, now at `ξ`); it is the normal component
  of the inverse slice differential, so it is the strict derivative of `sliceRep ξ hξ` at `literalCfg ξ`.
* `familyDirection ξ hξ : Blocks →L[ℝ] Cfg` sends a Book block vector `z` to the sum over anchors `H` of the
  actual A5 family derivative `preDer ξ hξ H (X, X, 0)` with `X = axisParameters H (z H)` (the accepted Book axis
  parameters; `X = Y` is simultaneous hidden conjugation, `preVar_same_conjugation`). `phaseV = pack ∘ familyDirection`
  is the packed real direction in `Fin 1053 → ℝ`.
* Each Book axis is, after the actual normal projection, exactly the actual slice-family derivative
  `sliceFamDer ξ hξ H (axisParameters H u, 0)` (`projBook_axis`), with no data computation.

No rank, chart, complementarity, isometry or conditioning premise. Only `IsUnitPhase ξ` is used in this file.
-/

set_option Elab.async false
noncomputable section

namespace Option2.NativeStress.HTPhaseComplete

open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeFourFamily.CartanSuccessor
open Option2.NativeStress.BookHT
open Option2.NativeStress.BookHT.NativeNormalKernelBridge
  (axisParameters axisParameters_cartan axisInverse axisInverse_axisParameters unpackNative
    unpackNative_pack pack_unpackNative rootFamilyEmbed simultaneousParameters)
open scoped Topology

/-! ## 1. The actual normal projection at phase `ξ` -/

/-- Projection onto the actual normal space along the actual orbit tangent, at phase `ξ`. -/
def normalProjXi (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Cfg →L[ℝ] normalC ξ :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Cfg) (F' := ↥(normalC ξ))
    ((normalC ξ).projectionOnto (orbitC ξ) (isCompl_orbitC_normalC ξ hξ).symm)

theorem normalProj_eq_zero_iff {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (x : Cfg) :
    normalProjXi ξ hξ x = 0 ↔ x ∈ orbitC ξ :=
  Submodule.projectionOnto_apply_eq_zero_iff (isCompl_orbitC_normalC ξ hξ).symm

@[simp] theorem normalProj_normal {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (n : normalC ξ) :
    normalProjXi ξ hξ (n : Cfg) = n :=
  Submodule.projectionOnto_apply_left (isCompl_orbitC_normalC ξ hξ).symm n

theorem sub_normalProj_mem_orbit {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (x : Cfg) :
    x - (normalProjXi ξ hξ x : Cfg) ∈ orbitC ξ :=
  Submodule.sub_projection_mem (isCompl_orbitC_normalC ξ hξ).symm x

theorem normalProj_mem_tangent {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) {x : Cfg}
    (hx : x ∈ tangentSpace ξ) : (normalProjXi ξ hξ x : Cfg) ∈ tangentSpace ξ := by
  have h := (tangentSpace ξ).sub_mem hx (klin_orbitC_le hξ (sub_normalProj_mem_orbit hξ x))
  simpa only [sub_sub_cancel] using h

/-- `Πξ` is the normal component of the inverse of the actual slice differential. -/
theorem normalProj_eq_sliceDiff {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) :
    normalProjXi ξ hξ =
      (ContinuousLinearMap.snd ℝ derC (normalC ξ)).comp
        (sliceDiff ξ hξ).symm.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro w
  let p := (sliceDiff ξ hξ).symm w
  have hp : orbitMapC ξ (p.1 : CEnd) + (p.2 : Cfg) = w :=
    (sliceDiff_apply ξ hξ p).symm.trans ((sliceDiff ξ hξ).apply_symm_apply w)
  have ho : normalProjXi ξ hξ (orbitMapC ξ (p.1 : CEnd)) = 0 :=
    (normalProj_eq_zero_iff hξ _).2 ⟨p.1, p.1.property, rfl⟩
  change normalProjXi ξ hξ w = p.2
  rw [← hp, map_add, ho, normalProj_normal, zero_add]

/-- The actual slice coordinate has strict derivative `Πξ` at the literal configuration. -/
theorem sliceRep_hasStrictFDerivAt_normalProjXi (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    HasStrictFDerivAt (sliceRep ξ hξ) (normalProjXi ξ hξ) (literalCfg ξ) := by
  have hi : HasStrictFDerivAt (slicePH ξ hξ).symm
      ((sliceDiff ξ hξ).symm : Cfg →L[ℝ] derC × normalC ξ) (literalCfg ξ) := by
    rw [← sliceChart_zero ξ]
    exact (hasStrictFDerivAt_sliceChart ξ hξ).to_localInverse
  rw [normalProj_eq_sliceDiff hξ]
  exact HasStrictFDerivAt.comp (𝕜 := ℝ) (E := Cfg)
    (F := ↥derC × ↥(normalC ξ)) (G := ↥(normalC ξ)) (literalCfg ξ)
    (hasStrictFDerivAt_snd (𝕜 := ℝ) (E := ↥derC) (F := ↥(normalC ξ))) hi

/-- The actual slice-family derivative is `Πξ` of the actual raw-family derivative. -/
theorem sliceFamDer_eq {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    sliceFamDer ξ hξ H = (normalProjXi ξ hξ).comp ((preDer ξ hξ H).comp rootFamilyEmbed) := by
  have hpre : HasStrictFDerivAt (fun p : SliceParam => preMap ξ hξ H (rootFamilyEmbed p))
      ((preDer ξ hξ H).comp rootFamilyEmbed) 0 := by
    have hp := hasStrictFDerivAt_preMap hξ H
    rw [← map_zero rootFamilyEmbed] at hp
    exact hp.comp 0 rootFamilyEmbed.hasStrictFDerivAt
  have hrep : HasStrictFDerivAt (sliceRep ξ hξ) (normalProjXi ξ hξ)
      (preMap ξ hξ H (rootFamilyEmbed 0)) := by
    simpa only [map_zero, preMap_zero hξ H] using sliceRep_hasStrictFDerivAt_normalProjXi ξ hξ
  exact (hasStrictFDerivAt_sliceFam hξ H).hasFDerivAt.unique
    (HasStrictFDerivAt.comp (𝕜 := ℝ) (E := SliceParam) (F := Cfg) (G := ↥(normalC ξ))
      (f := fun p : SliceParam => preMap ξ hξ H (rootFamilyEmbed p)) 0 hrep hpre).hasFDerivAt

theorem sliceFamDer_apply {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) (p : SliceParam) :
    sliceFamDer ξ hξ H p = normalProjXi ξ hξ (preDer ξ hξ H (p.1, 0, p.2)) := by
  rw [sliceFamDer_eq hξ H]
  rfl

/-! ## 2. Raw-family tangency and the gauge removal -/

/-- Every actual raw-family derivative is tangent to all 2184 original rows. -/
theorem preDer_mem_tangent {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) (p : PreParam) :
    preDer ξ hξ H p ∈ tangentSpace ξ := by
  change fderiv ℝ Option2.NativeStress.AnalyticDerivative.originalF (literalCfg ξ)
    (preDer ξ hξ H p) = 0
  have hD := (hasFDerivAt_originalF (literalCfg ξ)).differentiableAt.hasFDerivAt
  have hP := (hasStrictFDerivAt_preMap hξ H).hasFDerivAt
  have hD' : HasFDerivAt Option2.NativeStress.AnalyticDerivative.originalF
      (fderiv ℝ Option2.NativeStress.AnalyticDerivative.originalF (literalCfg ξ))
      (preMap ξ hξ H 0) := by simpa only [preMap_zero hξ H] using hD
  have hchain := hD'.comp 0 hP
  have hzero : (Option2.NativeStress.AnalyticDerivative.originalF ∘ preMap ξ hξ H) =
      fun _ : PreParam => (0 : Fin 2184 → ℝ) := by
    funext q
    exact originalF_preCfg hξ H (suExp_mem_specialUnitaryGroup q.1)
      (suExp_mem_specialUnitaryGroup q.2.1) _
  rw [hzero] at hchain
  have h := hchain.unique (hasFDerivAt_const (0 : Fin 2184 → ℝ) (0 : PreParam))
  exact congrArg (fun L : PreParam →L[ℝ] (Fin 2184 → ℝ) => L p) h

/-- The simultaneous left/right family derivative, projected at phase `ξ`. -/
def projSimFam (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    (Fin 8 → ℝ) →L[ℝ] normalC ξ :=
  (normalProjXi ξ hξ).comp ((preDer ξ hξ H).comp simultaneousParameters)

theorem projSimFam_apply {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) (X : Fin 8 → ℝ) :
    projSimFam ξ hξ H X = normalProjXi ξ hξ (preDer ξ hξ H (X, X, 0)) := rfl

/-- The actual right parameter is an orbit direction (`orbitMapC_gaugeDer`), so `Πξ` removes it. -/
theorem projSimFam_eq_left {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) (X : Fin 8 → ℝ) :
    projSimFam ξ hξ H X = sliceFamDer ξ hξ H (X, 0) := by
  have hright : normalProjXi ξ hξ (preDer ξ hξ H (0, X, 0)) = 0 := by
    apply (normalProj_eq_zero_iff hξ _).2
    have he := orbitMapC_gaugeDer hξ H X
    rw [eq_neg_of_add_eq_zero_right he]
    exact (orbitC ξ).neg_mem ⟨gaugeDer H X, gaugeDer_mem_derC H X, rfl⟩
  rw [sliceFamDer_apply, projSimFam_apply,
    show (X, X, (0 : Fin 2 → ℝ)) = (X, 0, 0) + (0, X, 0) by simp, map_add, map_add, hright,
    add_zero]

/-- The actual A5 raw-kernel characterization makes each projected family injective (every unit phase). -/
theorem projSimFam_injective {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    Function.Injective (projSimFam ξ hξ H) := by
  refine (injective_iff_map_eq_zero _).2 ?_
  intro X hX
  have hm : preDer ξ hξ H (X, X, 0) ∈ orbitC ξ := (normalProj_eq_zero_iff hξ _).1 hX
  obtain ⟨D, hD, hDvalue⟩ := hm
  have hraw : rawDer ξ hξ H (⟨-D, derC.neg_mem hD⟩, (X, X, 0)) = 0 := by
    rw [rawDer_apply]
    change orbitMapC ξ (-D) + preDer ξ hξ H (X, X, 0) = 0
    have hv : orbitMapC ξ D = preDer ξ hξ H (X, X, 0) := hDvalue
    rw [map_neg, hv, neg_add_cancel]
  obtain ⟨k, -, hparam⟩ := (rawDer_eq_zero_iff hξ H _).1 hraw
  exact congrArg Prod.fst hparam

/-! ## 3. The Book axis parameters as a real-linear map, and the phase direction -/

/-- The accepted Book axis parameters `axisParameters H`, as a real-linear map. -/
def axisLinear (H : Fin 4) : Triple →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun := axisParameters H
  map_add' u v := by
    funext m
    fin_cases H <;> fin_cases m <;> simp [axisParameters] <;> ring
  map_smul' c u := by
    funext m
    fin_cases H <;> fin_cases m <;> simp [axisParameters]

def axisLin (H : Fin 4) : Triple →L[ℝ] (Fin 8 → ℝ) :=
  LinearMap.toContinuousLinearMap (axisLinear H)

@[simp] theorem axisLin_apply (H : Fin 4) (u : Triple) : axisLin H u = axisParameters H u := rfl

theorem axisLin_injective (H : Fin 4) : Function.Injective (axisLin H) := by
  intro u v h
  rw [← axisInverse_axisParameters H u, ← axisInverse_axisParameters H v]
  exact congrArg (axisInverse H) h

/-- **The phase-native Book direction (ambient).** Sum over anchors of the actual A5 family derivative
at the accepted Book axis parameters. -/
def familyDirection (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Blocks →L[ℝ] Cfg :=
  ∑ H : Fin 4, ((preDer ξ hξ H).comp simultaneousParameters).comp
    ((axisLin H).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Triple) H))

theorem familyDirection_apply {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (z : Blocks) :
    familyDirection ξ hξ z =
      ∑ H : Fin 4, preDer ξ hξ H (axisParameters H (z H), axisParameters H (z H), 0) := by
  simp only [familyDirection, FunLike.coe_sum, Finset.sum_apply]
  rfl

theorem familyDirection_single {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) (u : Triple) :
    familyDirection ξ hξ (Pi.single H u) =
      preDer ξ hξ H (axisParameters H u, axisParameters H u, 0) := by
  rw [familyDirection_apply, Finset.sum_eq_single H]
  · simp
  · intro H' _ hH'
    have h0 : (Pi.single H u : Blocks) H' = 0 := by simp [hH']
    have ha : axisParameters H' (0 : Triple) = 0 := by rw [← axisLin_apply, map_zero]
    rw [h0, ha]
    exact (preDer ξ hξ H').map_zero
  · intro h
    exact absurd (Finset.mem_univ H) h

/-- The packed real phase direction `Vξ : Blocks →L[ℝ] (Fin 1053 → ℝ)`. -/
def phaseV (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Blocks →L[ℝ] (Fin 1053 → ℝ) :=
  packCLM.comp (familyDirection ξ hξ)

@[simp] theorem unpack_phaseV {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (z : Blocks) :
    unpackNative (phaseV ξ hξ z) = familyDirection ξ hξ z := by
  change unpackNative (NativePolynomial.PartialAction.pack (familyDirection ξ hξ z)) = _
  exact unpackNative_pack _

theorem familyDirection_mem_tangent {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (z : Blocks) :
    familyDirection ξ hξ z ∈ tangentSpace ξ := by
  rw [familyDirection_apply]
  exact Submodule.sum_mem _ fun H _ => preDer_mem_tangent hξ H _

/-- The projected Book directions, valued in the actual `tanN ξ = T ∩ N` (every unit phase). -/
def projBook (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Blocks →L[ℝ] tanN ξ :=
  ((normalC ξ).subtypeL.comp ((normalProjXi ξ hξ).comp (familyDirection ξ hξ))).codRestrict
    (tanN ξ) (fun z =>
      ⟨normalProj_mem_tangent hξ (familyDirection_mem_tangent hξ z),
        (normalProjXi ξ hξ (familyDirection ξ hξ z)).property⟩)

@[simp] theorem projBook_coe {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (z : Blocks) :
    (projBook ξ hξ z : Cfg) = (normalProjXi ξ hξ (unpackNative (phaseV ξ hξ z)) : Cfg) := by
  rw [unpack_phaseV]
  rfl

/-- **Axis binding.** The `H`-axis Book direction, after `Πξ`, is exactly the actual slice-family
derivative at the left parameter `axisParameters H u` (Cartan components `2, 7` zero). -/
theorem projBook_axis {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) (u : Triple) :
    (projBook ξ hξ (Pi.single H u) : Cfg) =
      (sliceFamDer ξ hξ H (axisParameters H u, 0) : Cfg) := by
  rw [projBook_coe, unpack_phaseV, familyDirection_single, ← projSimFam_apply,
    projSimFam_eq_left]

/-- Per-anchor injectivity of the projected Book axes, at every unit phase (resonant included). -/
theorem projBook_axis_injective {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    Function.Injective fun u : Triple => projBook ξ hξ (Pi.single H u) := by
  intro u v h
  have h1 : (projBook ξ hξ (Pi.single H u) : Cfg) = projBook ξ hξ (Pi.single H v) :=
    congrArg Subtype.val h
  rw [projBook_coe, projBook_coe, unpack_phaseV, unpack_phaseV, familyDirection_single,
    familyDirection_single, ← projSimFam_apply, ← projSimFam_apply] at h1
  exact axisLin_injective H (projSimFam_injective hξ H (Subtype.ext h1))

end Option2.NativeStress.HTPhaseComplete

#check @Option2.NativeStress.HTPhaseComplete.normalProjXi
#check @Option2.NativeStress.HTPhaseComplete.familyDirection
#check @Option2.NativeStress.HTPhaseComplete.phaseV
#check @Option2.NativeStress.HTPhaseComplete.projBook_axis
#print axioms Option2.NativeStress.HTPhaseComplete.normalProj_eq_sliceDiff
#print axioms Option2.NativeStress.HTPhaseComplete.sliceRep_hasStrictFDerivAt_normalProjXi
#print axioms Option2.NativeStress.HTPhaseComplete.sliceFamDer_eq
#print axioms Option2.NativeStress.HTPhaseComplete.preDer_mem_tangent
#print axioms Option2.NativeStress.HTPhaseComplete.projSimFam_eq_left
#print axioms Option2.NativeStress.HTPhaseComplete.projSimFam_injective
#print axioms Option2.NativeStress.HTPhaseComplete.familyDirection_single
#print axioms Option2.NativeStress.HTPhaseComplete.familyDirection_mem_tangent
#print axioms Option2.NativeStress.HTPhaseComplete.projBook
#print axioms Option2.NativeStress.HTPhaseComplete.projBook_coe
#print axioms Option2.NativeStress.HTPhaseComplete.projBook_axis
#print axioms Option2.NativeStress.HTPhaseComplete.projBook_axis_injective

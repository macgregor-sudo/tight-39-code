module

public import BookAxisDistance
public import BookNativeSheetGerms
public import Mathlib.Tactic.Positivity

@[expose] public section

set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.BookHT.SheetDistance
open SheetReduction TangentCoordinates NativeNormalKernelBridge
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeSliceNormalSplitting CKM.NativeSliceImplicitReduction
open QuadraticCertificate.ExactCKMConfiguration Filter Topology

/-- The actual ambient native-coordinate point represented by the reduced chart. -/
def ambientMap (x : KernelModel) : Cfg :=
  literalCfg exactPhases + (reducedEmbedding x : Cfg)

/-- Chosen localized representatives of all four actual native slice families. -/
def actualFamilyUnion (V : Fin 4 → Set SliceParam) : Set Cfg :=
  ⋃ H : Fin 4, (fun p => literalCfg exactPhases +
    (sliceFam exactPhases exactPhases_unit H p : Cfg)) '' V H

theorem ambientMap_C2 : ContDiffAt ℝ 2 ambientMap 0 := by
  let inc : Normal →L[ℝ] Cfg := (normalC exactPhases).subtypeL
  exact contDiffAt_const.add
    (inc.contDiff.contDiffAt.comp 0 reducedEmbedding_C2)

/-- The native germ-image identity places all sufficiently small chart-axis
points in any prescribed neighborhood of the corresponding family parameters. -/
theorem axis_image_near (H : Fin 4) (V : Set SliceParam) (hV : V ∈ 𝓝 0) :
    ∀ᶠ x : KernelModel in 𝓝 0, FourBlock.OnAxis H x.2 →
      ambientMap x ∈ (fun p => literalCfg exactPhases +
        (sliceFam exactPhases exactPhases_unit H p : Cfg)) '' V := by
  obtain ⟨V0, hV0, himage⟩ := reducedPH_family_native_germ H
  have heq := himage (V ∩ V0) (inter_mem hV hV0) Set.inter_subset_right
  rw [Filter.eventuallyEqSet_iff] at heq
  have ht : Tendsto reducedEmbedding (𝓝 (0 : KernelModel)) (𝓝 (0 : Normal)) := by
    simpa only [reducedEmbedding_zero] using reducedEmbedding_C2.continuousAt.tendsto
  have hsource : ∀ᶠ x : KernelModel in 𝓝 0,
      (x, (0 : normalRange exactPhases)) ∈ reducedPH.source :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (reducedPH.open_source.mem_nhds zero_mem_reducedPH_source)
  filter_upwards [ht.eventually heq, hsource] with x hx hs haxis
  have hm : reducedEmbedding x ∈ reducedPH ''
      (reducedPH.source ∩ nativeFamilyBlock (normalRange exactPhases) H) :=
    ⟨(x, 0), ⟨hs, ⟨haxis, rfl⟩⟩, rfl⟩
  obtain ⟨p, hp, hpx⟩ := hx.mpr hm
  refine ⟨p, hp.1, ?_⟩
  change literalCfg exactPhases + (sliceFam exactPhases exactPhases_unit H p : Cfg) =
    literalCfg exactPhases + (reducedEmbedding x : Cfg)
  rw [hpx]

/-- Quantitative chart-to-actual-sheet comparison. Both distances use their
existing norms: native coordinates and the Book outer Pi maximum norm.
The parameter neighborhoods select genuine local sheet representatives. -/
theorem local_sheet_distance (V : Fin 4 → Set SliceParam)
    (hV : ∀ H, V H ∈ 𝓝 0) :
    ∃ r L : ℝ, 0 < r ∧ 0 < L ∧
      ∀ (c : Common) (z : Blocks), ‖c‖ < r → ‖z‖ < r →
        ((c, z), (0 : normalRange exactPhases)) ∈ reducedPH.source ∧
        Metric.infDist (ambientMap (c, z)) (actualFamilyUnion V) ≤
          L * Metric.infDist z axisUnion := by
  have hd := ambientMap_C2.hasStrictFDerivAt (by norm_num)
  obtain ⟨K, U, hU, hLip⟩ := hd.exists_lipschitzOnWith
  have hfamily : ∀ᶠ x : KernelModel in 𝓝 0, ∀ H : Fin 4,
      FourBlock.OnAxis H x.2 → ambientMap x ∈
        (fun p => literalCfg exactPhases +
          (sliceFam exactPhases exactPhases_unit H p : Cfg)) '' V H :=
    Filter.eventually_all.mpr fun H => axis_image_near H (V H) (hV H)
  have hsource : ∀ᶠ x : KernelModel in 𝓝 0,
      (x, (0 : normalRange exactPhases)) ∈ reducedPH.source :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (reducedPH.open_source.mem_nhds zero_mem_reducedPH_source)
  have hU' : ∀ᶠ x : KernelModel in 𝓝 0, x ∈ U := hU
  have hnear := hU'.and (hfamily.and hsource)
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r, (K : ℝ) + 1, hr, by positivity, ?_⟩
  intro c z hc hz
  obtain ⟨H, hnorm, hdist⟩ := exists_nearest_axis z
  let w : Blocks := Pi.single H (z H)
  have hx : (c, z) ∈ U ∧ (∀ H : Fin 4, FourBlock.OnAxis H z →
      ambientMap (c, z) ∈ (fun p => literalCfg exactPhases +
        (sliceFam exactPhases exactPhases_unit H p : Cfg)) '' V H) ∧
      ((c, z), (0 : normalRange exactPhases)) ∈ reducedPH.source :=
    hrU (by simpa only [Metric.mem_ball, dist_zero_right, Prod.norm_mk] using max_lt hc hz)
  have hy : (c, w) ∈ U ∧ (∀ H : Fin 4, FourBlock.OnAxis H w →
      ambientMap (c, w) ∈ (fun p => literalCfg exactPhases +
        (sliceFam exactPhases exactPhases_unit H p : Cfg)) '' V H) ∧
      ((c, w), (0 : normalRange exactPhases)) ∈ reducedPH.source :=
    hrU (by simpa only [Metric.mem_ball, dist_zero_right, Prod.norm_mk] using
      max_lt hc (lt_of_le_of_lt hnorm hz))
  have hw : FourBlock.OnAxis H w := by
    intro J hJ
    simp [w, hJ]
  have hm : ambientMap (c, w) ∈ actualFamilyUnion V :=
    Set.mem_iUnion.mpr ⟨H, hy.2.1 H hw⟩
  have hxy : ‖((c, z) : KernelModel) - (c, w)‖ = Metric.infDist z axisUnion := by
    change max ‖c - c‖ ‖z - w‖ = _
    rw [sub_self, norm_zero, max_eq_right (norm_nonneg _)]
    exact hdist
  have hb := (lipschitzOnWith_iff_norm_sub_le.mp hLip) hx.1 hy.1
  rw [hxy] at hb
  refine ⟨hx.2.2, (Metric.infDist_le_dist_of_mem hm).trans ?_⟩
  rw [dist_eq_norm]
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) Metric.infDist_nonneg)

/-- The corresponding bound to the union of the full parametrized families. -/
theorem full_family_distance :
    ∃ r L : ℝ, 0 < r ∧ 0 < L ∧
      ∀ (c : Common) (z : Blocks), ‖c‖ < r → ‖z‖ < r →
        ((c, z), (0 : normalRange exactPhases)) ∈ reducedPH.source ∧
        Metric.infDist (ambientMap (c, z))
          (actualFamilyUnion (fun _ => Set.univ)) ≤ L * Metric.infDist z axisUnion :=
  local_sheet_distance (fun _ => Set.univ) (fun _ => Filter.univ_mem)

end Option2.NativeStress.BookHT.SheetDistance

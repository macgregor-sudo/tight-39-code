module

public import NativePhaseEuclideanCriterion
public import BookAxisDistance

@[expose] public section

/-! Local Lipschitz transfer to the four actual good-phase native families.
Parameter neighborhoods remain arbitrary; no ambient exhaustion is assumed. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.PhaseSheetDistance
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeSliceNormalSplitting CKM.NativeSliceImplicitReduction
open BookHT BookHT.SheetDistance HTPhaseComplete PhaseSheetChart PhaseRangeReduction Filter Topology
variable {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)

def ambientMap (x : KernelModel ξ) : Cfg := PhaseReducedHStress.nativeEmbedding hξ x
def actualFamilyUnion (V : Fin 4 → Set SliceParam) : Set Cfg :=
  ⋃ i : Fin 4, (fun p => literalCfg ξ + (sliceFam ξ hξ.1 i p : Cfg)) '' V i

theorem ambientMap_C2 : ContDiffAt ℝ 2 (ambientMap hξ) 0 :=
  PhaseReducedHStress.nativeEmbedding_C2 hξ

theorem axis_image_near (i : Fin 4) (V : Set SliceParam) (hV : V ∈ 𝓝 0) :
    ∀ᶠ x : KernelModel ξ in 𝓝 0, FourBlock.OnAxis i x.2 →
      ambientMap hξ x ∈ (fun p => literalCfg ξ + (sliceFam ξ hξ.1 i p : Cfg)) '' V := by
  have hc : Continuous (fun x : KernelModel ξ => (x.1,x.2 i)) :=
    continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)
  have ht : Tendsto (fun x : KernelModel ξ => (x.1,x.2 i)) (𝓝 0) (𝓝 0) := by
    simpa only [Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,Prod.mk_zero_zero] using hc.continuousAt.tendsto (x := 0)
  have hp : Tendsto (familyParam hξ i) (𝓝 0) (𝓝 0) := by
    simpa only [familyParam_zero] using (familyParam_analytic hξ i).continuousAt.tendsto
  filter_upwards [ht.eventually (eliminated_family_germ hξ i), ht.eventually (hp.eventually hV)] with x hx hv ha
  have he : Pi.single i (x.2 i) = x.2 := by
    ext j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj,ha j hj]
  refine ⟨familyParam hξ i (x.1,x.2 i),hv,?_⟩
  change literalCfg ξ + (familySheet hξ i (x.1,x.2 i) : Cfg) =
    literalCfg ξ + (reducedEmbedding hξ x : Cfg)
  simpa only [he,Prod.mk.eta] using congrArg (fun n : Normal ξ => literalCfg ξ + (n : Cfg)) hx.symm

/-- Quantitative chart-to-actual-sheet comparison. Both distances use their
existing norms: native coordinates and the Book outer Pi maximum norm.
The parameter neighborhoods select genuine local sheet representatives. -/
theorem local_sheet_distance (V : Fin 4 → Set SliceParam)
    (hV : ∀ H, V H ∈ 𝓝 0) :
    ∃ r L : ℝ, 0 < r ∧ 0 < L ∧
      ∀ (c : Common ξ) (z : Blocks), ‖c‖ < r → ‖z‖ < r →
        ((c, z), (0 : normalRange ξ)) ∈ (reducedPH hξ).source ∧
        Metric.infDist ((ambientMap hξ) (c, z)) ((actualFamilyUnion hξ) V) ≤
          L * Metric.infDist z axisUnion := by
  have hd := (ambientMap_C2 hξ).hasStrictFDerivAt (by norm_num)
  obtain ⟨K, U, hU, hLip⟩ := hd.exists_lipschitzOnWith
  have hfamily : ∀ᶠ x : KernelModel ξ in 𝓝 0, ∀ H : Fin 4,
      FourBlock.OnAxis H x.2 → (ambientMap hξ) x ∈
        (fun p => literalCfg ξ +
          (sliceFam ξ hξ.1 H p : Cfg)) '' V H :=
    Filter.eventually_all.mpr fun H => (axis_image_near hξ) H (V H) (hV H)
  have hsource : ∀ᶠ x : KernelModel ξ in 𝓝 0,
      (x, (0 : normalRange ξ)) ∈ (reducedPH hξ).source :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      ((reducedPH hξ).open_source.mem_nhds (zero_mem_reducedPH_source hξ))
  have hU' : ∀ᶠ x : KernelModel ξ in 𝓝 0, x ∈ U := hU
  have hnear := hU'.and (hfamily.and hsource)
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r, (K : ℝ) + 1, hr, by positivity, ?_⟩
  intro c z hc hz
  obtain ⟨H, hnorm, hdist⟩ := exists_nearest_axis z
  let w : Blocks := Pi.single H (z H)
  have hx : (c, z) ∈ U ∧ (∀ H : Fin 4, FourBlock.OnAxis H z →
      (ambientMap hξ) (c, z) ∈ (fun p => literalCfg ξ +
        (sliceFam ξ hξ.1 H p : Cfg)) '' V H) ∧
      ((c, z), (0 : normalRange ξ)) ∈ (reducedPH hξ).source :=
    hrU (by simpa only [Metric.mem_ball, dist_zero_right, Prod.norm_mk] using max_lt hc hz)
  have hy : (c, w) ∈ U ∧ (∀ H : Fin 4, FourBlock.OnAxis H w →
      (ambientMap hξ) (c, w) ∈ (fun p => literalCfg ξ +
        (sliceFam ξ hξ.1 H p : Cfg)) '' V H) ∧
      ((c, w), (0 : normalRange ξ)) ∈ (reducedPH hξ).source :=
    hrU (by simpa only [Metric.mem_ball, dist_zero_right, Prod.norm_mk] using
      max_lt hc (lt_of_le_of_lt hnorm hz))
  have hw : FourBlock.OnAxis H w := by
    intro J hJ
    simp [w, hJ]
  have hm : (ambientMap hξ) (c, w) ∈ (actualFamilyUnion hξ) V :=
    Set.mem_iUnion.mpr ⟨H, hy.2.1 H hw⟩
  have hxy : ‖((c, z) : KernelModel ξ) - (c, w)‖ = Metric.infDist z axisUnion := by
    change max ‖c - c‖ ‖z - w‖ = _
    rw [sub_self, norm_zero, max_eq_right (norm_nonneg _)]
    exact hdist
  have hb := (lipschitzOnWith_iff_norm_sub_le.mp hLip) hx.1 hy.1
  rw [hxy] at hb
  refine ⟨hx.2.2, (Metric.infDist_le_dist_of_mem hm).trans ?_⟩
  rw [dist_eq_norm]
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) Metric.infDist_nonneg)


end Option2.NativeStress.PhaseSheetDistance
#print axioms Option2.NativeStress.PhaseSheetDistance.local_sheet_distance

module

public import NativePhaseReducedQuadratic
public import BookNativePositiveKernel
public import BookNativeEuclideanHStress
public import SupportedStressCriterionV3

@[expose] public section

/-! The supported-stress criterion on the actual good-phase reduced residual.
The Euclidean representation is used only for orthogonal Book blocks; the
original residual, nonlinear embedding and phase-dependent neighborhoods remain. -/
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Option2.NativeStress.PhaseEuclideanCriterion
open CKM.NativeFourFamily CKM.NativeFirstOrder CKM.NativeSliceImplicitReduction CKM.NativeGroupSlice CKM.NativeSliceNormalSplitting
open BookHT BookOrthogonal HTPhaseComplete PhaseSheetChart PhaseRangeReduction PhaseReducedQuadratic
open scoped Topology BigOperators InnerProductSpace ContDiff
variable {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)

abbrev EuclideanModel (ξ : Fin 4 → ℂ) := Common ξ × E
def coordinates : EuclideanModel ξ →L[ℝ] KernelModel ξ :=
  (ContinuousLinearMap.fst ℝ (Common ξ) E).prod
    (toBlocks.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ (Common ξ) E))
def fE (p : EuclideanModel ξ) : Residual := sheetResidual hξ (coordinates p)
def embeddingE (p : EuclideanModel ξ) : Cfg := PhaseReducedHStress.nativeEmbedding hξ (coordinates p)
theorem fE_original : fE hξ = AnalyticDerivative.originalF ∘ embeddingE hξ := rfl

theorem fE_C2 : ContDiffAt ℝ 2 (fE hξ) 0 := by
  have hf : ContDiffAt ℝ 2 (sheetResidual hξ) (coordinates (ξ := ξ) 0) := by
    simpa only [map_zero] using sheetResidual_C2 hξ
  exact hf.comp 0 (coordinates (ξ := ξ)).contDiff.contDiffAt

theorem quadratic_fE (x : E) : SupportedStress.transverseQuadraticPart (fE hξ) x =
    reducedQuadratic hξ (toBlocks x) := by
  have h := SupportedStress.ReducedQuadratic.second_comp_linear (sheetResidual hξ)
    (coordinates (ξ := ξ)) (sheetResidual_C2 hξ) ((0 : Common ξ),x) ((0 : Common ξ),x)
  change (1/2 : ℝ) • fderiv ℝ (fderiv ℝ (sheetResidual hξ ∘ coordinates)) 0 (0,x) (0,x) = _
  rw [h]
  rfl

theorem fE_axis_zero_near (i : Fin 4) :
    ∀ᶠ p : EuclideanModel ξ in 𝓝 0, p.2 ∈ W i → fE hξ p = 0 := by
  have hc : Continuous (fun p : EuclideanModel ξ => (p.1,toBlocks p.2 i)) :=
    continuous_fst.prodMk ((continuous_apply i).comp (toBlocks.continuous.comp continuous_snd))
  have ht : Filter.Tendsto (fun p : EuclideanModel ξ => (p.1,toBlocks p.2 i))
      (𝓝 0) (𝓝 (0 : Common ξ × Triple)) := by
    simpa only [Prod.fst_zero,Prod.snd_zero,map_zero,Pi.zero_apply,Prod.mk_zero_zero]
      using hc.continuousAt.tendsto (x := 0)
  filter_upwards [ht.eventually (sheetResidual_family_zero hξ i)] with p hp hx
  have ha := (mem_W_iff_onAxis i p.2).mp hx
  have he : Pi.single i (toBlocks p.2 i) = toBlocks p.2 := by
    ext j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj,ha j hj]
  change sheetResidual hξ (p.1,toBlocks p.2) = 0
  simpa only [he] using hp

theorem criterion_neighborhood :
    ∃ U : Set (EuclideanModel ξ), IsOpen U ∧ (0 : EuclideanModel ξ) ∈ U ∧
      ContDiffOn ℝ 2 (fE hξ) U ∧
      (∀ (i : Fin 4) (c : Common ξ) (x : E), (c,x) ∈ U → x ∈ W i → fE hξ (c,x) = 0) ∧
      (∀ p ∈ U, (coordinates p,(0 : normalRange ξ)) ∈ (reducedPH hξ).source) ∧
      (∀ p ∈ U, rangeProjection ξ (fE hξ p) = 0) := by
  have hc2 := (fE_C2 hξ).eventually (by norm_num)
  have haxes : ∀ᶠ p : EuclideanModel ξ in 𝓝 0, ∀ i : Fin 4, p.2 ∈ W i → fE hξ p = 0 :=
    Filter.eventually_all.mpr (fE_axis_zero_near hξ)
  have hc : Continuous (fun p : EuclideanModel ξ => (coordinates p,(0 : normalRange ξ))) :=
    (coordinates (ξ := ξ)).continuous.prodMk continuous_const
  have ht : Filter.Tendsto (fun p : EuclideanModel ξ => (coordinates p,(0 : normalRange ξ)))
      (𝓝 0) (𝓝 0) := by
    simpa only [map_zero,Prod.mk_zero_zero] using hc.continuousAt.tendsto (x := 0)
  have hs := ht.eventually ((reducedPH hξ).open_source.mem_nhds (zero_mem_reducedPH_source hξ))
  obtain ⟨U,hU,hUo,hU0⟩ := mem_nhds_iff.mp (hc2.and (haxes.and hs))
  refine ⟨U,hUo,hU0,fun p hp => (hU hp).1.contDiffWithinAt,
    fun i c x hp hx => (hU hp).2.1 i hx,fun p hp => (hU hp).2.2,?_⟩
  intro p hp
  exact reducedEmbedding_range_zero hξ (coordinates p) (hU hp).2.2.1

theorem quadratic_zero_cone (x : E) : SupportedStress.transverseQuadraticPart (fE hξ) x = 0 ↔
    x ∈ SupportedStress.blockUnion W := by
  rw [quadratic_fE,reducedQuadratic_zero_cone]
  exact (mem_blockUnion_iff x).symm

theorem quadratic_contDiff : ContDiff ℝ ∞ (SupportedStress.transverseQuadraticPart (fE hξ)) := by
  let B := fderiv ℝ (fderiv ℝ (fE hξ)) (0 : EuclideanModel ξ)
  have hi : ContDiff ℝ ∞ (fun x : E => ((0 : Common ξ),x)) := contDiff_const.prodMk contDiff_id
  change ContDiff ℝ ∞ (fun x : E => (1/2 : ℝ) • B (0,x) (0,x))
  exact ((B.contDiff.comp hi).clm_apply hi).const_smul (1/2 : ℝ)

theorem contraction_kernel (ell : Residual →L[ℝ] Blocks) (Q : Blocks → Blocks) (w n : E)
    (hd : DifferentiableAt ℝ Q (toBlocks w))
    (he : ell ∘ SupportedStress.transverseQuadraticPart (fE hξ) = Q ∘ toBlocks)
    (hk : fderiv ℝ (SupportedStress.transverseQuadraticPart (fE hξ)) w n = 0) :
    fderiv ℝ Q (toBlocks w) (toBlocks n) = 0 := by
  have hh := congrArg (fun g : E → Blocks => fderiv ℝ g w n) he
  rw [fderiv_comp w ell.differentiableAt
      ((quadratic_contDiff hξ).differentiable (by simp)).differentiableAt,
    fderiv_comp w hd toBlocks.differentiableAt,
    ContinuousLinearMap.fderiv,ContinuousLinearEquiv.fderiv] at hh
  change ell (fderiv ℝ (SupportedStress.transverseQuadraticPart (fE hξ)) w n) =
    fderiv ℝ Q (toBlocks w) (toBlocks n) at hh
  rw [hk,map_zero] at hh
  exact hh.symm

theorem derivative_kernel_to_polar (w n : E)
    (hk : fderiv ℝ (SupportedStress.transverseQuadraticPart (fE hξ)) w n = 0) :
    QuadraticMap.polar H (toBlocks w) (toBlocks n) = 0 ∧
      QuadraticMap.polar T (toBlocks w) (toBlocks n) = 0 := by
  have hH : residualHxi ξ hξ.1 ∘ SupportedStress.transverseQuadraticPart (fE hξ) = H ∘ toBlocks := by
    funext x; simp only [Function.comp_apply,quadratic_fE,H_reduced]
  have hT : residualTxi ξ hξ.1 ∘ SupportedStress.transverseQuadraticPart (fE hξ) = T ∘ toBlocks := by
    funext x; simp only [Function.comp_apply,quadratic_fE,T_reduced]
  constructor
  · have h := contraction_kernel hξ _ H w n (contDiff_H.differentiable (by simp)).differentiableAt hH hk
    rwa [fderiv_H_apply] at h
  · have h := contraction_kernel hξ _ T w n (contDiff_T.differentiable (by simp)).differentiableAt hT hk
    rwa [fderiv_T_apply] at h

def axisCoordinates (i : Fin 4) : (Common ξ × W i) →L[ℝ] (Common ξ × Triple) :=
  (ContinuousLinearMap.fst ℝ (Common ξ) (W i)).prod
    ((ContinuousLinearMap.proj i : Blocks →L[ℝ] Triple).comp
      (toBlocks.toContinuousLinearMap.comp ((W i).subtypeL.comp
        (ContinuousLinearMap.snd ℝ (Common ξ) (W i)))))
def axisEmbedding (i : Fin 4) : (Common ξ × W i) →L[ℝ] EuclideanModel ξ :=
  (ContinuousLinearMap.fst ℝ (Common ξ) (W i)).prod
    ((W i).subtypeL.comp (ContinuousLinearMap.snd ℝ (Common ξ) (W i)))
def realFieldE (i : Fin 4) (w : W i) (p : Common ξ × W i) : Residual →L[ℝ] ℝ :=
  PhaseReducedHStress.realField hξ i (toBlocks (w : E)) (axisCoordinates i p)

set_option maxHeartbeats 400000 in
theorem positive_base_field (i : Fin 4) (w : W i) (hw : ‖w‖ = 1) (n : E)
    (hn : n ∈ (W i).orthogonal) (hne : n ≠ 0)
    (hk : fderiv ℝ (SupportedStress.transverseQuadraticPart (fE hξ)) (w : E) n = 0) :
    0 < realFieldE hξ i w 0 (SupportedStress.transverseQuadraticPart (fE hξ) n) := by
  have hp := derivative_kernel_to_polar hξ (w : E) n hk
  have hw0 : toBlocks (w : E) ≠ 0 := by
    intro hz
    have hu := (PositiveKernel.norm_toBlocks_on_W i (w : E) w.property).trans hw
    rw [hz,Pi.zero_apply,norm_zero] at hu
    norm_num at hu
  have hn0 : toBlocks n ≠ 0 := fun hz => hne (toBlocks.injective (by simpa only [map_zero] using hz))
  have hpos := kernel_stress_pos i (toBlocks (w : E)) (toBlocks n)
    ((mem_W_iff_onAxis i (w : E)).mp w.property)
    (PositiveKernel.orthogonal_block_zero i n hn) hw0 hn0 hp.1 hp.2
  have hinner (u v : Triple) : ⟪u,v⟫_ℝ = (⟪u,v⟫_ℂ).re := by
    simp only [PiLp.inner_apply,Complex.re_sum,Complex.inner,RCLike.inner_apply]
  rw [hinner] at hpos
  change 0 < PhaseReducedHStress.realField hξ i (toBlocks (w : E)) (axisCoordinates i 0) _
  rw [map_zero,PhaseReducedHStress.realField_zero_apply,quadratic_fE]
  have he (a : Fin 3) : (∑ r : Fin 2184, ellH ξ hξ.1 i a r *
      (reducedQuadratic hξ (toBlocks n) r : ℂ)) = (H (toBlocks n) i).ofLp a := by
    rw [← residualOf_apply]
    exact congrArg (fun z : Blocks => (z i).ofLp a) (H_reduced hξ (toBlocks n))
  simp only [he]
  simpa only [PiLp.inner_apply,RCLike.inner_apply, starRingEnd_apply, mul_comm] using hpos

theorem criterion_field (i : Fin 4) (w : W i) (U : Set (EuclideanModel ξ))
    (hU : IsOpen U) (h0 : (0 : EuclideanModel ξ) ∈ U) :
    ∃ V : Set (Common ξ × W i), IsOpen V ∧ (0 : Common ξ × W i) ∈ V ∧
      (∀ p ∈ V, (p.1,(p.2 : E)) ∈ U) ∧ ContinuousOn (realFieldE hξ i w) V ∧
      (∀ p ∈ V, ∀ n : E, realFieldE hξ i w p
        (fderiv ℝ (fE hξ) (p.1,(p.2 : E)) (0,n)) = 0) := by
  obtain ⟨VB,hB,hB0,-,hc,ha⟩ := PhaseReducedHStress.supported_stress_field hξ i
    (toBlocks (w : E)) Set.univ isOpen_univ (Set.mem_univ _)
  have hu : ∀ᶠ p in 𝓝 (0 : Common ξ × W i), axisEmbedding i p ∈ U :=
    (axisEmbedding i).continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hU.mem_nhds h0)
  have ht : Filter.Tendsto ((coordinates (ξ := ξ)).comp (axisEmbedding i))
      (𝓝 (0 : Common ξ × W i)) (𝓝 0) := by
    simpa only [map_zero] using ((coordinates (ξ := ξ)).comp (axisEmbedding i)).continuous.continuousAt.tendsto (x := 0)
  have hd := ht.eventually ((sheetResidual_C2 hξ).eventually (by norm_num))
  obtain ⟨V0,hV0,hVo,hVz⟩ := mem_nhds_iff.mp (hu.and hd)
  let V := V0 ∩ (axisCoordinates (ξ := ξ) i) ⁻¹' VB
  refine ⟨V,hVo.inter (hB.preimage (axisCoordinates i).continuous),
    ⟨hVz,by change axisCoordinates i 0 ∈ VB; simpa only [map_zero] using hB0⟩,
    fun p hp => (hV0 hp.1).1,?_,?_⟩
  · exact hc.comp (axisCoordinates i).continuous.continuousOn (fun p hp => hp.2)
  · intro p hp n
    have hs := (hV0 hp.1).2
    change ContDiffAt ℝ 2 (sheetResidual hξ) (coordinates (p.1,(p.2 : E))) at hs
    change PhaseReducedHStress.realField hξ i (toBlocks (w : E)) (axisCoordinates i p)
      (fderiv ℝ (sheetResidual hξ ∘ coordinates) (p.1,(p.2 : E)) (0,n)) = 0
    rw [fderiv_comp _ (hs.differentiableAt (by norm_num)) (coordinates (ξ := ξ)).differentiableAt,
      (coordinates (ξ := ξ)).fderiv]
    change PhaseReducedHStress.realField hξ i (toBlocks (w : E)) (axisCoordinates i p)
      (fderiv ℝ (sheetResidual hξ) (p.1,toBlocks (p.2 : E)) (0,toBlocks n)) = 0
    rw [EuclideanHStress.toBlocks_axis i p.2]
    exact ha (axisCoordinates i p) hp.2 (0,toBlocks n)

/-- Local reduced bound and exact zero set, with no H/T, stress, cone or
positivity hypothesis. Constants and neighborhoods may depend on the good phase. -/
theorem local_reduced_bound : ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
    ∀ (c : Common ξ) (u : E), ‖c‖ < r → ‖u‖ < r →
      (coordinates (c,u),(0 : normalRange ξ)) ∈ (reducedPH hξ).source ∧
      rangeProjection ξ (fE hξ (c,u)) = 0 ∧
      Metric.infDist u (SupportedStress.blockUnion W)^2 ≤ M * ‖fE hξ (c,u)‖ ∧
      (fE hξ (c,u) = 0 ↔ u ∈ SupportedStress.blockUnion W) := by
  obtain ⟨U,hU,h0,hf,hs,hsource,hrange⟩ := criterion_neighborhood hξ
  have hstress : ∀ (i : Fin 4) (w : W i), ‖w‖ = 1 →
      ∃ V : Set (Common ξ × W i), IsOpen V ∧ (0 : Common ξ × W i) ∈ V ∧
        (∀ p ∈ V, (p.1,(p.2 : E)) ∈ U) ∧
        ∃ ell : Common ξ × W i → Residual →L[ℝ] ℝ, ContinuousOn ell V ∧
          (∀ p ∈ V, ∀ n ∈ (W i).orthogonal,
            ell p (fderiv ℝ (fE hξ) (p.1,(p.2 : E)) (0,n)) = 0) ∧
          (∀ v ∈ (W i).orthogonal, v ≠ 0 →
            fderiv ℝ (SupportedStress.transverseQuadraticPart (fE hξ)) (w : E) v = 0 →
            0 < ell 0 (SupportedStress.transverseQuadraticPart (fE hξ) v)) := by
    intro i w hw
    obtain ⟨V,hV,hV0,hVU,hc,ha⟩ := criterion_field hξ i w U hU h0
    exact ⟨V,hV,hV0,hVU,realFieldE hξ i w,hc,fun p hp n _ => ha p hp n,
      fun v hv hv0 hk => positive_base_field hξ i w hw v hv hv0 hk⟩
  obtain ⟨r,M,hr,hM,hb⟩ := SupportedStress.supported_stress_local_criterion W pairwise_orthogonal
    span_top (fE hξ) U hU h0 hf hs (quadratic_zero_cone hξ) hstress
  refine ⟨r,M,hr,hM,?_⟩
  intro c u hc hu
  obtain ⟨hp,hd,hz⟩ := hb c u hc hu
  exact ⟨hsource (c,u) hp,hrange (c,u) hp,hd,hz⟩

end Option2.NativeStress.PhaseEuclideanCriterion
#print axioms Option2.NativeStress.PhaseEuclideanCriterion.positive_base_field
#print axioms Option2.NativeStress.PhaseEuclideanCriterion.local_reduced_bound

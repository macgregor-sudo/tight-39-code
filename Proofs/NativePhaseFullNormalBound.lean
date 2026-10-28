module

public import NativePhaseReducedFamilyBound

@[expose] public section

/-! Extension from the range-zero embedding to a full native normal neighborhood.
The range coordinate is the bounded projection of the unchanged full residual. -/
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Option2.NativeStress.PhaseFullNormalBound
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeSliceNormalSplitting CKM.NativeSliceImplicitReduction
open BookHT BookOrthogonal PhaseSheetChart PhaseRangeReduction PhaseEuclideanCriterion PhaseSheetDistance
open Filter Topology
variable {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)

theorem zero_mem_reducedPH_target : (0 : (Normal ξ)) ∈ (reducedPH hξ).target := by
  simpa only [(reducedPH_zero hξ)] using (reducedPH hξ).map_source (zero_mem_reducedPH_source hξ)

@[simp] theorem reducedPH_symm_zero : (reducedPH hξ).symm 0 = 0 := by
  simpa only [(reducedPH_zero hξ)] using (reducedPH hξ).left_inv (zero_mem_reducedPH_source hξ)

/-- The actual range coordinate is the actual bounded linear projection of all original rows. -/
theorem actual_range_coordinate (n : (Normal ξ)) (hn : n ∈ (reducedPH hξ).target) :
    ((reducedPH hξ).symm n).2 = rangeProjection ξ (normalResidual ξ n) := by
  have hq := (reducedPH hξ).map_target hn
  have h := congrArg Prod.snd ((rangePH hξ).right_inv hq.1)
  change rangeProjection ξ
    (normalResidual ξ ((reducedPH hξ) ((reducedPH hξ).symm n))) = ((reducedPH hξ).symm n).2 at h
  rw [(reducedPH hξ).right_inv hn] at h
  exact h.symm

def rangeZeroRetraction (n : (Normal ξ)) : (Normal ξ) := (reducedEmbedding hξ) ((reducedPH hξ).symm n).1

def kernelCoordinates (n : (Normal ξ)) : (EuclideanModel ξ) :=
  (((reducedPH hξ).symm n).1.1, toBlocks.symm ((reducedPH hξ).symm n).1.2)

@[simp] theorem rangeZeroRetraction_zero : (rangeZeroRetraction hξ) 0 = 0 := by
  simp [rangeZeroRetraction]

@[simp] theorem kernelCoordinates_zero : (kernelCoordinates hξ) 0 = 0 := by
  simp [kernelCoordinates]

theorem kernelCoordinates_binding (n : (Normal ξ)) :
    coordinates ((kernelCoordinates hξ) n) = ((reducedPH hξ).symm n).1 := by
  simp [kernelCoordinates, coordinates]

theorem embedding_kernelCoordinates (n : (Normal ξ)) :
    (embeddingE hξ) ((kernelCoordinates hξ) n) = literalCfg ξ + ((rangeZeroRetraction hξ) n : Cfg) := by
  change literalCfg ξ +
    ((reducedEmbedding hξ) (coordinates ((kernelCoordinates hξ) n)) : Cfg) = _
  rw [(kernelCoordinates_binding hξ)]
  rfl

theorem rangeZeroRetraction_continuousAt : ContinuousAt (rangeZeroRetraction hξ) 0 := by
  have h := (reducedPH_symm_C2 hξ).continuousAt.fst
  have hc : ContinuousAt (reducedEmbedding hξ) ((reducedPH hξ).symm (0 : (Normal ξ))).1 := by
    simpa only [(reducedPH_symm_zero hξ), Prod.fst_zero] using (reducedEmbedding_C2 hξ).continuousAt
  exact ContinuousAt.comp (f := fun n : (Normal ξ) => ((reducedPH hξ).symm n).1) hc h

theorem kernelCoordinates_continuousAt : ContinuousAt (kernelCoordinates hξ) 0 :=
  (reducedPH_symm_C2 hξ).continuousAt.fst.fst.prodMk
    (toBlocks.symm.continuous.continuousAt.comp (reducedPH_symm_C2 hξ).continuousAt.fst.snd)

/-- The specified Euclidean kernel coordinates tend to zero in their unchanged norms. -/
theorem kernelCoordinates_small (r : ℝ) (hr : 0 < r) :
    ∀ᶠ n : (Normal ξ) in 𝓝 0, ‖((kernelCoordinates hξ) n).1‖ < r ∧ ‖((kernelCoordinates hξ) n).2‖ < r := by
  have ht : Tendsto (kernelCoordinates hξ) (𝓝 (0 : (Normal ξ))) (𝓝 0) := by
    simpa only [(kernelCoordinates_zero hξ)] using (kernelCoordinates_continuousAt hξ).tendsto
  filter_upwards [ht.eventually (Metric.ball_mem_nhds (0 : (EuclideanModel ξ)) hr)] with n hn
  have hnorm : ‖(kernelCoordinates hξ) n‖ < r := by
    simpa only [Metric.mem_ball, dist_zero_right] using hn
  change max ‖((kernelCoordinates hξ) n).1‖ ‖((kernelCoordinates hξ) n).2‖ < r at hnorm
  exact max_lt_iff.mp hnorm

/-- Local Lipschitz comparison to the actual range-zero point, with a residual comparison.
The constants are constructed from chart/residual Lipschitz constants and the actual range
projection's operator norm. No Lipschitz or distance estimate is a premise. -/
theorem normal_retraction_estimates :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ᶠ n : (Normal ξ) in 𝓝 0, n ∈ (reducedPH hξ).target ∧
        ‖n - (rangeZeroRetraction hξ) n‖ ≤ A * ‖normalResidual ξ n‖ ∧
        ‖normalResidual ξ ((rangeZeroRetraction hξ) n)‖ ≤ B * ‖normalResidual ξ n‖ ∧
        ‖normalResidual ξ n‖ ≤ 1 := by
  obtain ⟨K, U, hU, hLip⟩ :=
    ((reducedPH_C2 hξ).hasStrictFDerivAt (by norm_num)).exists_lipschitzOnWith
  have hFC1 : ContDiffAt ℝ 1 (normalResidual ξ) (0 : (Normal ξ)) :=
    (normalResidual_contDiff ξ 1).contDiffAt
  obtain ⟨L, T0, hT0, hFLip⟩ :=
    (hFC1.hasStrictFDerivAt (by norm_num)).exists_lipschitzOnWith
  let A : ℝ := ((K : ℝ) + 1) * (‖rangeProjection ξ‖ + 1)
  let B : ℝ := 1 + (L : ℝ) * A
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have ht : Tendsto (reducedPH hξ).symm (𝓝 (0 : (Normal ξ))) (𝓝 0) := by
    simpa only [(reducedPH_symm_zero hξ)] using (reducedPH_symm_C2 hξ).continuousAt.tendsto
  have ht0 : Tendsto (fun n : (Normal ξ) => (((reducedPH hξ).symm n).1, (0 : normalRange ξ)))
      (𝓝 0) (𝓝 ((0 : (KernelModel ξ)), (0 : normalRange ξ))) :=
    ht.fst_nhds.prodMk_nhds tendsto_const_nhds
  have htr : Tendsto (rangeZeroRetraction hξ) (𝓝 (0 : (Normal ξ))) (𝓝 0) := by
    simpa only [(rangeZeroRetraction_zero hξ)] using (rangeZeroRetraction_continuousAt hξ).tendsto
  have hF0 : normalResidual ξ (0 : (Normal ξ)) = 0 := by
    simpa only [sheetResidual, (reducedEmbedding_zero hξ)] using (sheetResidual_zero hξ)
  have hFt : Tendsto (normalResidual ξ) (𝓝 (0 : (Normal ξ))) (𝓝 0) := by
    simpa only [hF0] using (normalResidual_contDiff ξ 1).continuous.continuousAt.tendsto (x := (0 : (Normal ξ)))
  refine ⟨A, B, hA, hB, ?_⟩
  filter_upwards [(reducedPH hξ).open_target.mem_nhds (zero_mem_reducedPH_target hξ),
    ht.eventually hU, ht0.eventually hU, hT0, htr.eventually hT0,
    hFt.eventually (Metric.ball_mem_nhds (0 : Residual) zero_lt_one)] with n hn hq hq0 hnT hrT hf1
  have hdiff : ‖(reducedPH hξ).symm n - (((reducedPH hξ).symm n).1, (0 : normalRange ξ))‖ =
      ‖((reducedPH hξ).symm n).2‖ := by
    change max ‖((reducedPH hξ).symm n).1 - ((reducedPH hξ).symm n).1‖ ‖((reducedPH hξ).symm n).2 - 0‖ = _
    simp
  have hd := (lipschitzOnWith_iff_norm_sub_le.mp hLip) hq hq0
  rw [hdiff, (reducedPH hξ).right_inv hn] at hd
  change ‖n - (rangeZeroRetraction hξ) n‖ ≤ (K : ℝ) * ‖((reducedPH hξ).symm n).2‖ at hd
  have hproj : ‖((reducedPH hξ).symm n).2‖ ≤
      ‖rangeProjection ξ‖ * ‖normalResidual ξ n‖ := by
    rw [(actual_range_coordinate hξ) n hn]
    exact (rangeProjection ξ).le_opNorm _
  have hKP : (K : ℝ) * ‖rangeProjection ξ‖ ≤ A := by
    dsimp [A]
    nlinarith [norm_nonneg (rangeProjection ξ), K.coe_nonneg]
  have ha : ‖n - (rangeZeroRetraction hξ) n‖ ≤ A * ‖normalResidual ξ n‖ := by
    calc
      _ ≤ (K : ℝ) * (‖rangeProjection ξ‖ * ‖normalResidual ξ n‖) :=
        hd.trans (mul_le_mul_of_nonneg_left hproj K.coe_nonneg)
      _ = ((K : ℝ) * ‖rangeProjection ξ‖) * ‖normalResidual ξ n‖ := by ring
      _ ≤ A * ‖normalResidual ξ n‖ :=
        mul_le_mul_of_nonneg_right hKP (norm_nonneg _)
  have hf := (lipschitzOnWith_iff_norm_sub_le.mp hFLip) hrT hnT
  rw [norm_sub_rev ((rangeZeroRetraction hξ) n) n] at hf
  have hb : ‖normalResidual ξ ((rangeZeroRetraction hξ) n)‖ ≤ B * ‖normalResidual ξ n‖ := by
    calc
      _ = ‖(normalResidual ξ ((rangeZeroRetraction hξ) n) - normalResidual ξ n) +
        normalResidual ξ n‖ := by rw [sub_add_cancel]
      _ ≤ ‖normalResidual ξ ((rangeZeroRetraction hξ) n) - normalResidual ξ n‖ +
        ‖normalResidual ξ n‖ := norm_add_le _ _
      _ ≤ (L : ℝ) * ‖n - (rangeZeroRetraction hξ) n‖ + ‖normalResidual ξ n‖ := add_le_add hf le_rfl
      _ ≤ (L : ℝ) * (A * ‖normalResidual ξ n‖) + ‖normalResidual ξ n‖ :=
        add_le_add (mul_le_mul_of_nonneg_left ha L.coe_nonneg) le_rfl
      _ = B * ‖normalResidual ξ n‖ := by dsimp [B]; ring
  refine ⟨hn, ha, hb, ?_⟩
  exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hf1)
/-- Full actual normal-neighborhood residual-distance-squared bound, for every specified
local family-parameter neighborhood. Both original native coordinates and norms are retained. -/
theorem local_normal_family_bound (V : Fin 4 → Set SliceParam)
    (hV : ∀ H, V H ∈ 𝓝 0) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ n : (Normal ξ), ‖n‖ < δ → n ∈ (reducedPH hξ).target ∧
        Metric.infDist (literalCfg ξ + (n : Cfg)) ((actualFamilyUnion hξ) V) ^ 2 ≤
          C * ‖AnalyticDerivative.originalF (literalCfg ξ + (n : Cfg))‖ := by
  obtain ⟨r, C0, hr, hC0, hred⟩ :=
    PhaseReducedFamilyBound.local_family_residual_bound hξ V hV
  obtain ⟨A, B, hA, hB, hret⟩ := (normal_retraction_estimates hξ)
  let C : ℝ := 2 * C0 * B + 2 * A ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : ∀ᶠ n : (Normal ξ) in 𝓝 0, n ∈ (reducedPH hξ).target ∧
      Metric.infDist (literalCfg ξ + (n : Cfg)) ((actualFamilyUnion hξ) V) ^ 2 ≤
        C * ‖normalResidual ξ n‖ := by
    filter_upwards [hret, (kernelCoordinates_small hξ) r hr] with n hn hs
    obtain ⟨hnt, hdist, hres, hsmall⟩ := hn
    obtain ⟨-, -, hredbound⟩ := hred ((kernelCoordinates hξ) n).1 ((kernelCoordinates hξ) n).2 hs.1 hs.2
    change Metric.infDist ((embeddingE hξ) ((kernelCoordinates hξ) n)) ((actualFamilyUnion hξ) V) ^ 2 ≤
      C0 * ‖AnalyticDerivative.originalF ((embeddingE hξ) ((kernelCoordinates hξ) n))‖ at hredbound
    rw [(embedding_kernelCoordinates hξ)] at hredbound
    change Metric.infDist (literalCfg ξ + ((rangeZeroRetraction hξ) n : Cfg)) ((actualFamilyUnion hξ) V) ^ 2 ≤
      C0 * ‖normalResidual ξ ((rangeZeroRetraction hξ) n)‖ at hredbound
    have hbb := hredbound.trans (mul_le_mul_of_nonneg_left hres hC0.le)
    have hff : ‖normalResidual ξ n‖ ^ 2 ≤ ‖normalResidual ξ n‖ := by
      nlinarith [norm_nonneg (normalResidual ξ n)]
    have hdd : ‖n - (rangeZeroRetraction hξ) n‖ ^ 2 ≤ A ^ 2 * ‖normalResidual ξ n‖ := by
      calc
        _ ≤ (A * ‖normalResidual ξ n‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hdist 2
        _ = A ^ 2 * ‖normalResidual ξ n‖ ^ 2 := by ring
        _ ≤ A ^ 2 * ‖normalResidual ξ n‖ := mul_le_mul_of_nonneg_left hff (sq_nonneg A)
    have hnativeDist : dist (literalCfg ξ + (n : Cfg))
        (literalCfg ξ + ((rangeZeroRetraction hξ) n : Cfg)) = ‖n - (rangeZeroRetraction hξ) n‖ := by
      simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← Submodule.coe_sub, Submodule.norm_coe]
    have htri := Metric.infDist_le_infDist_add_dist
      (x := literalCfg ξ + (n : Cfg))
      (y := literalCfg ξ + ((rangeZeroRetraction hξ) n : Cfg)) (s := (actualFamilyUnion hξ) V)
    rw [hnativeDist] at htri
    have hsq := pow_le_pow_left₀ Metric.infDist_nonneg htri 2
    refine ⟨hnt, ?_⟩
    dsimp [C]
    nlinarith [sq_nonneg (Metric.infDist (literalCfg ξ + ((rangeZeroRetraction hξ) n : Cfg))
      ((actualFamilyUnion hξ) V) - ‖n - (rangeZeroRetraction hξ) n‖)]
  obtain ⟨δ, hδ, hδbound⟩ := Metric.mem_nhds_iff.mp hbound
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro n hn
  exact hδbound (by simpa only [Metric.mem_ball, dist_zero_right] using hn)

/-- Exact local full-original zero equivalence is obtained from the actual chart, not from
vanishing infDist or a closedness assumption on localized family images. -/
theorem local_normal_zero_iff :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : (Normal ξ), ‖n‖ < δ → n ∈ (reducedPH hξ).target ∧
      (AnalyticDerivative.originalF (literalCfg ξ + (n : Cfg)) = 0 ↔
        ((reducedPH hξ).symm n).2 = 0 ∧ ∃ i : Fin 4, FourBlock.OnAxis i ((reducedPH hξ).symm n).1.2) := by
  obtain ⟨r, M, hr, -, hred⟩ := PhaseEuclideanCriterion.local_reduced_bound hξ
  have hnear : ∀ᶠ n : (Normal ξ) in 𝓝 0, n ∈ (reducedPH hξ).target ∧
      (AnalyticDerivative.originalF (literalCfg ξ + (n : Cfg)) = 0 ↔
        ((reducedPH hξ).symm n).2 = 0 ∧ ∃ i : Fin 4, FourBlock.OnAxis i ((reducedPH hξ).symm n).1.2) := by
    filter_upwards [(reducedPH hξ).open_target.mem_nhds (zero_mem_reducedPH_target hξ),
      (kernelCoordinates_small hξ) r hr] with n hn hs
    obtain ⟨-, -, -, hz⟩ := hred ((kernelCoordinates hξ) n).1 ((kernelCoordinates hξ) n).2 hs.1 hs.2
    have he : (sheetResidual hξ) ((reducedPH hξ).symm n).1 = 0 ↔
        ∃ i : Fin 4, FourBlock.OnAxis i ((reducedPH hξ).symm n).1.2 := by
      have h := hz.trans (mem_blockUnion_iff ((kernelCoordinates hξ) n).2)
      change (sheetResidual hξ) (coordinates ((kernelCoordinates hξ) n)) = 0 ↔
        ∃ i : Fin 4, FourBlock.OnAxis i (toBlocks (toBlocks.symm ((reducedPH hξ).symm n).1.2)) at h
      simpa only [(kernelCoordinates_binding hξ), ContinuousLinearEquiv.apply_symm_apply] using h
    exact ⟨hn, ((originalF_zero_iff_normal hξ) n hn).trans (and_congr Iff.rfl he)⟩
  obtain ⟨δ, hδ, hδnear⟩ := Metric.mem_nhds_iff.mp hnear
  exact ⟨δ, hδ, fun n hn => hδnear (by simpa only [Metric.mem_ball, dist_zero_right] using hn)⟩


end Option2.NativeStress.PhaseFullNormalBound
#print axioms Option2.NativeStress.PhaseFullNormalBound.local_normal_family_bound
#print axioms Option2.NativeStress.PhaseFullNormalBound.local_normal_zero_iff

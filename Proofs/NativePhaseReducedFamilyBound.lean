module

public import NativePhaseSheetDistance
public import BookNativeEuclideanSheetDistance

@[expose] public section

/-! The unchanged original residual controls squared distance to all four actual
native families, on the good-phase reduced embedding and for arbitrary local
parameter neighborhoods. No fixed-seed reproduction hypothesis remains. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.PhaseReducedFamilyBound
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeSliceNormalSplitting CKM.NativeSliceImplicitReduction
open BookHT BookOrthogonal PhaseSheetChart PhaseRangeReduction PhaseEuclideanCriterion PhaseSheetDistance
open BookHT.SheetDistance (axisUnion)
open Filter Topology
variable {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)

/-- Actual native chart-to-family distance, measured by the Euclidean distance
from the orthogonal block union. Every chosen family-parameter neighborhood is
retained, and the native chart domain is shrunk by the proved operator bound. -/
theorem local_euclidean_sheet_distance (V : Fin 4 → Set SliceParam)
    (hV : ∀ H, V H ∈ 𝓝 0) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ (c : Common ξ) (x : BookOrthogonal.E), ‖c‖ < r → ‖x‖ < r →
        ((c, toBlocks x), (0 : normalRange ξ)) ∈ (reducedPH hξ).source ∧
        Metric.infDist ((ambientMap hξ) (c, toBlocks x)) ((actualFamilyUnion hξ) V) ≤
          C * Metric.infDist x (SupportedStress.blockUnion W) := by
  obtain ⟨r0, L, hr0, hL, hsheet⟩ := (local_sheet_distance hξ) V hV
  obtain ⟨r, hr, hrr0, hshrink⟩ := BookHT.EuclideanSheetDistance.norm_domain_shrink r0 hr0
  let K : ℝ := BookOrthogonal.Distance.forwardConstant
  have hK : 0 < K := BookOrthogonal.Distance.forwardConstant_pos
  refine ⟨r, L * K, hr, mul_pos hL hK, ?_⟩
  intro c x hc hx
  have hc0 : ‖c‖ < r0 := lt_of_lt_of_le hc hrr0
  have hx0 : ‖toBlocks x‖ < r0 := hshrink x hx
  obtain ⟨hsource, hdist⟩ := hsheet c (toBlocks x) hc0 hx0
  have hbook : Metric.infDist (toBlocks x) axisUnion ≤
      K * Metric.infDist x (SupportedStress.blockUnion W) :=
    BookOrthogonal.Distance.forward_infDist x
  refine ⟨hsource, hdist.trans ?_⟩
  calc
    L * Metric.infDist (toBlocks x) axisUnion ≤
        L * (K * Metric.infDist x (SupportedStress.blockUnion W)) :=
      mul_le_mul_of_nonneg_left hbook hL.le
    _ = (L * K) * Metric.infDist x (SupportedStress.blockUnion W) :=
      (mul_assoc _ _ _).symm

/-- Localized actual native family distance squared is controlled by the unchanged
original residual on the genuine reduced embedding. The chosen family-parameter
neighborhoods are retained; only the two exact native reproductions are inputs. -/
theorem local_family_residual_bound
    (V : Fin 4 → Set SliceParam) (hV : ∀ H, V H ∈ 𝓝 0) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ (c : Common ξ) (x : BookOrthogonal.E), ‖c‖ < r → ‖x‖ < r →
        (coordinates (c,x), (0 : normalRange ξ)) ∈ (reducedPH hξ).source ∧
        rangeProjection ξ (AnalyticDerivative.originalF ((embeddingE hξ) (c,x))) = 0 ∧
        Metric.infDist ((embeddingE hξ) (c,x)) ((actualFamilyUnion hξ) V) ^ 2 ≤
          C * ‖AnalyticDerivative.originalF ((embeddingE hξ) (c,x))‖ := by
  obtain ⟨r0, M, hr0, hM, hres⟩ :=
    PhaseEuclideanCriterion.local_reduced_bound hξ
  obtain ⟨r1, L, hr1, hL, hdist⟩ :=
    (local_euclidean_sheet_distance hξ) V hV
  refine ⟨min r0 r1, L ^ 2 * M, lt_min hr0 hr1, mul_pos (pow_pos hL 2) hM, ?_⟩
  intro c x hc hx
  have hc0 : ‖c‖ < r0 := lt_of_lt_of_le hc (min_le_left _ _)
  have hx0 : ‖x‖ < r0 := lt_of_lt_of_le hx (min_le_left _ _)
  have hc1 : ‖c‖ < r1 := lt_of_lt_of_le hc (min_le_right _ _)
  have hx1 : ‖x‖ < r1 := lt_of_lt_of_le hx (min_le_right _ _)
  obtain ⟨hsource, hrange, hbound, hzero⟩ := hres c x hc0 hx0
  obtain ⟨hsource1, hfamily⟩ := hdist c x hc1 hx1
  change Metric.infDist ((embeddingE hξ) (c,x)) ((actualFamilyUnion hξ) V) ≤
    L * Metric.infDist x (SupportedStress.blockUnion W) at hfamily
  have hsq : Metric.infDist ((embeddingE hξ) (c,x)) ((actualFamilyUnion hξ) V) ^ 2 ≤
      (L * Metric.infDist x (SupportedStress.blockUnion W)) ^ 2 :=
    pow_le_pow_left₀ Metric.infDist_nonneg hfamily 2
  refine ⟨hsource, hrange, ?_⟩
  calc
    Metric.infDist ((embeddingE hξ) (c,x)) ((actualFamilyUnion hξ) V) ^ 2 ≤
        L ^ 2 * Metric.infDist x (SupportedStress.blockUnion W) ^ 2 := by
      simpa only [mul_pow] using hsq
    _ ≤ L ^ 2 * (M * ‖AnalyticDerivative.originalF ((embeddingE hξ) (c,x))‖) :=
      mul_le_mul_of_nonneg_left hbound (sq_nonneg L)
    _ = (L ^ 2 * M) * ‖AnalyticDerivative.originalF ((embeddingE hξ) (c,x))‖ :=
      (mul_assoc _ _ _).symm


end Option2.NativeStress.PhaseReducedFamilyBound
#print axioms Option2.NativeStress.PhaseReducedFamilyBound.local_family_residual_bound

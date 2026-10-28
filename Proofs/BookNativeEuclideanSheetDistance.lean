module

public import BookNativeSheetDistance
public import BookOrthogonalDistance

@[expose] public section

noncomputable section
namespace Option2.NativeStress.BookHT.EuclideanSheetDistance
open SheetDistance SheetReduction BookOrthogonal
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeSliceNormalSplitting CKM.NativeSliceImplicitReduction
open QuadraticCertificate.ExactCKMConfiguration Filter Topology

/-- The actual continuous coordinate map is bounded in the unchanged norms.
This is not an isometry claim. -/
theorem norm_toBlocks_le (x : BookOrthogonal.E) :
    ‖toBlocks x‖ ≤ (BookOrthogonal.Distance.forwardConstant : ℝ) * ‖x‖ := by
  calc
    ‖toBlocks x‖ ≤ ‖(toBlocks : BookOrthogonal.E →L[ℝ] Blocks)‖ * ‖x‖ :=
      (toBlocks : BookOrthogonal.E →L[ℝ] Blocks).le_opNorm x
    _ ≤ (BookOrthogonal.Distance.forwardConstant : ℝ) * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      change ‖(toBlocks : BookOrthogonal.E →L[ℝ] Blocks)‖ ≤
        ‖(toBlocks : BookOrthogonal.E →L[ℝ] Blocks)‖ + 1
      linarith

/-- A positive Euclidean radius that stays inside any given Book radius. -/
theorem norm_domain_shrink (r : ℝ) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ r ∧
      ∀ x : BookOrthogonal.E, ‖x‖ < δ → ‖toBlocks x‖ < r := by
  let K : ℝ := BookOrthogonal.Distance.forwardConstant
  have hK : 0 < K := BookOrthogonal.Distance.forwardConstant_pos
  refine ⟨min r (r / K), lt_min hr (div_pos hr hK), min_le_left _ _, ?_⟩
  intro x hx
  have hxdiv : ‖x‖ < r / K := lt_of_lt_of_le hx (min_le_right _ _)
  have hmul : K * ‖x‖ < r := by
    simpa only [mul_comm] using (lt_div_iff₀ hK).mp hxdiv
  exact (norm_toBlocks_le x).trans_lt hmul

/-- Actual native chart-to-family distance, measured by the Euclidean distance
from the orthogonal block union. Every chosen family-parameter neighborhood is
retained, and the native chart domain is shrunk by the proved operator bound. -/
theorem local_euclidean_sheet_distance (V : Fin 4 → Set SliceParam)
    (hV : ∀ H, V H ∈ 𝓝 0) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ (c : Common) (x : BookOrthogonal.E), ‖c‖ < r → ‖x‖ < r →
        ((c, toBlocks x), (0 : normalRange exactPhases)) ∈ reducedPH.source ∧
        Metric.infDist (ambientMap (c, toBlocks x)) (actualFamilyUnion V) ≤
          C * Metric.infDist x (SupportedStress.blockUnion W) := by
  obtain ⟨r0, L, hr0, hL, hsheet⟩ := local_sheet_distance V hV
  obtain ⟨r, hr, hrr0, hshrink⟩ := norm_domain_shrink r0 hr0
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

/-- Full family ranges are a specialization of the localized native result. -/
theorem full_family_euclidean_distance :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ (c : Common) (x : BookOrthogonal.E), ‖c‖ < r → ‖x‖ < r →
        ((c, toBlocks x), (0 : normalRange exactPhases)) ∈ reducedPH.source ∧
        Metric.infDist (ambientMap (c, toBlocks x))
          (actualFamilyUnion (fun _ => Set.univ)) ≤
            C * Metric.infDist x (SupportedStress.blockUnion W) :=
  local_euclidean_sheet_distance (fun _ => Set.univ) (fun _ => Filter.univ_mem)

end Option2.NativeStress.BookHT.EuclideanSheetDistance

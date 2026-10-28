module

public import BookNativeEuclideanCriterion
public import BookNativeReducedSheetHStress

@[expose] public section

/-! Actual H fields on the Euclidean supported-stress domain.
All coordinate maps retain the existing norms; no isometry or positivity is assumed. -/
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Option2.NativeStress.BookHT.EuclideanHStress
open BookOrthogonal EuclideanCriterion SheetReduction SheetHStress
open CKM.NativeSliceImplicitReduction
open scoped Topology BigOperators

abbrev AxisDomain (i : Fin 4) := Common × W i

/-- Include the actual orthogonal axis in the actual criterion domain. -/
def axisInclusion (i : Fin 4) : AxisDomain i →L[ℝ] EuclideanModel :=
  (ContinuousLinearMap.fst ℝ Common (W i)).prod
    ((W i).subtypeL.comp (ContinuousLinearMap.snd ℝ Common (W i)))

/-- The specified continuous coordinate map (c,u) ↦ (c,(toBlocks u)i). -/
def axisCoordinates (i : Fin 4) : AxisDomain i →L[ℝ] FamilyCoordinates :=
  (ContinuousLinearMap.fst ℝ Common (W i)).prod
    ((ContinuousLinearMap.proj i : Blocks →L[ℝ] Triple).comp
      (toBlocks.toContinuousLinearMap.comp
        ((W i).subtypeL.comp (ContinuousLinearMap.snd ℝ Common (W i)))))

@[simp] theorem axisCoordinates_apply (i : Fin 4) (p : AxisDomain i) :
    axisCoordinates i p = (p.1, toBlocks (p.2 : E) i) := rfl

/-- Genuine W support, not an assumed set-image correspondence. -/
theorem toBlocks_axis (i : Fin 4) (u : W i) :
    toBlocks (u : E) = Pi.single i (toBlocks (u : E) i) := by
  have ha := (mem_W_iff_onAxis i (u : E)).1 u.property
  ext j
  by_cases hj : j = i
  · subst j; simp
  · simp [hj, ha j hj]

theorem axis_coordinate_binding (i : Fin 4) (p : AxisDomain i) :
    euclideanCoordinates (axisInclusion i p) =
      ((axisCoordinates i p).1, Pi.single i (axisCoordinates i p).2) := by
  change (p.1, toBlocks (p.2 : E)) = (p.1, Pi.single i (toBlocks (p.2 : E) i))
  exact congrArg (fun z : Blocks => (p.1, z)) (toBlocks_axis i p.2)

/-- Fixed Euclidean w selects the exact Book H functional; the field point varies separately. -/
def realFieldE (i : Fin 4) (w : W i) (p : AxisDomain i) : Residual →L[ℝ] ℝ :=
  realField i (toBlocks (w : E)) (axisCoordinates i p)

@[simp] theorem realFieldE_zero (i : Fin 4) (w : W i) :
    realFieldE i w 0 = NativeH.realStressFunctional i (toBlocks (w : E)) := by
  rw [realFieldE, map_zero, realField_zero]

/-- Exact factor three, conjugation on sigma, original H weights, and real part. -/
theorem realFieldE_zero_apply (i : Fin 4) (w : W i) (q : Residual) :
    realFieldE i w 0 q = 3 *
      (∑ a : Fin 3, star (sigma (toBlocks (w : E) i) a) *
        ∑ r : Fin 2184, NativeH.weightC i a r * (q r : ℂ)).re := by
  rw [realFieldE_zero]
  exact NativeH.realStressFunctional_apply_hermitian i (toBlocks (w : E)) q

/-- Open-neighborhood H field on exactly Common × W i, for every fixed w (hence every unit w).
Annihilation holds on all Euclidean directions, in particular on the orthogonal complement. -/
theorem supported_stress_field_E (i : Fin 4) (w : W i) (U : Set EuclideanModel)
    (hU : IsOpen U) (h0 : (0 : EuclideanModel) ∈ U) :
    ∃ V : Set (AxisDomain i), IsOpen V ∧ (0 : AxisDomain i) ∈ V ∧
      (∀ p ∈ V, (p.1, (p.2 : E)) ∈ U) ∧
      ContinuousOn (realFieldE i w) V ∧
      (∀ p ∈ V, ∀ n : E,
        realFieldE i w p (fderiv ℝ fE (p.1, (p.2 : E)) (0,n)) = 0) ∧
      realFieldE i w 0 = NativeH.realStressFunctional i (toBlocks (w : E)) := by
  obtain ⟨VB, hVB, hVB0, -, hcont, hann, -⟩ :=
    supported_stress_field i (toBlocks (w : E)) Set.univ isOpen_univ (Set.mem_univ _)
  have hu : ∀ᶠ p in 𝓝 (0 : AxisDomain i), axisInclusion i p ∈ U :=
    (axisInclusion i).continuous.continuousAt.preimage_mem_nhds
      (by rw [map_zero]; exact hU.mem_nhds h0)
  have ht : Filter.Tendsto (euclideanCoordinates.comp (axisInclusion i))
      (𝓝 (0 : AxisDomain i)) (𝓝 0) := by
    simpa only [map_zero] using
      (euclideanCoordinates.comp (axisInclusion i)).continuous.continuousAt.tendsto (x := 0)
  have hd : ∀ᶠ p in 𝓝 (0 : AxisDomain i),
      ContDiffAt ℝ 2 sheetResidual (euclideanCoordinates (axisInclusion i p)) :=
    ht.eventually (sheetResidual_C2.eventually (by norm_num))
  obtain ⟨V0, hV0, hV0open, hV00⟩ := mem_nhds_iff.1 (hu.and hd)
  let V : Set (AxisDomain i) := V0 ∩ (axisCoordinates i) ⁻¹' VB
  have hz : (0 : AxisDomain i) ∈ V := ⟨hV00, by
    change axisCoordinates i 0 ∈ VB
    simpa only [map_zero] using hVB0⟩
  refine ⟨V, hV0open.inter (hVB.preimage (axisCoordinates i).continuous), hz,
    fun p hp => (hV0 hp.1).1, ?_, ?_, realFieldE_zero i w⟩
  · exact hcont.comp (axisCoordinates i).continuous.continuousOn (fun p hp => hp.2)
  · intro p hp n
    have hs := (hV0 hp.1).2
    change ContDiffAt ℝ 2 sheetResidual (euclideanCoordinates (p.1, (p.2 : E))) at hs
    change realField i (toBlocks (w : E)) (axisCoordinates i p)
      (fderiv ℝ (sheetResidual ∘ euclideanCoordinates) (p.1, (p.2 : E)) (0,n)) = 0
    rw [fderiv_comp _ (hs.differentiableAt (by norm_num)) euclideanCoordinates.differentiableAt]
    rw [euclideanCoordinates.fderiv]
    change realField i (toBlocks (w : E)) (axisCoordinates i p)
      (fderiv ℝ sheetResidual (p.1, toBlocks (p.2 : E)) (0,toBlocks n)) = 0
    rw [toBlocks_axis i p.2]
    exact hann (axisCoordinates i p) hp.2 (toBlocks n)

/-- The precise existential continuous-field/orthogonal-annihilation part of the accepted criterion.
Its positive-kernel clause is deliberately not asserted. -/
theorem criterion_stress_field (i : Fin 4) (w : W i) (U : Set EuclideanModel)
    (hU : IsOpen U) (h0 : (0 : EuclideanModel) ∈ U) :
    ∃ V : Set (Common × W i), IsOpen V ∧ (0 : Common × W i) ∈ V ∧
      (∀ p ∈ V, (p.1, (p.2 : E)) ∈ U) ∧
      ∃ ell : Common × W i → Residual →L[ℝ] ℝ,
        ContinuousOn ell V ∧
        (∀ p ∈ V, ∀ n ∈ (W i).orthogonal,
          ell p (fderiv ℝ fE (p.1, (p.2 : E)) (0,n)) = 0) ∧
        ell 0 = NativeH.realStressFunctional i (toBlocks (w : E)) := by
  obtain ⟨V, hV, hV0, hVU, hc, ha, hb⟩ := supported_stress_field_E i w U hU h0
  exact ⟨V, hV, hV0, hVU, realFieldE i w, hc, fun p hp n _ => ha p hp n, hb⟩

end Option2.NativeStress.BookHT.EuclideanHStress

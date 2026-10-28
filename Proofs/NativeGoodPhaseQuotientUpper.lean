module

public import NativeSliceQuotientDimension
public import NativePhaseNormalDimension
public import NativeSliceShrink

@[expose] public section

/-! Actual native good-phase quotient upper bound. The complete normal zero
bound is transferred by the literal affine normal coordinate, then the existing
finite-action quotient dimension theorem. The invariant neighborhood is shrunk
inside the actual native quotient chart. No pivot or generic-phase hypothesis
beyond the twelve-test IsGoodPhase predicate is added. -/
noncomputable section
namespace Option2.NativeStress.NativeGoodPhaseQuotientUpper
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeUnlabelledSlice
open CKM.NativeFourFamily
open CKM.NativeTraceMetricBinding
open PhaseSheetChart PhaseNormalForm PhaseNormalDimension
open NativeLocalDimensionA7 SliceTenPatchesA7
open TopologicalSpace

theorem native_good_phase_quotient_upper {ξ : Fin 4 → ℂ} (hgood : IsGoodPhase ξ) :
    ∃ V : Set Cfg, IsOpen V ∧ literalCfg ξ ∈ V ∧
      (∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ V ↔ C ∈ V) ∧
      Topology.IsOpenEmbedding (sliceQuotMap ξ V) ∧
      HasSmallInductiveDimensionLE (SliceQuot ξ V) 10 := by
  obtain ⟨δ, hδ, hbound⟩ := normal_zero_dimension_le hgood
  have hnormal : HasSmallInductiveDimensionLE
      ↥(Metric.ball (0 : Normal ξ) δ ∩ nativeZeros ξ) 10 :=
    hbound _ Metric.isOpen_ball (Metric.mem_ball_self hδ) Set.Subset.rfl
  obtain ⟨W, hW, hPW, hInvW, _, hembW, _⟩ := exists_sliceQuot_isOpenEmbedding ξ hgood.1
  obtain ⟨V, hV, hPV, hsmall, hInvV⟩ := native_invariant_open_within ξ hgood.1
    (hW.inter Metric.isOpen_ball) (show literalCfg ξ ∈ W ∩ Metric.ball (literalCfg ξ) δ from
      ⟨hPW, Metric.mem_ball_self hδ⟩)
  have hmaps (s : sliceGerm ξ V) : sliceNormal ξ V s ∈
      Metric.ball (0 : Normal ξ) δ ∩ nativeZeros ξ := by
    constructor
    · have hs := (hsmall s.2.1).2
      simpa [Metric.mem_ball, dist_eq_norm, sliceNormal] using hs
    · change AnalyticDerivative.originalF
        (literalCfg ξ + ((s.1 : Cfg) - literalCfg ξ)) = 0
      rw [add_sub_cancel]
      exact s.1.2
  let f : sliceGerm ξ V → ↥(Metric.ball (0 : Normal ξ) δ ∩ nativeZeros ξ) :=
    fun s => ⟨sliceNormal ξ V s, hmaps s⟩
  have hf : Topology.IsEmbedding f :=
    (Topology.IsEmbedding.subtypeVal.of_comp_iff).mp (isEmbedding_sliceNormal ξ V)
  have hslice : HasSmallInductiveDimensionLE (sliceGerm ξ V) 10 :=
    hf.isInducing.hasSmallInductiveDimensionLE hnormal
  exact ⟨V, hV, hPV, hInvV,
    sliceQuotMap_isOpenEmbedding_of_subset hInvW hembW hV
      (fun _ hs => (hsmall hs).1),
    native_slice_quotient_dimension_le_ten ξ hgood.1 V hInvV hslice⟩

#print axioms native_good_phase_quotient_upper
end Option2.NativeStress.NativeGoodPhaseQuotientUpper

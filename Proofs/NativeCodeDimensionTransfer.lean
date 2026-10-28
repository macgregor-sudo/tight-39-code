module

public import NativeLocalDimensionLower
public import NativePhaseA6

@[expose] public section

/-! Exact native locus identification and transport of a proved finite-slice
quotient upper bound into an open neighborhood in the actual CodeModuli.
No generic finite-to-one dimension theorem or target-as-assumption is used.
-/
noncomputable section
namespace Option2.NativeStress.NativeLocalDimensionA7
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeUnlabelledSlice CKM.NativeGoodPhase
open PhasePivotA6 PhasePivotLocusA6

/-- The source locus is exactly the same named nonempty open dense locus
already carrying the admitted A6 and good-phase accumulation outputs. -/
theorem nativeAdmittedGoodLocus_eq_nativeA6Locus :
    nativeAdmittedGoodLocus = PhaseA6.nativeA6Locus := rfl

/-- Actual native quotient/code transfer of the ten-dimensional upper bound.
The source is the whole finite slice quotient and its map is the frozen native
open embedding, so its range is a genuine CodeModuli neighborhood. -/
theorem code_neighborhood_ind_le_ten_of_slice (u : NativePhaseTorus)
    (W : Set Cfg) (hP : literalCfg u.1 ∈ W)
    (hemb : Topology.IsOpenEmbedding (sliceQuotMap u.1 W))
    (hdim : HasSmallInductiveDimensionLE (SliceQuot u.1 W) 10) :
    ∃ N : Set CodeModuli, IsOpen N ∧ codeClass u ∈ N ∧
      smallInductiveDimension N ≤ (10 : WithBot ℕ∞) := by
  let f : SliceQuot u.1 W → CodeModuli := unlabelledToCode ∘ sliceQuotMap u.1 W
  have hf : Topology.IsOpenEmbedding f := unlabelledHomeo.isOpenEmbedding.comp hemb
  have hNdim : HasSmallInductiveDimensionLE ↥(Set.range f) 10 :=
    (hf.toIsEmbedding.toHomeomorph.hasSmallInductiveDimensionLE 10).1 hdim
  refine ⟨Set.range f,hf.isOpen_range,?_,smallInductiveDimension_le_iff.2 hNdim⟩
  exact ⟨Quotient.mk (stabSetoid u.1 W)
    ⟨basePt u.1 u.2,hP,literalCfg_mem_sliceSet u.1⟩,rfl⟩

#print axioms nativeAdmittedGoodLocus_eq_nativeA6Locus
#print axioms code_neighborhood_ind_le_ten_of_slice
end Option2.NativeStress.NativeLocalDimensionA7

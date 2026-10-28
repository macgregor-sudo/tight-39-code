module
public import ZeroDimensionalAmbientSeparation

/-! The dimension-raising decomposition lemma: a space covered by a subspace of
inductive dimension below n and a zero-dimensional subspace has dimension at
most n. This uses only ambient separation avoiding the latter subspace. -/
@[expose] public section
noncomputable section
namespace SmallInductiveClosedSum
open Set Topology TopologicalSpace
variable {X : Type*} [TopologicalSpace X] [CompletelyNormalSpace X]
  [SecondCountableTopology X] [T1Space X]

/-- Engelking's dimension-raising decomposition step, retaining arbitrary
(nonclosed) subspaces and allowing the empty lower-dimensional part. -/
theorem dimension_le_of_union_zero_dimensional (n : ℕ) (Y Z : Set X)
    (hY : HasSmallInductiveDimensionLT ↥Y n)
    (hZ : HasSmallInductiveDimensionLE ↥Z 0) (hcover : Y ∪ Z = univ) :
    HasSmallInductiveDimensionLE X n := by
  let b : Set (Set X) := {U | IsOpen U ∧ HasSmallInductiveDimensionLT ↥(frontier U) n}
  have hb : IsTopologicalBasis b := by
    apply isTopologicalBasis_of_isOpen_of_nhds (fun _ h => h.1)
    intro x O hx hO
    have hd : Disjoint ({x} : Set X) Oᶜ :=
      disjoint_left.mpr (fun y hy hn => hn (mem_singleton_iff.mp hy ▸ hx))
    obtain ⟨U,V,hU,hV,hxU,hOV,hZUV,hUV⟩ := zero_dimensional_ambient_separation Z hZ
      {x} Oᶜ isClosed_singleton hO.isClosed_compl hd
    have hfY : frontier U ⊆ Y := by
      intro y hy
      have hall : y ∈ Y ∪ Z := by rw [hcover]; trivial
      apply hall.resolve_right
      intro hyZ
      rcases hZUV hyZ with hyU | hyV
      · exact (hU.frontier_eq ▸ hy).2 hyU
      · exact disjoint_left.mp (hUV.closure_left hV) (frontier_subset_closure hy) hyV
    have hind : HasSmallInductiveDimensionLT ↥(frontier U) n :=
      (Topology.IsInducing.id.restrict (show MapsTo id (frontier U) Y from hfY)).hasSmallInductiveDimensionLT hY
    refine ⟨U,⟨hU,hind⟩,hxU (mem_singleton x),?_⟩
    intro y hy
    by_contra hn
    exact disjoint_left.mp hUV hy (hOV hn)
  exact .succ n b hb (fun _ h => h.2)

end SmallInductiveClosedSum
#print axioms SmallInductiveClosedSum.dimension_le_of_union_zero_dimensional

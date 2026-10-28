module
public import ZeroDimensionalSeparation

/-! Countable frontier-controlled bases and zero-dimensional remainders after
removing all basis frontiers. These use only the definition of small inductive
dimension, not a sum theorem. -/
@[expose] public section
noncomputable section
namespace SmallInductiveClosedSum
open Set Topology TopologicalSpace
variable {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]

/-- A second-countable space with ind≤n has an enumerated open basis whose
frontiers have ind<n. The empty set ensures enumeration even for empty X. -/
theorem exists_countable_frontier_controlled_basis [SecondCountableTopology X]
    (n : ℕ) (hdim : HasSmallInductiveDimensionLE X n) :
    ∃ U : ℕ → Set X, IsTopologicalBasis (range U) ∧
      ∀ k, HasSmallInductiveDimensionLT ↥(frontier (U k)) n := by
  classical
  cases hdim with
  | succ n b hb hfront =>
    obtain ⟨s,hs,hsc,hsb⟩ := hb.exists_countable
    let t : Set (Set X) := s ∪ {∅}
    have htc : t.Countable := hsc.union (countable_singleton _)
    obtain ⟨U,hU⟩ := htc.exists_eq_range ⟨∅,Or.inr rfl⟩
    have hopen : ∀ V ∈ t, IsOpen V := by
      intro V hV
      rcases hV with hV | hV
      · exact hsb.isOpen hV
      · simpa only [mem_singleton_iff.mp hV] using (isOpen_empty : IsOpen (∅ : Set X))
    have htb : IsTopologicalBasis t := hsb.of_isOpen_of_subset hopen (fun _ h => Or.inl h)
    refine ⟨U,hU ▸ htb,?_⟩
    intro k
    have hk : U k ∈ t := hU ▸ mem_range_self k
    rcases hk with hk | hk
    · exact hfront _ (hs hk)
    · have he : U k = ∅ := mem_singleton_iff.mp hk
      rw [he,frontier_empty]
      infer_instance

/-- An inducing subspace avoiding every frontier of an ambient basis is
zero-dimensional. This applies to nonclosed subspaces. -/
theorem zero_dimensional_of_avoids_basis_frontiers {f : Z → X}
    (hf : IsInducing f) (b : Set (Set X)) (hb : IsTopologicalBasis b)
    (havoid : ∀ z U, U ∈ b → f z ∉ frontier U) :
    HasSmallInductiveDimensionLE Z 0 := by
  apply hasSmallInductiveDimensionLT_one_iff.mpr
  apply (hf.isTopologicalBasis hb).of_isOpen_of_subset (fun _ h => h.isOpen)
  rintro V ⟨U,hU,rfl⟩
  apply isClopen_iff_frontier_eq_empty.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact havoid z U hU (hf.continuous.frontier_preimage_subset U hz)

end SmallInductiveClosedSum
#print axioms SmallInductiveClosedSum.exists_countable_frontier_controlled_basis
#print axioms SmallInductiveClosedSum.zero_dimensional_of_avoids_basis_frontiers

module
public import CountableClosedSum

/-! Forward dimension-lowering separation. This is proved after the closed-sum
theorem, using a countable union of controlled frontiers and ambient separation
avoiding the zero-dimensional remainder. No Euclidean normalization is used. -/
@[expose] public section
noncomputable section
namespace SmallInductiveClosedSum
open Set Topology TopologicalSpace
variable {X : Type*} [TopologicalSpace X] [CompletelyNormalSpace X]
  [SecondCountableTopology X] [T1Space X]

/-- A countable union of ambient closed subspaces of dimension at most n has
dimension at most n, with the subspace topology on the union. -/
theorem countable_closed_union (n : ℕ) (F : ℕ → Set X)
    (hF : ∀ i, IsClosed (F i)) (hdim : ∀ i, HasSmallInductiveDimensionLE ↥(F i) n) :
    HasSmallInductiveDimensionLE ↥(⋃ i, F i) n := by
  let Y : Set X := ⋃ i, F i
  let G : ℕ → Set Y := fun i => Subtype.val ⁻¹' F i
  have hGc (i : ℕ) : IsClosed (G i) := (hF i).preimage continuous_subtype_val
  have hGd (i : ℕ) : HasSmallInductiveDimensionLE ↥(G i) n :=
    subtype_preimage_dimension_le Y (F i) n (hdim i)
  have hc : (⋃ i, G i) = univ := by
    apply eq_univ_of_forall
    intro y
    obtain ⟨i,hi⟩ := mem_iUnion.mp y.2
    exact mem_iUnion.mpr ⟨i,hi⟩
  exact countable_closed_sum n G hGc hGd hc

/-- A partition between arbitrary ambient disjoint closed sets can be chosen
to lower the dimension of its intersection with a prescribed subspace. -/
theorem dimension_lowering_separation (n : ℕ) (M : Set X)
    (hM : HasSmallInductiveDimensionLE ↥M n)
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧ Disjoint U V ∧
      HasSmallInductiveDimensionLT ↥(M \ (U ∪ V)) n := by
  classical
  cases n with
  | zero =>
    obtain ⟨U,V,hU,hV,hAU,hBV,hMUV,hUV⟩ :=
      zero_dimensional_ambient_separation M hM A B hA hB hAB
    refine ⟨U,V,hU,hV,hAU,hBV,hUV,hasSmallInductiveDimensionLT_zero_iff.mpr ?_⟩
    exact ⟨fun x => x.2.2 (hMUV x.2.1)⟩
  | succ n =>
    obtain ⟨T,hTb,hTf⟩ := exists_countable_frontier_controlled_basis (n+1) hM
    let Y : Set M := ⋃ i, frontier (T i)
    have hY : HasSmallInductiveDimensionLE ↥Y n :=
      countable_closed_union n (fun i => frontier (T i)) (fun _ => isClosed_frontier) hTf
    let Z : Set M := Yᶜ
    have hZ : HasSmallInductiveDimensionLE ↥Z 0 := by
      apply zero_dimensional_of_avoids_basis_frontiers Topology.IsInducing.subtypeVal
        (range T) hTb
      rintro z W ⟨i,rfl⟩ hz
      exact z.2 (mem_iUnion.mpr ⟨i,hz⟩)
    let Q : Set X := Subtype.val '' Z
    have hQ : HasSmallInductiveDimensionLE ↥Q 0 :=
      (Topology.IsEmbedding.subtypeVal.homeomorphImage Z).symm.isInducing.hasSmallInductiveDimensionLE hZ
    obtain ⟨U,V,hU,hV,hAU,hBV,hQUV,hUV⟩ :=
      zero_dimensional_ambient_separation Q hQ A B hA hB hAB
    have hRY (r : ↥(M \ (U ∪ V))) : (⟨r.1,r.2.1⟩ : M) ∈ Y := by
      by_contra hn
      exact r.2.2 (hQUV ⟨⟨r.1,r.2.1⟩,hn,rfl⟩)
    let f : ↥(M \ (U ∪ V)) → Y := fun r => ⟨⟨r.1,r.2.1⟩,hRY r⟩
    have hg : IsInducing (fun y : Y => (y.1 : X)) :=
      Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
    have hf : IsInducing f := hg.of_comp_iff.mp (show
        IsInducing ((fun y : Y => (y.1 : X)) ∘ f) from Topology.IsInducing.subtypeVal)
    exact ⟨U,V,hU,hV,hAU,hBV,hUV,hf.hasSmallInductiveDimensionLE hY⟩

/-- The whole-space separation form used by inductive-dimension lower bounds:
A lies in an open set whose closure avoids B and whose frontier has lower
dimension. No compactness is needed. -/
theorem exists_open_small_frontier (n : ℕ)
    (hdim : HasSmallInductiveDimensionLE X n)
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ Disjoint (closure U) B ∧
      HasSmallInductiveDimensionLT ↥(frontier U) n := by
  have hwhole : HasSmallInductiveDimensionLE ↥(univ : Set X) n :=
    Topology.IsInducing.subtypeVal.hasSmallInductiveDimensionLE hdim
  obtain ⟨U,V,hU,hV,hAU,hBV,hUV,hres⟩ :=
    dimension_lowering_separation n univ hwhole A B hA hB hAB
  have hf : frontier U ⊆ (univ : Set X) \ (U ∪ V) := by
    intro x hx
    refine ⟨mem_univ x,?_⟩
    rintro (hu | hv)
    · exact (hU.frontier_eq ▸ hx).2 hu
    · exact disjoint_left.mp (hUV.closure_left hV) (frontier_subset_closure hx) hv
  exact ⟨U,hU,hAU,(hUV.closure_left hV).mono_right hBV,
    (Topology.IsInducing.id.restrict (show MapsTo id (frontier U)
      ((univ : Set X) \ (U ∪ V)) from hf)).hasSmallInductiveDimensionLT hres⟩

end SmallInductiveClosedSum
#print axioms SmallInductiveClosedSum.dimension_lowering_separation

#print axioms SmallInductiveClosedSum.exists_open_small_frontier

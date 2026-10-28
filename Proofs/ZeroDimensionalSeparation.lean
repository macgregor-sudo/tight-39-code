module
public import Mathlib.Topology.SmallInductiveDimension
public import Mathlib.Order.Disjointed

/-! Zero-dimensional separation for second-countable spaces. This is the
noncompact separation prerequisite for the metric countable closed-sum theorem;
no countable-sum theorem or dimension-preserving quotient is assumed. -/
@[expose] public section
noncomputable section
namespace SmallInductiveClosedSum
open Set Topology TopologicalSpace

variable {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]

/-- An adapted countable clopen cover for two disjoint closed sets. -/
theorem countable_clopen_separating_cover
    (hdim : HasSmallInductiveDimensionLE X 0) (A B : Set X)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ U : ℕ → Set X, (∀ n, IsClopen (U n)) ∧ (⋃ n, U n) = univ ∧
      ∀ n, U n ⊆ Aᶜ ∨ U n ⊆ Bᶜ := by
  classical
  obtain ⟨b,hb,hbc,hbasis⟩ := (hasSmallInductiveDimensionLT_one_iff.mp hdim).exists_countable
  let s : Set (Set X) := {u ∈ b | u ⊆ Aᶜ ∨ u ⊆ Bᶜ} ∪ {∅}
  have hs : s.Countable := (hbc.mono (sep_subset _ _)).union (countable_singleton _)
  obtain ⟨U,hU⟩ := hs.exists_eq_range ⟨∅,Or.inr rfl⟩
  have hmem (n : ℕ) : U n ∈ s := hU ▸ mem_range_self n
  have hcl (n : ℕ) : IsClopen (U n) := by
    rcases hmem n with h | h
    · exact hb h.1
    · simpa only [mem_singleton_iff.mp h] using (isClopen_empty : IsClopen (∅ : Set X))
  have hside (n : ℕ) : U n ⊆ Aᶜ ∨ U n ⊆ Bᶜ := by
    rcases hmem n with h | h
    · exact h.2
    · rw [mem_singleton_iff.mp h]; exact Or.inl (empty_subset _)
  refine ⟨U,hcl,?_,hside⟩
  apply eq_univ_of_forall
  intro x
  have hh : ∃ u ∈ b, x ∈ u ∧ (u ⊆ Aᶜ ∨ u ⊆ Bᶜ) := by
    by_cases hx : x ∈ A
    · have hxB : x ∈ Bᶜ := fun hxB => (disjoint_left.mp hAB) hx hxB
      obtain ⟨u,hu,hxu,hus⟩ := hbasis.exists_subset_of_mem_open hxB hB.isOpen_compl
      exact ⟨u,hu,hxu,Or.inr hus⟩
    · obtain ⟨u,hu,hxu,hus⟩ := hbasis.exists_subset_of_mem_open hx hA.isOpen_compl
      exact ⟨u,hu,hxu,Or.inl hus⟩
  obtain ⟨u,hu,hxu,hus⟩ := hh
  have hm : u ∈ s := Or.inl ⟨hu,hus⟩
  rw [hU] at hm
  obtain ⟨n,rfl⟩ := hm
  exact mem_iUnion.mpr ⟨n,hxu⟩

/-- Countable clopen covers admit disjoint clopen refinements, with no compactness. -/
theorem disjoint_clopen_refinement (U : ℕ → Set X) (hU : ∀ n, IsClopen (U n)) :
    (∀ n, IsClopen (disjointed U n)) ∧
      Pairwise (fun i j => Disjoint (disjointed U i) (disjointed U j)) ∧
      (⋃ n, disjointed U n) = ⋃ n, U n ∧
      ∀ n, disjointed U n ⊆ U n := by
  refine ⟨?_,disjoint_disjointed U,iUnion_disjointed,disjointed_subset U⟩
  intro n
  exact disjointedRec (p := IsClopen) (fun {t i} ht => ht.inter (hU i).compl) (hU n)

/-- Zero-dimensional separation between arbitrary disjoint closed subsets of a
second-countable space. Empty sets and empty spaces are included. -/
theorem zero_dimensional_clopen_separator
    (hdim : HasSmallInductiveDimensionLE X 0) (A B : Set X)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ C : Set X, IsClopen C ∧ A ⊆ C ∧ C ⊆ Bᶜ := by
  classical
  obtain ⟨U,hU,hcover,hside⟩ := countable_clopen_separating_cover hdim A B hA hB hAB
  obtain ⟨hd,hdisj,hunion,hsub⟩ := disjoint_clopen_refinement U hU
  let C : Set X := ⋃ n : {n : ℕ // U n ⊆ Bᶜ}, disjointed U n.1
  have hopen : IsOpen C := isOpen_iUnion fun n => (hd n.1).isOpen
  have hcomp : Cᶜ = ⋃ n : {n : ℕ // ¬ U n ⊆ Bᶜ}, disjointed U n.1 := by
    ext x
    constructor
    · intro hx
      have hxall : x ∈ ⋃ n, disjointed U n := by rw [hunion,hcover]; trivial
      obtain ⟨n,hn⟩ := mem_iUnion.mp hxall
      have hnb : ¬ U n ⊆ Bᶜ := fun h => hx (mem_iUnion.mpr ⟨⟨n,h⟩,hn⟩)
      exact mem_iUnion.mpr ⟨⟨n,hnb⟩,hn⟩
    · intro hxall hx
      obtain ⟨n,hn⟩ := mem_iUnion.mp hxall
      obtain ⟨m,hm⟩ := mem_iUnion.mp hx
      have hne : n.1 ≠ m.1 := fun he => n.2 (he ▸ m.2)
      exact (disjoint_left.mp (hdisj hne)) hn hm
  have hclosed : IsClosed C := by
    rw [← isOpen_compl_iff,hcomp]
    exact isOpen_iUnion fun n => (hd n.1).isOpen
  refine ⟨C,⟨hclosed,hopen⟩,?_,?_⟩
  · intro x hx
    have hxall : x ∈ ⋃ n, disjointed U n := by rw [hunion,hcover]; trivial
    obtain ⟨n,hn⟩ := mem_iUnion.mp hxall
    have hnb : U n ⊆ Bᶜ := (hside n).resolve_left (fun h => h (hsub n hn) hx)
    exact mem_iUnion.mpr ⟨⟨n,hnb⟩,hn⟩
  · intro x hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    exact n.2 (hsub n.1 hn)

end SmallInductiveClosedSum
#print axioms SmallInductiveClosedSum.zero_dimensional_clopen_separator

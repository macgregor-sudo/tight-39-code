module
public import CountableClosedSum

/-! Countable- and finite-index forms of the closed-sum theorem. Empty index
types are handled by adjoining an empty stratum before enumerating. -/
@[expose] public section
noncomputable section
namespace SmallInductiveClosedSum
open Set Topology TopologicalSpace
variable {X : Type*} [TopologicalSpace X] [CompletelyNormalSpace X]
  [SecondCountableTopology X] [T1Space X]

/-- The closed-sum theorem for an arbitrary countable index type. -/
theorem countable_index_closed_sum {ι : Type*} [Countable ι]
    (n : ℕ) (F : ι → Set X) (hF : ∀ i, IsClosed (F i))
    (hdim : ∀ i, HasSmallInductiveDimensionLE ↥(F i) n)
    (hcover : (⋃ i, F i) = univ) : HasSmallInductiveDimensionLE X n := by
  classical
  let s : Set (Set X) := range F ∪ {∅}
  have hs : s.Countable := (countable_range F).union (countable_singleton _)
  obtain ⟨U,hU⟩ := hs.exists_eq_range ⟨∅,Or.inr rfl⟩
  have hmem (k : ℕ) : U k ∈ s := hU ▸ mem_range_self k
  have hUc (k : ℕ) : IsClosed (U k) := by
    rcases hmem k with ⟨i,hi⟩ | he
    · rw [← hi]; exact hF i
    · rw [mem_singleton_iff.mp he]; exact isClosed_empty
  have hUd (k : ℕ) : HasSmallInductiveDimensionLE ↥(U k) n := by
    rcases hmem k with ⟨i,hi⟩ | he
    · rw [← hi]; exact hdim i
    · rw [mem_singleton_iff.mp he]; infer_instance
  have hUcover : (⋃ k, U k) = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ i, F i := by rw [hcover]; trivial
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    have hm : F i ∈ s := Or.inl (mem_range_self i)
    rw [hU] at hm
    obtain ⟨k,hk⟩ := hm
    exact mem_iUnion.mpr ⟨k,hk.symm ▸ hi⟩
  exact countable_closed_sum n U hUc hUd hUcover

/-- The finite closed-sum theorem, for arbitrary finite index types including
an empty index type. This is the face-union input for Euclidean normalization. -/
theorem finite_closed_sum {ι : Type*} [Finite ι]
    (n : ℕ) (F : ι → Set X) (hF : ∀ i, IsClosed (F i))
    (hdim : ∀ i, HasSmallInductiveDimensionLE ↥(F i) n)
    (hcover : (⋃ i, F i) = univ) : HasSmallInductiveDimensionLE X n :=
  countable_index_closed_sum n F hF hdim hcover

end SmallInductiveClosedSum
#print axioms SmallInductiveClosedSum.finite_closed_sum

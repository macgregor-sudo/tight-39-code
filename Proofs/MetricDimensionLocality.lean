module
public import ClosedSumConsequences
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.LocallyClosed

/-! The Fσ-cover and open-neighborhood locality consequences required for
finite quotient strata. Fσ is expressed as complement IsGδ, the existing
predicate in this pinned Mathlib; no alternative dimension definition is used. -/
@[expose] public section
noncomputable section
namespace SmallInductiveClosedSum
open Set Topology TopologicalSpace
variable {X : Type*} [MetricSpace X] [SecondCountableTopology X]

/-- Countably many pieces with countable ambient closed exhaustions suffice
for a dimension bound. Closed pieces inherit dimension by actual inclusion. -/
theorem countable_closed_exhaustion_cover {ι : Type*} [Countable ι]
    (n : ℕ) (F : ι → Set X)
    (hF : ∀ i, ∃ C : ℕ → Set X, (∀ k, IsClosed (C k)) ∧ (⋃ k, C k) = F i)
    (hdim : ∀ i, HasSmallInductiveDimensionLE ↥(F i) n)
    (hcover : (⋃ i, F i) = univ) : HasSmallInductiveDimensionLE X n := by
  classical
  choose C hCc hCe using hF
  have hsub (i : ι) (k : ℕ) : C i k ⊆ F i := by
    rw [← hCe i]
    exact subset_iUnion (C i) k
  have hCd (p : ι × ℕ) : HasSmallInductiveDimensionLE ↥(C p.1 p.2) n :=
    (Topology.IsInducing.id.restrict (show MapsTo id (C p.1 p.2) (F p.1) from
      hsub p.1 p.2)).hasSmallInductiveDimensionLE (hdim p.1)
  apply countable_index_closed_sum n (fun p : ι × ℕ => C p.1 p.2)
    (fun p => hCc p.1 p.2) hCd
  apply eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ i, F i := by rw [hcover]; trivial
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  rw [← hCe i] at hi
  obtain ⟨k,hk⟩ := mem_iUnion.mp hi
  exact mem_iUnion.mpr ⟨(i,k),hk⟩

/-- Countable Fσ covers preserve a fixed upper dimension bound. The complement
Gδ hypothesis is exactly Fσ, including for empty pieces or an empty index type. -/
theorem countable_fsigma_cover {ι : Type*} [Countable ι]
    (n : ℕ) (F : ι → Set X) (hF : ∀ i, IsGδ (F i)ᶜ)
    (hdim : ∀ i, HasSmallInductiveDimensionLE ↥(F i) n)
    (hcover : (⋃ i, F i) = univ) : HasSmallInductiveDimensionLE X n := by
  apply countable_closed_exhaustion_cover n F ?_ hdim hcover
  intro i
  obtain ⟨O,hOo,hOe⟩ := (hF i).eq_iInter_nat
  refine ⟨fun k => (O k)ᶜ,fun k => (hOo k).isClosed_compl,?_⟩
  rw [← compl_iInter,← hOe,compl_compl]

/-- Countable locally closed covers preserve dimension bounds, including the
finite stratification case used for finite group quotients. -/
theorem countable_locallyClosed_cover {ι : Type*} [Countable ι]
    (n : ℕ) (F : ι → Set X) (hF : ∀ i, IsLocallyClosed (F i))
    (hdim : ∀ i, HasSmallInductiveDimensionLE ↥(F i) n)
    (hcover : (⋃ i, F i) = univ) : HasSmallInductiveDimensionLE X n := by
  apply countable_closed_exhaustion_cover n F ?_ hdim hcover
  intro i
  obtain ⟨O,Z,hO,hZ,he⟩ := hF i
  obtain ⟨C,hCc,_,hCe,_⟩ := hO.exists_iUnion_isClosed
  refine ⟨fun k => C k ∩ Z,fun k => (hCc k).inter hZ,?_⟩
  rw [← iUnion_inter,hCe,← he]

/-- An arbitrary open cover by subspaces of dimension at most n gives the same
global bound. Second countability supplies the countable subcover. -/
theorem dimension_le_of_open_cover {ι : Type*} (n : ℕ) (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hdim : ∀ i, HasSmallInductiveDimensionLE ↥(U i) n)
    (hcover : (⋃ i, U i) = univ) : HasSmallInductiveDimensionLE X n := by
  classical
  obtain ⟨r,hr,hrcover⟩ := isLindelof_univ.elim_countable_subcover U hU
    (show (univ : Set X) ⊆ ⋃ i, U i by rw [hcover])
  letI : Countable r := hr.to_subtype
  refine countable_closed_exhaustion_cover n (fun i : r => U i.1) ?_ (fun i => hdim i.1) ?_
  · intro i
    obtain ⟨C,hCc,_,hCe,_⟩ := (hU i.1).exists_iUnion_isClosed
    exact ⟨C,hCc,hCe⟩
  · apply eq_univ_of_forall
    intro x
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hrcover (mem_univ x))
    obtain ⟨hir,hx⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨⟨i,hir⟩,hx⟩

/-- Metric locality of a fixed upper bound for small inductive dimension. -/
theorem dimension_le_of_open_neighborhoods (n : ℕ)
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      HasSmallInductiveDimensionLE ↥U n) : HasSmallInductiveDimensionLE X n := by
  classical
  choose U hU hxU hdim using h
  apply dimension_le_of_open_cover n U hU hdim
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨x,hxU x⟩

end SmallInductiveClosedSum
#print axioms SmallInductiveClosedSum.countable_fsigma_cover
#print axioms SmallInductiveClosedSum.countable_locallyClosed_cover
#print axioms SmallInductiveClosedSum.dimension_le_of_open_neighborhoods

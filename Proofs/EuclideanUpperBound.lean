module

public import BoxBoundaryEuclidean

@[expose] public section

/-! Euclidean upper-bound induction for Mathlib's EXISTING small inductive
dimension. FiniteClosedSumContract is a explicit theorem parameter;
it is not an axiom and this file does not claim unconditional normalization.
It matches the metric specialization of the closed-sum theorem.
-/
noncomputable section
namespace SmallInductiveEuclideanA7
open Set TopologicalSpace

/-- The finite closed-sum hypothesis. All uses below are actual finite closed
covers of box-boundary subtypes. The metric hypotheses supply complete normality
and T1 to the general D2 implementation. -/
def FiniteClosedSumContract : Prop :=
  ∀ (X ι : Type) [MetricSpace X] [SecondCountableTopology X] [Finite ι]
    (n : ℕ) (F : ι → Set X),
    (∀ i, IsClosed (F i)) →
    (∀ i, HasSmallInductiveDimensionLE ↥(F i) n) →
    (⋃ i, F i) = Set.univ → HasSmallInductiveDimensionLE X n

/-- The dimension-zero starting point does not use the sum contract. -/
theorem pi_zero_smallInductiveDimensionLE : HasSmallInductiveDimensionLE (Fin 0 → ℝ) 0 := by
  apply hasSmallInductiveDimensionLT_one_iff.2
  apply isTopologicalBasis_of_isOpen_of_nhds (fun _ h => h.isOpen)
  intro x U hx _
  refine ⟨Set.univ,isClopen_univ,Set.mem_univ _,?_⟩
  intro y _
  simpa only [Subsingleton.elim y x] using hx

/-- Each frontier in the actual box basis has the expected inductive bound,
using coordinate deletion and only the visible finite closed-sum join. -/
theorem box_frontier_smallInductiveDimensionLE
    (hsum : FiniteClosedSumContract) {n : ℕ}
    (hind : HasSmallInductiveDimensionLE (Fin n → ℝ) n)
    {a b : Fin (n+1) → ℝ} (hab : ∀ i, a i < b i) :
    HasSmallInductiveDimensionLE ↥(frontier (openBox a b)) n := by
  let X := frontier (openBox a b)
  let ι := Fin (n+1) × Bool
  let F : ι → Set X := fun j => Subtype.val ⁻¹' boxFace a b j.1 j.2
  obtain ⟨hclosed,hcover⟩ := frontier_face_closed_cover hab
  apply hsum X ι n F hclosed ?_ hcover
  intro j
  let f : F j → boxFace a b j.1 j.2 := fun x => ⟨x.1.1,x.2⟩
  have hf : Topology.IsEmbedding f :=
    (Topology.IsEmbedding.subtypeVal.of_comp_iff).1
      (show Topology.IsEmbedding (Subtype.val ∘ f) from
        (show Topology.IsEmbedding (Subtype.val : X → (Fin (n+1) → ℝ)) from
          Topology.IsEmbedding.subtypeVal).comp
        (show Topology.IsEmbedding (Subtype.val : F j → X) from
          Topology.IsEmbedding.subtypeVal))
  exact ((isEmbedding_face_removeNth a b j.1 j.2).comp hf).toIsInducing.hasSmallInductiveDimensionLE hind

/-- Conditional only on the explicitly named D2 theorem: the genuine
small-inductive upper-bound induction, including n=0. -/
theorem pi_smallInductiveDimensionLE (hsum : FiniteClosedSumContract) (n : ℕ) :
    HasSmallInductiveDimensionLE (Fin n → ℝ) n := by
  induction n with
  | zero => exact pi_zero_smallInductiveDimensionLE
  | succ n ih =>
    apply HasSmallInductiveDimensionLT.succ (n+1) _ (openBox_basis (n+1))
    rintro U ⟨a,b,hab,rfl⟩
    exact box_frontier_smallInductiveDimensionLE hsum ih hab

theorem euclidean_smallInductiveDimensionLE (hsum : FiniteClosedSumContract) (n : ℕ) :
    HasSmallInductiveDimensionLE (EuclideanSpace ℝ (Fin n)) n :=
  (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).toHomeomorph.isInducing.hasSmallInductiveDimensionLE
    (pi_smallInductiveDimensionLE hsum n)

theorem euclidean_smallInductiveDimension_le (hsum : FiniteClosedSumContract) (n : ℕ) :
    smallInductiveDimension (EuclideanSpace ℝ (Fin n)) ≤ (n : WithBot ℕ∞) :=
  smallInductiveDimension_le_iff.2 (euclidean_smallInductiveDimensionLE hsum n)

/-- The upper bound holds for every subspace, hence also every nonempty
open subtype; no unproved locality or lower-bound premise is hidden here. -/
theorem euclidean_subtype_smallInductiveDimension_le (hsum : FiniteClosedSumContract)
    (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) :
    smallInductiveDimension A ≤ (n : WithBot ℕ∞) :=
  smallInductiveDimension_subtype_le.trans (euclidean_smallInductiveDimension_le hsum n)

#print axioms pi_zero_smallInductiveDimensionLE
#print axioms box_frontier_smallInductiveDimensionLE
#print axioms euclidean_smallInductiveDimension_le
#print axioms euclidean_subtype_smallInductiveDimension_le
end SmallInductiveEuclideanA7

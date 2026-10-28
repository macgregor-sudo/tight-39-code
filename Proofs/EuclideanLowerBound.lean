module

public import CubeSeparation
public import DimensionLoweringSeparation
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-! Actual small-inductive lower bound from the proved dimension-lowering
separator and the proved cube opposite-face theorem. The partition iteration
keeps one ambient space and decreases dimension of its residual subset; no
partition-extension or normalization hypothesis is assumed.
Uses the dimension-lowering separation and Brouwer fixed-point theorems.
-/
noncomputable section
namespace SmallInductiveEuclideanA7
open Set Topology TopologicalSpace

/-- The forward partition theorem needed for Euclidean normalization.
With ind(M)<n, n disjoint closed pairs admit separating open sets whose unions
cover M. The empty-index case follows from the actual LT-zero definition. -/
theorem separating_pairs_cover_residual
    {X : Type*} [TopologicalSpace X] [CompletelyNormalSpace X]
    [SecondCountableTopology X] [T1Space X]
    (n : ℕ) (M : Set X) (hM : HasSmallInductiveDimensionLT ↥M n)
    (A B : Fin n → Set X) (hA : ∀ i, IsClosed (A i))
    (hB : ∀ i, IsClosed (B i)) (hAB : ∀ i, Disjoint (A i) (B i)) :
    ∃ U V : Fin n → Set X,
      (∀ i, IsOpen (U i) ∧ IsOpen (V i) ∧ A i ⊆ U i ∧ B i ⊆ V i ∧ Disjoint (U i) (V i)) ∧
      ∀ x ∈ M, ∃ i, x ∈ U i ∨ x ∈ V i := by
  induction n generalizing M with
  | zero =>
    have he : IsEmpty ↥M := hasSmallInductiveDimensionLT_zero_iff.1 hM
    refine ⟨(fun i => Fin.elim0 i),(fun i => Fin.elim0 i),(fun i => Fin.elim0 i),?_⟩
    intro x hx
    exact (he.false ⟨x,hx⟩).elim
  | succ n ih =>
    obtain ⟨U₀,V₀,hU₀,hV₀,hAU,hBV,hdisj,hres⟩ :=
      SmallInductiveClosedSum.dimension_lowering_separation n M hM (A 0) (B 0) (hA 0) (hB 0) (hAB 0)
    obtain ⟨U,V,hUV,hcov⟩ := ih (M \ (U₀ ∪ V₀)) hres
      (fun i => A i.succ) (fun i => B i.succ)
      (fun i => hA i.succ) (fun i => hB i.succ) (fun i => hAB i.succ)
    refine ⟨Fin.cons U₀ U,Fin.cons V₀ V,?_,?_⟩
    · intro i
      exact Fin.cases ⟨hU₀,hV₀,hAU,hBV,hdisj⟩ (fun j => hUV j) i
    · intro x hx
      by_cases hfirst : x ∈ U₀ ∪ V₀
      · exact ⟨0,hfirst⟩
      · obtain ⟨i,hi⟩ := hcov x ⟨hx,hfirst⟩
        exact ⟨i.succ,hi⟩

/-- The closed cube cannot have small inductive dimension less than its
coordinate count; the n=0 cube is nonempty and is covered by the same proof. -/
theorem cube_not_hasSmallInductiveDimensionLT (n : ℕ) :
    ¬ HasSmallInductiveDimensionLT (@unit_cube n) n := by
  intro hdim
  let A : Fin n → Set (@unit_cube n) := fun i => {x | x.1 i = 0}
  let B : Fin n → Set (@unit_cube n) := fun i => {x | x.1 i = 1}
  have hA : ∀ i, IsClosed (A i) := fun i =>
    isClosed_eq ((continuous_apply i).comp continuous_subtype_val) continuous_const
  have hB : ∀ i, IsClosed (B i) := fun i =>
    isClosed_eq ((continuous_apply i).comp continuous_subtype_val) continuous_const
  have hAB : ∀ i, Disjoint (A i) (B i) := by
    intro i
    apply Set.disjoint_left.2
    intro x hx hy
    have hx' : x.1 i = 0 := hx
    have hy' : x.1 i = 1 := hy
    linarith
  have hM : HasSmallInductiveDimensionLT ↥(Set.univ : Set (@unit_cube n)) n :=
    Topology.IsInducing.subtypeVal.hasSmallInductiveDimensionLT hdim
  obtain ⟨U,V,hUV,hcover⟩ := separating_pairs_cover_residual n Set.univ hM A B hA hB hAB
  obtain ⟨x,hx⟩ := cube_opposite_face_partitions_intersect
    (fun i => (U i ∪ V i)ᶜ) U V
    (fun i => (hUV i).1) (fun i => (hUV i).2.1)
    (fun i => (hUV i).2.2.2.2)
    (fun x i hx => (hUV i).2.2.1 hx)
    (fun x i hx => (hUV i).2.2.2.1 hx)
    (fun i => compl_compl _)
  obtain ⟨i,hi⟩ := hcover x (Set.mem_univ _)
  exact hx i hi

/-- Genuine embedding of the actual cube into Euclidean n-space. -/
theorem cube_euclidean_isEmbedding (n : ℕ) :
    Topology.IsEmbedding (fun x : @unit_cube n =>
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x.1) :=
  (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm.toHomeomorph.isEmbedding.comp
    Topology.IsEmbedding.subtypeVal

theorem euclidean_not_hasSmallInductiveDimensionLT (n : ℕ) :
    ¬ HasSmallInductiveDimensionLT (EuclideanSpace ℝ (Fin n)) n := by
  intro h
  exact cube_not_hasSmallInductiveDimensionLT n
    ((cube_euclidean_isEmbedding n).toIsInducing.hasSmallInductiveDimensionLT h)

theorem euclidean_smallInductiveDimension_lower_bound (n : ℕ) :
    (n : WithBot ℕ∞) ≤ smallInductiveDimension (EuclideanSpace ℝ (Fin n)) := by
  rw [← not_lt,smallInductiveDimension_lt_iff]
  exact euclidean_not_hasSmallInductiveDimensionLT n

#print axioms separating_pairs_cover_residual
#print axioms cube_not_hasSmallInductiveDimensionLT
#print axioms euclidean_smallInductiveDimension_lower_bound
end SmallInductiveEuclideanA7

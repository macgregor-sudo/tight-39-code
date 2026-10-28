module
public import DimensionDecomposition
public import FrontierControlledBasis
public import ZeroDimensionalClosedSum
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Data.Nat.Pairing

/-! The separable metrizable countable closed-sum theorem for Mathlib's small
inductive dimension. The proof works for second-countable completely normal T₁
spaces and uses induction through the union of the relative basis frontiers. -/
@[expose] public section
noncomputable section
namespace SmallInductiveClosedSum
open Set Topology TopologicalSpace

/-- Restricting an ambient subspace to another subset cannot raise dimension. -/
theorem subtype_preimage_dimension_le {X : Type*} [TopologicalSpace X]
    (Y D : Set X) (n : ℕ) (hD : HasSmallInductiveDimensionLE ↥D n) :
    HasSmallInductiveDimensionLE ↥((Subtype.val : Y → X) ⁻¹' D) n := by
  let f : ↥((Subtype.val : Y → X) ⁻¹' D) → D := fun y => ⟨y.1.1,y.2⟩
  have hf : IsInducing f := by
    apply Topology.IsInducing.subtypeVal.of_comp_iff.mp
    change IsInducing ((Subtype.val : Y → X) ∘ Subtype.val)
    exact Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  exact hf.hasSmallInductiveDimensionLE hD

/-- The countable closed-sum theorem, including empty strata and empty spaces.
In particular it applies to every second-countable metric space. -/
theorem countable_closed_sum {X : Type*} [TopologicalSpace X]
    [CompletelyNormalSpace X] [SecondCountableTopology X] [T1Space X]
    (n : ℕ) (F : ℕ → Set X) (hF : ∀ i, IsClosed (F i))
    (hdim : ∀ i, HasSmallInductiveDimensionLE ↥(F i) n)
    (hcover : (⋃ i, F i) = univ) : HasSmallInductiveDimensionLE X n := by
  classical
  induction n generalizing X with
  | zero => exact zero_dimensional_countable_closed_sum F hF hdim hcover
  | succ n IH =>
    choose U hUb hUf using fun i => exists_countable_frontier_controlled_basis (n+1) (hdim i)
    let D : ℕ → Set X := fun k => Subtype.val '' frontier (U k.unpair.1 k.unpair.2)
    have hDc (k : ℕ) : IsClosed (D k) :=
      (hF k.unpair.1).isClosedMap_subtype_val _ isClosed_frontier
    have hDd (k : ℕ) : HasSmallInductiveDimensionLE ↥(D k) n := by
      exact (Topology.IsEmbedding.subtypeVal.homeomorphImage
        (frontier (U k.unpair.1 k.unpair.2))).symm.isInducing.hasSmallInductiveDimensionLE
          (hUf k.unpair.1 k.unpair.2)
    let Y : Set X := ⋃ k, D k
    let G : ℕ → Set Y := fun k => Subtype.val ⁻¹' D k
    have hGc (k : ℕ) : IsClosed (G k) := (hDc k).preimage continuous_subtype_val
    have hGd (k : ℕ) : HasSmallInductiveDimensionLE ↥(G k) n :=
      subtype_preimage_dimension_le Y (D k) n (hDd k)
    have hGcover : (⋃ k, G k) = univ := by
      apply eq_univ_of_forall
      intro y
      obtain ⟨k,hk⟩ := mem_iUnion.mp y.2
      exact mem_iUnion.mpr ⟨k,hk⟩
    have hY : HasSmallInductiveDimensionLE ↥Y n := IH G hGc hGd hGcover
    let Z : Set X := Yᶜ
    let H : ℕ → Set Z := fun i => Subtype.val ⁻¹' F i
    have hHc (i : ℕ) : IsClosed (H i) := (hF i).preimage continuous_subtype_val
    have hHd (i : ℕ) : HasSmallInductiveDimensionLE ↥(H i) 0 := by
      let f : H i → F i := fun z => ⟨z.1.1,z.2⟩
      have hf : IsInducing f := by
        apply Topology.IsInducing.subtypeVal.of_comp_iff.mp
        change IsInducing ((Subtype.val : Z → X) ∘ Subtype.val)
        exact Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
      apply zero_dimensional_of_avoids_basis_frontiers hf (range (U i)) (hUb i)
      rintro z W ⟨j,rfl⟩ hz
      apply z.1.2
      apply mem_iUnion.mpr
      refine ⟨Nat.pair i j,?_⟩
      change z.1.1 ∈ Subtype.val '' frontier (U (Nat.unpair (Nat.pair i j)).1
        (Nat.unpair (Nat.pair i j)).2)
      rw [Nat.unpair_pair]
      exact ⟨f z,hz,rfl⟩
    have hHcover : (⋃ i, H i) = univ := by
      apply eq_univ_of_forall
      intro z
      have hz : z.1 ∈ ⋃ i, F i := by rw [hcover]; trivial
      obtain ⟨i,hi⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨i,hi⟩
    have hZ : HasSmallInductiveDimensionLE ↥Z 0 :=
      zero_dimensional_countable_closed_sum H hHc hHd hHcover
    exact dimension_le_of_union_zero_dimensional (n+1) Y Z hY hZ (union_compl_self Y)

end SmallInductiveClosedSum
#print axioms SmallInductiveClosedSum.countable_closed_sum

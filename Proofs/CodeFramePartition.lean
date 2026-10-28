module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-!
# A 39-point Gram matrix with rank at most 27 forces thirteen triples

Let `G` be a real symmetric `39 × 39` matrix with unit diagonal, off-diagonal entries in
`{0, 1/3}`, every row sum equal to `13` and rank at most `27`. Then the indices split into
thirteen triples: distinct indices have entry `0` exactly when they lie in the same triple, and
entry `1/3` otherwise (`exists_equiv_triples`).

## Proof

Let `H` be the graph whose edges are the distinct pairs with zero entry (`zeroGraph`). The row
sums force every vertex to have degree two, and then `3 • G = L + J`, where `L` is the Laplacian
matrix of `H` and `J` is the all-ones matrix. Since the coordinates of `L v` always sum to zero,
`ker (L + J) ⊆ ker L`. The constant vector lies in `ker L` but not in `ker (L + J)`, so
`rank G ≥ 40 − c`, where `c` is the number of connected components of `H`. Rank at most `27`
gives `c ≥ 13`. Every component of a 2-regular simple graph has at least three vertices, so
`c ≤ 13`. Hence every component is a closed neighbourhood `{v} ∪ N(v)` of exactly three
vertices, i.e. a triangle.

## References

The identification of the kernel of the Laplacian with functions constant on connected
components is `SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix` in
`Mathlib.Combinatorics.SimpleGraph.LapMatrix` (Adrian Wüthrich), used here through its public
API.
-/

open Matrix SimpleGraph Finset

namespace CKM.CodeFramePartition

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph on the index set whose edges are the distinct pairs with vanishing entry. -/
def zeroGraph (G : Matrix V V ℝ) : SimpleGraph V :=
  SimpleGraph.fromRel fun i j => G i j = 0

instance (G : Matrix V V ℝ) : DecidableRel (zeroGraph G).Adj := Classical.decRel _

/-! ### Degrees and the identity `3 • G = L + J` -/

omit [Fintype V] [DecidableEq V] in
theorem zeroGraph_adj_iff {G : Matrix V V ℝ} (hsymm : G.IsSymm) {i j : V} :
    (zeroGraph G).Adj i j ↔ i ≠ j ∧ G i j = 0 := by
  rw [zeroGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, by rw [← hsymm.apply i j]; exact h⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

omit [Fintype V] in
/-- Entrywise affine form of `G`: every entry is `1/3`, plus `2/3` on the diagonal,
minus `1/3` on the edges of the zero graph. -/
private lemma entry_eq {G : Matrix V V ℝ} (hsymm : G.IsSymm) (hdiag : ∀ i, G i i = 1)
    (hoff : ∀ i j, i ≠ j → G i j = 0 ∨ G i j = (1 / 3 : ℝ)) (i j : V) :
    G i j = 1 / 3 + 2 / 3 * (if i = j then 1 else 0)
      - 1 / 3 * (if (zeroGraph G).Adj i j then 1 else 0) := by
  by_cases hij : i = j
  · subst hij
    simp only [hdiag, ite_true, SimpleGraph.irrefl, ite_false]
    norm_num
  · rcases hoff i j hij with h | h
    · have hadj : (zeroGraph G).Adj i j := (zeroGraph_adj_iff hsymm).2 ⟨hij, h⟩
      simp only [h, hij, hadj, ite_true, ite_false]
      norm_num
    · have hadj : ¬ (zeroGraph G).Adj i j := fun ha =>
        by have := ((zeroGraph_adj_iff hsymm).1 ha).2; rw [h] at this; norm_num at this
      simp only [h, hij, hadj, ite_false]
      norm_num

theorem sum_row_eq {G : Matrix V V ℝ} (hsymm : G.IsSymm) (hdiag : ∀ i, G i i = 1)
    (hoff : ∀ i j, i ≠ j → G i j = 0 ∨ G i j = (1 / 3 : ℝ)) (i : V) :
    ∑ j, G i j = 1 + ((Fintype.card V : ℝ) - 1 - ((zeroGraph G).degree i : ℝ)) / 3 := by
  rw [Finset.sum_congr rfl fun j _ => entry_eq hsymm hdiag hoff i j,
    (zeroGraph G).degree_eq_sum_if_adj (R := ℝ) i]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Finset.sum_ite_eq, Finset.mem_univ, ite_true, nsmul_eq_mul]
  ring

theorem degree_eq_two {G : Matrix (Fin 39) (Fin 39) ℝ} (hsymm : G.IsSymm)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → G i j = 0 ∨ G i j = (1 / 3 : ℝ))
    (hrow : ∀ i, ∑ j, G i j = 13) (i : Fin 39) : (zeroGraph G).degree i = 2 := by
  have h := sum_row_eq hsymm hdiag hoff i
  rw [hrow i, Fintype.card_fin] at h
  have h2 : ((zeroGraph G).degree i : ℝ) = 2 := by push_cast at h; linarith
  exact_mod_cast h2

theorem three_smul_eq_lapMatrix_add {G : Matrix V V ℝ} (hsymm : G.IsSymm)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → G i j = 0 ∨ G i j = (1 / 3 : ℝ))
    (hdeg : ∀ i, (zeroGraph G).degree i = 2) :
    (3 : ℝ) • G = (zeroGraph G).lapMatrix ℝ + Matrix.of fun _ _ => (1 : ℝ) := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, entry_eq hsymm hdiag hoff i j, Matrix.add_apply,
    Matrix.of_apply, lapMatrix, Matrix.sub_apply, degMatrix, Matrix.diagonal_apply, adjMatrix_apply,
    hdeg i]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true, SimpleGraph.irrefl, ite_false]
    norm_num
  · by_cases hadj : (zeroGraph G).Adj i j
    · simp only [hij, hadj, ite_true, ite_false]
      norm_num
    · simp only [hij, hadj, ite_false]
      norm_num

/-! ### Rank and connected components -/

/-- The coordinates of `L *ᵥ v` sum to zero: `L` is symmetric and `L *ᵥ 1 = 0`. -/
private lemma sum_lapMatrix_mulVec (H : SimpleGraph V) [DecidableRel H.Adj] (v : V → ℝ) :
    ∑ i, (H.lapMatrix ℝ *ᵥ v) i = 0 := by
  rw [← one_dotProduct, dotProduct_mulVec, ← mulVec_transpose, (H.isSymm_lapMatrix ℝ).eq,
    H.lapMatrix_mulVec_one_eq_zero ℝ, zero_dotProduct]

omit [DecidableEq V] in
/-- The all-ones matrix sends `v` to the constant vector `∑ v`. -/
private lemma ones_mulVec (v : V → ℝ) :
    (Matrix.of fun _ _ => (1 : ℝ) : Matrix V V ℝ) *ᵥ v = fun _ => ∑ j, v j := by
  ext i
  simp [mulVec, dotProduct]

/-- `ker (L + J)` is a proper subspace of `ker L`; the constant vector separates them. -/
private lemma ker_lapMatrix_add_ones_lt (H : SimpleGraph V) [DecidableRel H.Adj] [Nonempty V] :
    LinearMap.ker (H.lapMatrix ℝ + Matrix.of fun _ _ => (1 : ℝ)).mulVecLin <
      LinearMap.ker (H.lapMatrix ℝ).toLin' := by
  have hcard : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Matrix.toLin'_apply']
  refine lt_of_le_of_ne (fun v hv => ?_) (fun heq => ?_)
  · rw [LinearMap.mem_ker, mulVecLin_apply] at hv ⊢
    rw [add_mulVec, ones_mulVec] at hv
    -- Summing the coordinates of `(L + J) v = 0` gives `card V * ∑ v = 0`.
    have hs : ∑ j, v j = 0 := by
      have h := congrArg (fun w => ∑ i, w i) hv
      simp only [Pi.add_apply, Finset.sum_add_distrib, sum_lapMatrix_mulVec, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, zero_add, Pi.zero_apply, mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hcard
    rw [hs] at hv
    exact (add_zero _).symm.trans hv
  · have h1 : (1 : V → ℝ) ∈ LinearMap.ker (H.lapMatrix ℝ).mulVecLin := by
      rw [LinearMap.mem_ker, mulVecLin_apply, H.lapMatrix_mulVec_one_eq_zero ℝ]
    rw [← heq, LinearMap.mem_ker, mulVecLin_apply, add_mulVec, H.lapMatrix_mulVec_one_eq_zero ℝ,
      ones_mulVec] at h1
    have h := congrFun h1 (Classical.arbitrary V)
    simp only [Pi.one_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      zero_add, Pi.zero_apply] at h
    exact hcard h

theorem card_add_one_le_rank_add_card_connectedComponent (H : SimpleGraph V)
    [DecidableRel H.Adj] [Nonempty V] :
    Fintype.card V + 1 ≤
      (H.lapMatrix ℝ + Matrix.of fun _ _ => (1 : ℝ)).rank + Fintype.card H.ConnectedComponent := by
  have hrn :=
    LinearMap.finrank_range_add_finrank_ker (H.lapMatrix ℝ + Matrix.of fun _ _ => (1 : ℝ)).mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  have hlt := Submodule.finrank_lt_finrank_of_lt (ker_lapMatrix_add_ones_lt H)
  rw [← H.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix] at hlt
  unfold Matrix.rank
  omega

/-! ### Components of a 2-regular graph -/

/-- The closed neighbourhood `{v} ∪ N(v)` of a vertex of degree two has three elements. -/
private theorem card_insert_neighborFinset (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ v, H.degree v = 2) (v : V) : #(insert v (H.neighborFinset v)) = 3 := by
  rw [card_insert_of_notMem (H.notMem_neighborFinset_self v), card_neighborFinset_eq_degree,
    hdeg]

/-- The closed neighbourhood of `v` lies in the fiber of `v`'s connected component. -/
private theorem insert_neighborFinset_subset_fiber (H : SimpleGraph V) [DecidableRel H.Adj]
    [DecidableEq H.ConnectedComponent] (v : V) :
    insert v (H.neighborFinset v) ⊆
      ({w | H.connectedComponentMk w = H.connectedComponentMk v} : Finset V) := by
  intro w hw
  rw [mem_insert, mem_neighborFinset] at hw
  rw [mem_filter]
  refine ⟨mem_univ _, ?_⟩
  rcases hw with rfl | hadj
  · rfl
  · exact (ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm

/-- Every component fiber of a 2-regular graph has at least three vertices. -/
private theorem three_le_card_fiber (H : SimpleGraph V) [DecidableRel H.Adj]
    [DecidableEq H.ConnectedComponent]
    (hdeg : ∀ v, H.degree v = 2) (C : H.ConnectedComponent) :
    3 ≤ #{w | H.connectedComponentMk w = C} := by
  obtain ⟨v, rfl⟩ := C.exists_rep
  rw [← card_insert_neighborFinset H hdeg v]
  exact card_le_card (insert_neighborFinset_subset_fiber H v)

/-- The vertex count is the sum of the component fiber sizes. -/
private theorem card_eq_sum_card_fiber (H : SimpleGraph V) [DecidableRel H.Adj]
    [DecidableEq H.ConnectedComponent] :
    Fintype.card V = ∑ C : H.ConnectedComponent, #{w | H.connectedComponentMk w = C} :=
  card_eq_sum_card_fiberwise (f := H.connectedComponentMk) (s := univ) (t := univ)
    (fun _ _ => mem_coe.mpr (mem_univ _))

/-- Under the counting bound, every component fiber has exactly three vertices (finset form). -/
private theorem card_fiber_finset_eq_three (H : SimpleGraph V) [DecidableRel H.Adj]
    [DecidableEq H.ConnectedComponent]
    (hdeg : ∀ v, H.degree v = 2)
    (hle : Fintype.card V ≤ 3 * Fintype.card H.ConnectedComponent) (C : H.ConnectedComponent) :
    #{w | H.connectedComponentMk w = C} = 3 := by
  refine le_antisymm ?_ (three_le_card_fiber H hdeg C)
  by_contra hlt
  push Not at hlt
  -- one fiber larger than three makes the fiber sum exceed `3 * #components`
  have hsum : ∑ _C : H.ConnectedComponent, 3 <
      ∑ C : H.ConnectedComponent, #{w | H.connectedComponentMk w = C} :=
    sum_lt_sum (fun C _ => three_le_card_fiber H hdeg C) ⟨C, mem_univ _, hlt⟩
  rw [← card_eq_sum_card_fiber, sum_const, card_univ, smul_eq_mul, mul_comm] at hsum
  omega

theorem three_mul_card_connectedComponent_le (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ v, H.degree v = 2) :
    3 * Fintype.card H.ConnectedComponent ≤ Fintype.card V := by
  classical
  rw [card_eq_sum_card_fiber H, mul_comm, ← smul_eq_mul, ← card_univ, ← sum_const]
  exact sum_le_sum fun C _ => three_le_card_fiber H hdeg C

theorem card_fiber_eq_three (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ v, H.degree v = 2)
    (hle : Fintype.card V ≤ 3 * Fintype.card H.ConnectedComponent) (C : H.ConnectedComponent) :
    Nat.card {v // H.connectedComponentMk v = C} = 3 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_fiber_finset_eq_three H hdeg hle C

theorem adj_of_connectedComponentMk_eq (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ v, H.degree v = 2)
    (hle : Fintype.card V ≤ 3 * Fintype.card H.ConnectedComponent) {u w : V} (huw : u ≠ w)
    (h : H.connectedComponentMk u = H.connectedComponentMk w) : H.Adj u w := by
  classical
  -- the closed neighbourhood of `u` fills `u`'s three-element fiber
  have heq := eq_of_subset_of_card_le (insert_neighborFinset_subset_fiber H u)
    (by rw [card_fiber_finset_eq_three H hdeg hle _, card_insert_neighborFinset H hdeg])
  have hw : w ∈ insert u (H.neighborFinset u) := by
    rw [heq, mem_filter]
    exact ⟨mem_univ _, h.symm⟩
  rw [mem_insert, mem_neighborFinset] at hw
  exact hw.resolve_left (Ne.symm huw)

/-! ### The thirteen triples -/

/-- A real symmetric `39 × 39` matrix with unit diagonal, off-diagonal entries in `{0, 1/3}`,
all row sums `13` and rank at most `27` is, after relabelling, block-structured by thirteen
triples: distinct indices have entry `0` exactly when they lie in the same triple. -/
theorem exists_equiv_triples (G : Matrix (Fin 39) (Fin 39) ℝ) (hsymm : G.IsSymm)
    (hdiag : ∀ i, G i i = 1) (hoff : ∀ i j, i ≠ j → G i j = 0 ∨ G i j = (1 / 3 : ℝ))
    (hrow : ∀ i, ∑ j, G i j = 13) (hrank : G.rank ≤ 27) :
    ∃ e : Fin 39 ≃ (Fin 13 × Fin 3),
      (∀ i j, i ≠ j → (G i j = 0 ↔ (e i).1 = (e j).1)) ∧
      (∀ i j, i ≠ j → (e i).1 = (e j).1 → G i j = 0) ∧
      (∀ i j, (e i).1 ≠ (e j).1 → G i j = 1 / 3) := by
  set H := zeroGraph G
  have hdeg : ∀ i, H.degree i = 2 := degree_eq_two hsymm hdiag hoff hrow
  -- `3 • G = L + J` and scaling by `3` preserves rank, so `40 ≤ rank G + #components`.
  have hrankLJ : (H.lapMatrix ℝ + Matrix.of fun _ _ => (1 : ℝ)).rank = G.rank := by
    rw [← three_smul_eq_lapMatrix_add hsymm hdiag hoff hdeg]
    exact rank_smul_of_mem_nonZeroDivisors G (mem_nonZeroDivisors_of_ne_zero three_ne_zero)
  have hB := card_add_one_le_rank_add_card_connectedComponent H
  have hC := three_mul_card_connectedComponent_le H hdeg
  rw [hrankLJ, Fintype.card_fin] at hB
  rw [Fintype.card_fin] at hC
  have hcard : Fintype.card H.ConnectedComponent = 13 := by omega
  have hle : Fintype.card (Fin 39) ≤ 3 * Fintype.card H.ConnectedComponent := by
    rw [Fintype.card_fin]; omega
  have hfib := card_fiber_eq_three H hdeg hle
  -- Label components by `Fin 13` and the three points of each component by `Fin 3`.
  let f : H.ConnectedComponent ≃ Fin 13 := Fintype.equivFinOfCardEq hcard
  let g : ∀ C : H.ConnectedComponent, {v // H.connectedComponentMk v = C} ≃ Fin 3 :=
    fun C => (Finite.equivFin _).trans (finCongr (hfib C))
  let e : Fin 39 ≃ (Fin 13 × Fin 3) :=
    (Equiv.sigmaFiberEquiv H.connectedComponentMk).symm.trans
      ((Equiv.sigmaCongrRight g).trans
        ((Equiv.sigmaEquivProd _ _).trans (Equiv.prodCongr f (Equiv.refl _))))
  have he : ∀ i, (e i).1 = f (H.connectedComponentMk i) := fun _ => rfl
  have hsame : ∀ i j, (e i).1 = (e j).1 ↔ H.connectedComponentMk i = H.connectedComponentMk j :=
    fun i j => by rw [he, he, f.injective.eq_iff]
  have hzero : ∀ i j, i ≠ j → (G i j = 0 ↔ (e i).1 = (e j).1) := by
    intro i j hij
    rw [hsame, ← (zeroGraph_adj_iff hsymm).trans (and_iff_right hij)]
    exact ⟨ConnectedComponent.connectedComponentMk_eq_of_adj,
      adj_of_connectedComponentMk_eq H hdeg hle hij⟩
  refine ⟨e, hzero, fun i j hij h => (hzero i j hij).2 h, fun i j h => ?_⟩
  have hij : i ≠ j := by rintro rfl; exact h rfl
  exact (hoff i j hij).resolve_left fun h0 => h ((hzero i j hij).1 h0)

end

end CKM.CodeFramePartition

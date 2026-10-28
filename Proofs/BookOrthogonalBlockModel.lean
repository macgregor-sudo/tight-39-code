module

public import BookHTQuartic
public import FirstBlockLimitV3
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-! A Euclidean carrier for the four complex triples. The coordinate map to the
unchanged BookHT.Blocks is a continuous real-linear equivalence. No isometry
with the outer Pi maximum norm is asserted. This module concerns only the Book
H/T common zero cone, without a native residual or sheet-exhaustion claim. -/
noncomputable section

namespace Option2.NativeStress.BookOrthogonal

open scoped BigOperators InnerProductSpace

set_option autoImplicit false
set_option Elab.async false

/-- All twelve complex coordinates with their finite Euclidean norm. -/
abbrev E := EuclideanSpace ℂ (Fin 4 × Fin 3)

/-- The existing real Euclidean inner product is the restricted complex one. -/
theorem real_inner_eq_re_complex_inner (x y : E) :
    ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re := by
  simp only [PiLp.inner_apply, Complex.re_sum, Complex.inner, RCLike.inner_apply]

/-- Coordinate regrouping; the real scalar structure is unchanged. -/
def toBlocksLinearEquiv : E ≃ₗ[ℝ] BookHT.Blocks where
  toFun x i := WithLp.toLp 2 (fun a => x (i, a))
  invFun z := WithLp.toLp 2 (fun p => z p.1 p.2)
  left_inv x := by
    apply PiLp.ext
    intro p
    rfl
  right_inv z := by
    funext i
    apply PiLp.ext
    intro a
    rfl
  map_add' x y := by
    funext i
    apply PiLp.ext
    intro a
    rfl
  map_smul' r x := by
    funext i
    apply PiLp.ext
    intro a
    rfl

/-- The genuine continuous equivalence; finite dimension supplies continuity. -/
def toBlocks : E ≃L[ℝ] BookHT.Blocks :=
  toBlocksLinearEquiv.toContinuousLinearEquiv

@[simp] theorem toBlocks_apply (x : E) (i : Fin 4) (a : Fin 3) :
    toBlocks x i a = x (i, a) := rfl

@[simp] theorem toBlocks_symm_apply (z : BookHT.Blocks) (i : Fin 4) (a : Fin 3) :
    toBlocks.symm z (i, a) = z i a := rfl

/-- The real subspace supported on one three-coordinate block. -/
def W (i : Fin 4) : Submodule ℝ E where
  carrier := {x | ∀ j, j ≠ i → ∀ a, x (j, a) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy j hji a
    simp only [PiLp.add_apply, hx j hji a, hy j hji a, add_zero]
  smul_mem' := by
    intro r x hx j hji a
    simp only [PiLp.smul_apply, hx j hji a, smul_zero]

@[simp] theorem mem_W (i : Fin 4) (x : E) :
    x ∈ W i ↔ ∀ j, j ≠ i → ∀ a, x (j, a) = 0 := Iff.rfl

/-- Distinct supported blocks are orthogonal for the real inner product. -/
theorem pairwise_orthogonal : Pairwise (fun i j => (W i).IsOrtho (W j)) := by
  intro i j hij
  apply Submodule.isOrtho_iff_inner_eq.mpr
  intro x hx y hy
  change (∀ k, k ≠ i → ∀ a, x (k, a) = 0) at hx
  change (∀ k, k ≠ j → ∀ a, y (k, a) = 0) at hy
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hpi : p.1 = i
  · have hpj : p.1 ≠ j := by simpa only [hpi] using hij
    rw [hy p.1 hpj p.2]
    exact inner_zero_right _
  · rw [hx p.1 hpi p.2]
    exact inner_zero_left _

/-- The part of a vector on block i, used only for the spanning proof. -/
def blockPart (i : Fin 4) (x : E) : E :=
  WithLp.toLp 2 (fun p => if p.1 = i then x p else 0)

theorem blockPart_mem (i : Fin 4) (x : E) : blockPart i x ∈ W i := by
  intro j hji a
  simp [blockPart, hji]

theorem sum_blockPart (x : E) : (∑ i, blockPart i x) = x := by
  apply PiLp.ext
  intro p
  change (WithLp.ofLp (∑ i, blockPart i x)) p = x p
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp [blockPart, eq_comm]

/-- The four supported real subspaces span the whole Euclidean carrier. -/
theorem span_top : (⨆ i, W i) = ⊤ := by
  apply top_unique
  intro x hx
  rw [← sum_blockPart x]
  exact Submodule.sum_mem_iSup (fun i => blockPart_mem i x)

/-- Axis support is transported through the same continuous equivalence. -/
theorem mem_W_iff_onAxis (i : Fin 4) (x : E) :
    x ∈ W i ↔ FourBlock.OnAxis i (toBlocks x) := by
  constructor
  · intro hx j hji
    apply PiLp.ext
    intro a
    exact hx j hji a
  · intro hx j hji a
    simpa only [toBlocks_apply, PiLp.zero_apply] using
      congrArg (fun v : BookHT.Triple => v a) (hx j hji)

theorem symm_mem_W_iff_onAxis (i : Fin 4) (z : BookHT.Blocks) :
    toBlocks.symm z ∈ W i ↔ FourBlock.OnAxis i z := by
  simpa only [toBlocks.apply_symm_apply] using mem_W_iff_onAxis i (toBlocks.symm z)

theorem image_W (i : Fin 4) :
    toBlocks '' (W i : Set E) = {z | FourBlock.OnAxis i z} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_W_iff_onAxis i x).mp hx
  · intro hz
    exact ⟨toBlocks.symm z, (symm_mem_W_iff_onAxis i z).mpr hz,
      toBlocks.apply_symm_apply z⟩

theorem mem_blockUnion_iff (x : E) :
    x ∈ SupportedStress.blockUnion W ↔ ∃ i, FourBlock.OnAxis i (toBlocks x) := by
  simp only [SupportedStress.blockUnion, Set.mem_iUnion]
  exact exists_congr (fun i => mem_W_iff_onAxis i x)

theorem image_blockUnion :
    toBlocks '' SupportedStress.blockUnion W = {z | ∃ i, FourBlock.OnAxis i z} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_blockUnion_iff x).mp hx
  · intro hz
    change ∃ i, FourBlock.OnAxis i z at hz
    refine ⟨toBlocks.symm z, ?_, toBlocks.apply_symm_apply z⟩
    apply (mem_blockUnion_iff (toBlocks.symm z)).mpr
    simpa only [toBlocks.apply_symm_apply] using hz

/-- The accepted Book H/T common cone in the Euclidean block model. -/
theorem book_selected_zero_cone (x : E) :
    (BookHT.H (toBlocks x) = 0 ∧ BookHT.T (toBlocks x) = 0) ↔
      x ∈ SupportedStress.blockUnion W :=
  (BookHT.zero_cone (toBlocks x)).trans (mem_blockUnion_iff x).symm

end Option2.NativeStress.BookOrthogonal

#print axioms Option2.NativeStress.BookOrthogonal.real_inner_eq_re_complex_inner
#print axioms Option2.NativeStress.BookOrthogonal.toBlocks
#print axioms Option2.NativeStress.BookOrthogonal.pairwise_orthogonal
#print axioms Option2.NativeStress.BookOrthogonal.span_top
#print axioms Option2.NativeStress.BookOrthogonal.image_W
#print axioms Option2.NativeStress.BookOrthogonal.image_blockUnion
#print axioms Option2.NativeStress.BookOrthogonal.book_selected_zero_cone

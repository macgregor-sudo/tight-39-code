module

public import SliceGlue
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# CHAINMID prototype: the two slice hypotheses over a generic field, from matrix data

* `cutLinearSpace_nil_le_linearAnnihilator`: `hvanish` from `L·B = 0`
  (`∑_j equationLinearMatrix g (E e) j * B j t = 0`).
* `le_finrank_cutLinearSpace_nil_of_det`: `hdim` (`r ≤ finrank (cutLinearSpace g E [])`) from a
  nonzero `r × r` minor of the Jacobian `L` (rows `E ∘ rowSel`, columns `colSel`); for A6, `r = 973`.
  A nonzero determinant can be certified by an explicit right inverse (`det_ne_zero_of_right_inverse`).
-/

open MvPolynomial Module PolynomialJets SliceLemmas

namespace ChainMid

variable {K : Type*} [Field K] {n m : ℕ} {ι ε : Type*} [Fintype ι]

omit [Fintype ι] in
theorem cutLinearSpace_nil_eq (g : ι → MvPolynomial (Fin n) K) (E : ε → ι) :
    cutLinearSpace g E [] = Submodule.span K (Set.range fun e => homogeneousComponent 1 (g (E e))) := by
  simp [cutLinearSpace]

omit [Fintype ι] in
theorem coeffVector_homogeneousComponent_one' (f : MvPolynomial (Fin n) K) :
    coeffVector (homogeneousComponent 1 f) = fun j => f.coeff (Finsupp.single j 1) := by
  funext j
  simp [coeffVector, coeff_homogeneousComponent]

omit [Fintype ι] in
/-- `hvanish` from the matrix identity `L·B = 0`. -/
theorem cutLinearSpace_nil_le_linearAnnihilator (g : ι → MvPolynomial (Fin n) K) (E : ε → ι)
    (B : Matrix (Fin n) (Fin m) K)
    (hLB : ∀ e t, ∑ j, equationLinearMatrix g (E e) j * B j t = 0) :
    cutLinearSpace g E [] ≤ linearAnnihilator B := by
  rw [cutLinearSpace_nil_eq, Submodule.span_le]
  rintro _ ⟨e, rfl⟩
  refine (mem_linearAnnihilator_iff_vecMul _ _).2 ⟨homogeneousComponent_mem 1 _, ?_⟩
  rw [coeffVector_homogeneousComponent_one']
  funext t
  simpa [Matrix.vecMul, dotProduct, equationLinearMatrix] using hLB e t

/-- `hdim` from a nonzero `r × r` minor of the Jacobian. -/
theorem le_finrank_cutLinearSpace_nil_of_det (g : ι → MvPolynomial (Fin n) K) (E : ε → ι)
    {r : ℕ} (rowSel : Fin r → ε) (colSel : Fin r → Fin n)
    (hdet : Matrix.det (Matrix.of fun a b => equationLinearMatrix g (E (rowSel a)) (colSel b)) ≠ 0) :
    r ≤ finrank K (cutLinearSpace g E []) := by
  classical
  let ℓ : Fin r → MvPolynomial (Fin n) K := fun a => homogeneousComponent 1 (g (E (rowSel a)))
  let read : MvPolynomial (Fin n) K →ₗ[K] (Fin r → K) :=
    { toFun := fun f b => f.coeff (Finsupp.single (colSel b) 1)
      map_add' := fun f f' => by funext b; simp
      map_smul' := fun c f => by funext b; simp }
  have hrows := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hcomp : read ∘ ℓ = fun a => (Matrix.of fun a b =>
      equationLinearMatrix g (E (rowSel a)) (colSel b)) a := by
    funext a b
    simp [read, ℓ, coeff_homogeneousComponent, equationLinearMatrix]
  have hli : LinearIndependent K ℓ := LinearIndependent.of_comp read (hcomp ▸ hrows)
  have hle : Submodule.span K (Set.range ℓ) ≤ cutLinearSpace g E [] := by
    rw [cutLinearSpace_nil_eq]
    exact Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨rowSel a, rfl⟩)
  have hfin : FiniteDimensional K (cutLinearSpace g E []) := by
    rw [cutLinearSpace_nil_eq]
    -- the span of finitely many vectors indexed by the image of `E` (a subset of the finite `ι`)
    have hsub : Set.range (fun e => homogeneousComponent 1 (g (E e))) ⊆
        Set.range (fun i : ι => homogeneousComponent 1 (g i)) := by
      rintro _ ⟨e, rfl⟩; exact ⟨E e, rfl⟩
    have := FiniteDimensional.span_of_finite K
      (Set.finite_range fun i : ι => homogeneousComponent 1 (g i))
    exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)
  calc r = finrank K (Submodule.span K (Set.range ℓ)) := by
          rw [finrank_span_eq_card hli, Fintype.card_fin]
    _ ≤ finrank K (cutLinearSpace g E []) := Submodule.finrank_mono hle

end ChainMid

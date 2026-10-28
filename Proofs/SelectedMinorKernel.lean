module

public import RankBridge
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-! Pointwise normalized kernel coordinates from a selected nonsingular minor.
First-party proof using finite-dimensional linear algebra, with no finite arithmetic.
This does not construct a coefficient-ring or Laurent witness. -/

noncomputable section
namespace Option2.NativeStress.SelectedMinorKernel
open Matrix Module
open scoped BigOperators

theorem exists_normalized_kernel {K : Type*} [Field K] {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (rs : Fin r → Fin m) (cs : Fin r → Fin n)
    (hdet : (A.submatrix rs cs).det ≠ 0) (hrank : A.rank ≤ r) :
    ∃ (piv : Fin (n-r) → Fin n) (B : Matrix (Fin n) (Fin (n-r)) K),
      (∀ t, piv t ∉ Set.range cs) ∧
      Set.range piv = (Set.range cs)ᶜ ∧
      SliceLemmas.IsPivot B piv ∧
      (∀ i t, ∑ j, A i j * B j t = 0) ∧
      finrank K (LinearMap.ker A.mulVecLin) = n-r := by
  classical
  have hc : Function.Injective cs := by
    intro i j hij
    apply (Matrix.linearIndependent_cols_of_det_ne_zero hdet).injective
    funext k
    exact congrArg (A (rs k)) hij
  let F := {j : Fin n // j ∉ Set.range cs}
  have hcard : Fintype.card F = n-r := by
    change Fintype.card (↥(Set.range cs)ᶜ) = n-r
    rw [Fintype.card_compl_set]
    have hh := Fintype.card_congr (Equiv.ofInjective cs hc)
    simpa only [Fintype.card_fin] using congrArg (n - ·) hh.symm
  let eF : Fin (n-r) ≃ F := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let piv : Fin (n-r) → Fin n := fun t => (eF t).val
  have hp : ∀ t, piv t ∉ Set.range cs := fun t => (eF t).property
  have hcover : Set.range piv = (Set.range cs)ᶜ := by
    ext j
    constructor
    · rintro ⟨t, rfl⟩; exact hp t
    · intro hj
      exact ⟨eF.symm ⟨j, hj⟩, congrArg Subtype.val (eF.apply_symm_apply ⟨j,hj⟩)⟩
  let L : LinearMap.ker A.mulVecLin →ₗ[K] (Fin (n-r) → K) :=
    { toFun := fun x t => x.val (piv t)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hL : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have hfree : ∀ j, j ∉ Set.range cs → x.val j = 0 := by
      intro j hj
      have hj' : j ∈ Set.range piv := by rw [hcover]; exact hj
      obtain ⟨t, rfl⟩ := hj'
      exact congrFun hx t
    have hsum (i : Fin r) :
        ∑ k, A (rs i) (cs k) * x.val (cs k) = ∑ j, A (rs i) j * x.val j := by
      calc
        _ = ∑ j ∈ Finset.univ.image cs, A (rs i) j * x.val j :=
          (Finset.sum_image (f := fun j => A (rs i) j * x.val j)
            (s := Finset.univ) (g := cs) (fun a _ b _ h => hc h)).symm
        _ = _ := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j _ hj
          rw [hfree j (by simpa only [Finset.mem_image, Finset.mem_univ, true_and,
            Set.mem_range] using hj), mul_zero]
    have hxker : A.mulVec x.val = 0 := x.property
    have hs : (A.submatrix rs cs).mulVec (fun k => x.val (cs k)) = 0 := by
      funext i
      change (∑ k, A (rs i) (cs k) * x.val (cs k)) = 0
      rw [hsum]
      exact congrFun hxker (rs i)
    have hu : IsUnit (A.submatrix rs cs) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    have hz : (fun k => x.val (cs k)) = 0 :=
      Matrix.mulVec_injective_iff_isUnit.mpr hu (hs.trans (Matrix.mulVec_zero _).symm)
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ Set.range cs
    · obtain ⟨k, rfl⟩ := hj
      exact congrFun hz k
    · exact hfree j hj
  have hdimle : finrank K (LinearMap.ker A.mulVecLin) ≤ n-r := by
    simpa only [Module.finrank_fin_fun] using LinearMap.finrank_le_finrank_of_injective hL
  have hnull := A.mulVecLin.finrank_range_add_finrank_ker
  have hdim : finrank K (LinearMap.ker A.mulVecLin) = n-r := by
    change A.rank + finrank K (LinearMap.ker A.mulVecLin) = finrank K (Fin n → K) at hnull
    rw [Module.finrank_fin_fun] at hnull
    omega
  have hbij : Function.Bijective L := ⟨hL,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa only [Module.finrank_fin_fun] using hdim)).mp hL⟩
  let e := LinearEquiv.ofBijective L hbij
  let B : Matrix (Fin n) (Fin (n-r)) K :=
    fun j t => (e.symm (Pi.single t 1)).val j
  refine ⟨piv, B, hp, hcover, ?_, ?_, hdim⟩
  · intro t t'
    have h := congrFun (e.apply_symm_apply (Pi.single t' 1)) t
    simpa only [e, LinearEquiv.ofBijective_apply, L, LinearMap.coe_mk,
      AddHom.coe_mk, Pi.single_apply, eq_comm] using h
  · intro i t
    exact congrFun (e.symm (Pi.single t 1)).property i

end Option2.NativeStress.SelectedMinorKernel

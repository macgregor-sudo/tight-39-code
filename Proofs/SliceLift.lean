module

public import SliceKernel

@[expose] public section

/-!
# Lifting a spanning statement from the slice

(S5) Let `B` be a pivoted slice matrix and `W` a space of linear forms containing every linear
form that vanishes on the slice. If a subspace `R` of the forms of degree `e + 1` in `n`
variables contains `W · S_e` and restricts onto all forms of degree `e + 1` in `m` variables,
then `R` is all of `S_(e+1)`.

Proof: for `f ∈ S_(e+1)` pick `r ∈ R` with the same restriction; then `f - r` is a form of
degree `e + 1` vanishing on the slice, so it lies in `W · S_e ⊆ R` by (S2).
-/

open MvPolynomial

namespace SliceLemmas

variable {K : Type*} [Field K] {n m : ℕ}

/-- (S5) A subspace of `S_(e+1)` containing `W · S_e` whose restriction to the slice is all of
the degree-`(e+1)` forms in `m` variables is the whole of `S_(e+1)`. -/
theorem eq_homogeneousSubmodule_of_restrict_surjective {B : Matrix (Fin n) (Fin m) K}
    {piv : Fin m → Fin n} (hB : IsPivot B piv) {W : Submodule K (MvPolynomial (Fin n) K)}
    (hW : W ≤ homogeneousSubmodule (Fin n) K 1) (hann : linearAnnihilator B ≤ W) {e : ℕ}
    {R : Submodule K (MvPolynomial (Fin n) K)}
    (hR : R ≤ homogeneousSubmodule (Fin n) K (e + 1)) (hrel : sliceRelations W e ≤ R)
    (hsurj : homogeneousSubmodule (Fin m) K (e + 1) ≤ R.map (restrict B).toLinearMap) :
    R = homogeneousSubmodule (Fin n) K (e + 1) := by
  refine le_antisymm hR fun f hf => ?_
  obtain ⟨r, hr, hrf⟩ := hsurj (restrict_isHomogeneous B hf)
  have hrf' : restrict B r = restrict B f := hrf
  have hdiff : f - r ∈ sliceRelations W e :=
    mem_sliceRelations_of_restrict_eq_zero hB hW hann
      (Submodule.sub_mem _ hf (hR hr)) (by rw [map_sub, hrf', sub_self])
  have := R.add_mem (hrel hdiff) hr
  rwa [sub_add_cancel] at this

/-- (S5, spanning form) If the restrictions of the elements of `T ⊆ S_(e+1)` span all forms of
degree `e + 1` on the slice, then `W · S_e` together with `T` spans `S_(e+1)`. -/
theorem sliceRelations_sup_eq_homogeneousSubmodule {B : Matrix (Fin n) (Fin m) K}
    {piv : Fin m → Fin n} (hB : IsPivot B piv) {W : Submodule K (MvPolynomial (Fin n) K)}
    (hW : W ≤ homogeneousSubmodule (Fin n) K 1) (hann : linearAnnihilator B ≤ W) {e : ℕ}
    {T : Submodule K (MvPolynomial (Fin n) K)}
    (hT : T ≤ homogeneousSubmodule (Fin n) K (e + 1))
    (hsurj : homogeneousSubmodule (Fin m) K (e + 1) ≤ T.map (restrict B).toLinearMap) :
    sliceRelations W e ⊔ T = homogeneousSubmodule (Fin n) K (e + 1) :=
  eq_homogeneousSubmodule_of_restrict_surjective hB hW hann
    (sup_le (sliceRelations_le_homogeneousSubmodule hW e) hT) le_sup_left
    (hsurj.trans (Submodule.map_mono le_sup_right))

end SliceLemmas

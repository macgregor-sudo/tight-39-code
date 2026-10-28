/-
Adapted from https://github.com/Xmask19/mathlib4 at
230d75acb32d80e7d7c4f4cd028b139f3dc28be7,
Mathlib/AlgebraicTopology/InvarianceOfDomain.lean, Kai Lam (2026), Apache-2.0.
Copied scope: the retained invariance-of-domain implementation and dimension
corollaries described below. Existing namespace and compatibility changes are
retained; this candidate additionally uses module-system/public-import syntax.
Thank you to Kai Lam and the Lean/Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/
module

/-
Copyright (c) 2026 Kai Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Lam
-/

public import TopologyPreflight.ConditionalIoD

@[expose] public section

/-!
Invariance of domain and its finite-dimensional consequences under the stated
Brouwer fixed-point hypothesis.
Source: Xmask19/mathlib4@230d75acb32d80e7d7c4f4cd028b139f3dc28be7,
Mathlib/AlgebraicTopology/InvarianceOfDomain.lean.
Changes: remove the unfinished preceding proof; put retained declarations in
TopologyReuse; make the ambient type binder explicit. Local API/elaboration compatibility edits retain the theorem statements;
the source modification record is preserved in the provenance diffs.
The source's Apache-2.0 notice is retained; see LICENSES/Apache-2.0.txt.
-/

namespace TopologyReuse

open MeasureTheory Metric Set ContinuousLinearMap LinearMap Topology Polynomial

/-- If there is an injective map `f` from `ℝ^n` to `ℝ^m`, then `n ≤ m`. -/
theorem dim_le_of_injective_continuous
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [BrouwerFixedPoint E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E → F) (hf_cont : Continuous f) (hf_inj : Function.Injective f) :
    Module.finrank ℝ E ≤ Module.finrank ℝ F := by
  -- Suppose by contradiction that `m < n`.
  by_contra h
  rw [not_le] at h
  let n := (Module.finrank ℝ E)
  let m := (Module.finrank ℝ F)
  have hdimlt : m < n :=  Nat.lt_of_succ_le h
  -- Get bases and isomorphisms with Euclidean space.
  let basisE := stdOrthonormalBasis ℝ E
  let basisF := stdOrthonormalBasis ℝ F
  let coordE := basisE.repr
  let coordF := basisF.repr
  -- Takes a vector in `ℝ^m` to `ℝ^n` by filling the last entries with `0`,
  -- `(x₀, ..., x_m) → (x₀, ..., x_m, 0, ..., 0)`
  let pad : (Fin m → ℝ) → (Fin n → ℝ) := fun v i => if hi : i.val < m then v ⟨i.val, hi⟩ else 0
  let coordF_padded : F → (Fin n → ℝ) := fun x => pad (coordF x)
  let toEuclideanE : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm
  -- The inclusion map from `ℝ^m` to `ℝ^n`. It is continuous and injective.
  let incl : F → E := fun x =>
    coordE.symm (((EuclideanSpace.equiv (Fin n) ℝ).symm) (coordF_padded x))
  have hincl_cont : Continuous incl := by
    apply Continuous.comp' (LinearIsometryEquiv.continuous _)
    apply Continuous.comp' (ContinuousLinearEquiv.continuous _)
    exact continuous_pi fun i => by
      simp only [coordF_padded, pad, coordF]
      by_cases hi : i.val < m
      · simp only [dif_pos hi]; fun_prop
      · simp only [dif_neg hi]; exact continuous_const
  have hincl_inj : Function.Injective incl := by
    intro x y hxy
    apply coordF.injective
    ext i
    have hi : i.val < m := i.isLt
    have h : coordF_padded x = coordF_padded y := by
      have := congr_arg coordE hxy
      simp only [incl, LinearIsometryEquiv.apply_symm_apply,
        PiLp.continuousLinearEquiv_symm_apply, WithLp.toLp.injEq] at this
      exact this
    have := congr_fun h ⟨i.val, by grind⟩
    simp only [coordF_padded, pad, hi, dif_pos] at this
    exact this
  -- The inclusion map composed with `f` gives `g`, a continuous and injective map
  -- from `ℝ^n` to `ℝ^n`.
  let g : E → E := incl ∘ f
  have hg_cont : Continuous g := hincl_cont.comp hf_cont
  have hg_inj : Function.Injective g := hincl_inj.comp hf_inj
  -- `ℝ^n` is open
  -- By invariance of domain, `g` is an open mapping and so `g(ℝ^n)` is open.
  have hg_img_open : IsOpen (g '' Set.univ) := invariance_of_domain_open_map g Set.univ isOpen_univ
    hg_cont.continuousOn hg_inj.injOn
  -- Use definition of openness with balls.
  rw [Metric.isOpen_iff] at hg_img_open
  -- the `mth` coordinate of every point in the image is `0`.
  have hlastzero : ∀ x ∈ g '' Set.univ, (EuclideanSpace.equiv (Fin n) ℝ) (coordE x) ⟨m, h⟩ = 0 := by
    intro x ⟨y, _, hy⟩
    rw [← hy]
    simp [PiLp.continuousLinearEquiv_symm_apply, Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply, PiLp.continuousLinearEquiv_apply, lt_self_iff_false,
      ↓reduceDIte, coordE, g, incl, coordF_padded, pad]
  -- Consider some point `x` in the image of `g`.
  -- As the `mth` coordinate of every point of the image is `0`,
  have : (g '' Set.univ).Nonempty := Set.Nonempty.of_subtype
  let x : E := this.some
  have hx := Set.Nonempty.some_mem this
  -- There is a ball around it contained in `g(ℝ^n)`.
  rcases hg_img_open x hx with ⟨ε, hε, hball⟩
  -- `c` picks out the `mth` coordinate.
  let c : E → ℝ := fun y => (EuclideanSpace.equiv (Fin n) ℝ) (coordE y) ⟨m, h⟩
  -- The `mth` coordinate is `0` for every point in the ball around `x`.
  have hc_zero : ∀ y ∈ ball x ε, c y = 0 := fun y hy => (fun y hy => hlastzero y (hball hy)) y hy
  -- Take `x` and add `ε/2` in the `mth` coordinate to get a point `x'`.
  let x' : E := x + coordE.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm
    (fun i => if i = ⟨m, h⟩ then ε / 2 else 0))
  -- `x'` is in the `ε-ball` around `x`.
  have hx'_in_ball : x' ∈ ball x ε := by
    simp only [x', mem_ball, dist_eq_norm, add_sub_cancel_left]
    have hconv : (EuclideanSpace.equiv (Fin n) ℝ).symm
        (fun i => if i = ⟨m, h⟩ then ε / 2 else 0) =
        EuclideanSpace.single ⟨m, h⟩ (ε / 2) := by
      ext i
      simp only [EuclideanSpace.single, EuclideanSpace.equiv,
        PiLp.continuousLinearEquiv_symm_apply]
      split_ifs with hi
      · rw [hi] ; simp
      · simp [hi]
    rw [LinearIsometryEquiv.norm_map, hconv, EuclideanSpace.norm_single,
      Real.norm_of_nonneg (by linarith)]
    linarith [half_lt_self hε]
  -- The `mth` coordinate of `x'` is non-zero, (as it is `ε/2`).
  have hx'_nonzero : c x' ≠ 0 := by
    have hsum : ((EuclideanSpace.equiv (Fin n) ℝ) (coordE x) + (EuclideanSpace.equiv (Fin n) ℝ)
      (coordE (coordE.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm
      fun i => if i = ⟨m, h⟩ then ε / 2 else 0)))) ⟨m, h⟩ =
      (EuclideanSpace.equiv (Fin n) ℝ) (coordE x) ⟨m, h⟩ + ε / 2 := by simp [Pi.add_apply]
    have hcx : c x = 0 := hlastzero x hx
    unfold c at hcx
    have hsum2 : (EuclideanSpace.equiv (Fin n) ℝ) (coordE x) ⟨m, h⟩ + ε / 2 = ε / 2 := by
      rw [hcx]
      ring
    simp only [x', c, map_add, hsum, hsum2]
    linarith [half_pos hε]
  -- This contradicts all points in the ball having `mth` coordinate `0`.
  exact hx'_nonzero (hc_zero x' hx'_in_ball)

-- If there is a homeomorphism between `ℝ^m` and `ℝ^n`, then `m = n`
theorem invariance_of_dimension
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BrouwerFixedPoint E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [BrouwerFixedPoint F]
    (φ : E ≃ₜ F) :
    Module.finrank ℝ E = Module.finrank ℝ F := by
  -- From the homeomorphism, get continuous and injective functions both ways and apply the above.
  let f : E → F := φ
  let g : F → E := φ.symm
  exact Nat.le_antisymm (dim_le_of_injective_continuous f (φ.continuous) (φ.injective))
    (dim_le_of_injective_continuous g (φ.symm.continuous) (φ.symm.injective))

end TopologyReuse

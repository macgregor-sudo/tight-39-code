/-
Copyright (c) 2026 harfe. Licensed under MIT; see LICENSES/harfe-MIT.txt.
Source: https://github.com/harfe/fixed-point-theorems-lean4
Revision: 770940ddf9878cf61952ed53d910b92bca841838
Original file: FixedPointTheorems/brouwer.lean; copied scope: complete file.
Compatibility ancestry: https://github.com/openai/math at
1581d4cbdd69a0faf34b2089614fe2a814316a6a,
lean/patches/fixed-point-theorems-lean4341.patch (Apache-2.0).
Modifications: the existing Lean 4.35 compatibility port is retained;
this candidate additionally uses module-system/public-import syntax.
Thank you to harfe and the Lean, Mathlib, and OpenAI math contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/
module

public import Mathlib.Dynamics.FixedPoints.Basic
public import FixedPointTheorems.apply_cubical_sperner
public import FixedPointTheorems.convex_homeos

@[expose] public section

/-!
# Brouwer's fixed-point theorem

The unit-cube fixed-point theorem is transported along a homeomorphism of a
nonempty compact convex set. The resulting theorem is also expressed using
`Function.IsFixedPt` and the set of fixed points.
-/


theorem brouwer_fixed_point {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    : ∀ (s : Set V), Convex ℝ s → IsCompact s → Set.Nonempty s →
    ∀ (f : C(s, s)), ∃ x, f x = x := by {
  intro s hcvx hcmpct hne f
  obtain ⟨k, ⟨e⟩ ⟩ := homeo_unit_cube_of_convex_compact s hcvx hcmpct hne
  let g := (toContinuousMap e).comp (f.comp (toContinuousMap e.symm))
  obtain ⟨y, hy⟩ := @fixed_point_unit_cube k g
  use (toContinuousMap e.symm) y
  have h1 : e.symm (e (f (e.symm y))) = e.symm y := congrArg e.symm hy
  rwa [e.symm_apply_apply] at h1
}

theorem brouwer_fixed_point_isFixedPt {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : Set.Nonempty s)
    (f : C(s, s)) :
    ∃ x, Function.IsFixedPt f x := by
  simpa [Function.IsFixedPt] using! brouwer_fixed_point s hcvx hcmpct hne f

theorem brouwer_fixedPoints_nonempty {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : Set.Nonempty s)
    (f : C(s, s)) :
    (Function.fixedPoints f).Nonempty := by
  exact brouwer_fixed_point_isFixedPt s hcvx hcmpct hne f

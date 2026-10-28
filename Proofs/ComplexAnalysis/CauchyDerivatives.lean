/-
Isolated pinned-toolchain port of https://github.com/bjbraams/lean-SCV
Revision: 50392764ae64d75779abbea1396fe93d80b677cc
Original file: ComplexAnalysis/CauchyDerivatives.lean; copied scope: the complete original file.
Original author/copyright holder: Bastiaan J Braams (retained header below).
License: Apache-2.0; unchanged upstream license retained at LICENSES/SCV-Apache-2.0.txt.
Changes: pinned-toolchain compatibility port, public module/import adaptation and attribution comments; see THIRD_PARTY_NOTICES.md#scv-complex-analysis for the public modification record.
Thank you to the lean-SCV author and Lean/Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/
/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Cauchy's derivative formula at an arbitrary point of a disk

Mathlib's higher-derivative circle formula is stated at the center. Here the evaluation point
may be anywhere in the open disk. The derivative of the contour kernel in the evaluation point
is Mathlib's `Complex.hasDerivAt_circleIntegral_sub_zpow_smul`, which needs only circle
integrability of the function; induction on the order then gives the formula without boundary
derivatives of the function.

These Banach-valued, one-variable results also support iterated Cauchy formulas in several
variables. The circle center and evaluation point are independent, and the derivative order is
arbitrary. The statements use Mathlib's `HasDerivAt`, `iteratedDeriv`, `DiffContOnCl`, and
circle-integral interfaces rather than introducing a separate contour or derivative theory.
Their intended Mathlib home is `Analysis.Complex.CauchyIntegral`.

## Main results

* `DiffContOnCl.iteratedDeriv_eq_circleIntegral_sub_zpow_smul`: Cauchy's formula for every
  derivative at any point inside the circle.
* `DiffContOnCl.iteratedDeriv_eq_circleIntegral_sub_zpow_mul`: the scalar form.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

open Complex MeasureTheory Metric Filter Set
open scoped Topology

public noncomputable section

section Banach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Cauchy's formula for every derivative at any point inside the circle. The function need only be
holomorphic in the open disk and continuous on its closure.

The corresponding integral formula appears in Mathlib PR #43100 by `JJYYY-JJY`, with coauthor
`ajirving`. See `THIRD_PARTY_NOTICES.md#scv-complex-analysis`, which locates lean-CA's historical credit record and distinguishes related formulas from copied proofs. -/
theorem DiffContOnCl.iteratedDeriv_eq_circleIntegral_sub_zpow_smul
    {c : ℂ} {R : ℝ} {f : ℂ → E} (hf : DiffContOnCl ℂ f (ball c R))
    (hR : 0 < R) (n : ℕ) {w : ℂ} (hw : w ∈ ball c R) :
    iteratedDeriv n f w = ((n.factorial : ℂ) * (2 * (Real.pi : ℂ) * I)⁻¹) •
      ∮ s in C(c, R), (s - w) ^ (-(n + 1 : ℤ)) • f s := by
  induction n generalizing w with
  | zero =>
    simpa using
      (hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw).symm
  | succ n ih =>
    have heq : (iteratedDeriv n f) =ᶠ[nhds w]
        (fun w ↦ ((n.factorial : ℂ) * (2 * (Real.pi : ℂ) * I)⁻¹) •
          ∮ s in C(c, R), (s - w) ^ (-(n + 1 : ℤ)) • f s) := by
      filter_upwards [isOpen_ball.mem_nhds hw] with v hv
      exact ih hv
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hint : CircleIntegrable f c R :=
      (hf.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable hR.le
    have hw' : w ∉ sphere c |R| := by
      rw [abs_of_pos hR]
      exact fun h ↦ (mem_ball.mp hw).ne (mem_sphere.mp h)
    have hd := ((Complex.hasDerivAt_circleIntegral_sub_zpow_smul (n := -(n + 1 : ℤ)) hint
      hw').const_smul ((n.factorial : ℂ) * (2 * (Real.pi : ℂ) * I)⁻¹)).deriv
    refine hd.trans ?_
    have hexp : (-(n + 1 : ℤ) - 1) = -((n + 1 : ℕ) + 1 : ℤ) := by push_cast; ring
    rw [hexp]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, smul_smul]
    congr 1
    push_cast
    ring

end Banach

/-- Cauchy's formula for every derivative at any point inside the circle. The function need only be
holomorphic in the open disk and continuous on its closure.

The corresponding integral formula appears in Mathlib PR #43100 by `JJYYY-JJY`, with coauthor
`ajirving`. See `THIRD_PARTY_NOTICES.md#scv-complex-analysis`, which locates lean-CA's historical credit record and distinguishes related formulas from copied proofs. -/
theorem DiffContOnCl.iteratedDeriv_eq_circleIntegral_sub_zpow_mul
    {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f (ball c R))
    (hR : 0 < R) (n : ℕ) {w : ℂ} (hw : w ∈ ball c R) :
    iteratedDeriv n f w = (n.factorial : ℂ) * (2 * (Real.pi : ℂ) * I)⁻¹ *
      ∮ s in C(c, R), (s - w) ^ (-(n + 1 : ℤ)) * f s := by
  simpa only [smul_eq_mul] using hf.iteratedDeriv_eq_circleIntegral_sub_zpow_smul hR n hw

end

/-
Isolated pinned-toolchain port of https://github.com/bjbraams/lean-SCV
Revision: 50392764ae64d75779abbea1396fe93d80b677cc
Original file: SeveralComplexVariables/Analyticity.lean; copied scope: the complete original file.
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

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import SeveralComplexVariables.Osgood

/-!
# Analyticity of holomorphic maps in finite dimension

This file proves the several-complex-variables theorem that a complex Fréchet-differentiable map on
an open subset of a finite-dimensional complex normed space is analytic. The general theorem uses
coordinates only inside its proof. The file is a temporary project home for material ultimately
intended for a Mathlib location such as `Mathlib.Analysis.Complex.SeveralVariables.Analyticity`. It
builds on the polydisc Cauchy-series and Osgood theorems; the underlying predicates are Mathlib
definitions.

## Main results

`DifferentiableOn.analyticOnNhd_of_finiteDimensional` and
`differentiableOn_iff_analyticOnNhd_of_finiteDimensional` give the coordinate-free interface for
arbitrary finite-dimensional complex normed domains and complete complex normed codomains.

`DifferentiableOn.analyticOnNhd_pi` and `differentiableOn_iff_analyticOnNhd_pi` give the
corresponding interface for finite coordinate spaces `ι → ℂ`. Such spaces are natural for
separate holomorphy, coordinate derivatives, and polydisc expansions. The coordinate theorem is
proved first and then transported along a linear equivalence; this proof order imposes no choice
of coordinates on the general statements.

## References

* V. Scheidemann, *Introduction to Complex Analysis in Several Variables*,
  Birkhäuser, 2005 (background on holomorphic functions of several variables).
-/

public section

open Set

section Coordinates

variable {ι F : Type*} [Fintype ι]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A complex Fréchet-differentiable map on an open subset of a finite complex coordinate space is
analytic there. -/
theorem DifferentiableOn.analyticOnNhd_pi {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) : AnalyticOnNhd ℂ f U := by
  classical
  apply SeveralComplexVariables.analyticOnNhd_pi_of_analyticOnNhd_update hU hf.continuousOn
  intro z hz i
  let V : Set ℂ := {w | Function.update z i w ∈ U}
  have hupdate : Continuous (fun w : ℂ ↦ Function.update z i w) := by fun_prop
  have hupdate_diff : Differentiable ℂ (fun w : ℂ ↦ Function.update z i w) :=
    fun w => (hasDerivAt_update z i w).differentiableAt
  have hV : IsOpen V := hU.preimage hupdate
  have hd : DifferentiableOn ℂ (fun w ↦ f (Function.update z i w)) V := by
    intro w hw
    exact (((hf _ hw).differentiableAt (hU.mem_nhds hw)).comp w
      hupdate_diff.differentiableAt).differentiableWithinAt
  exact hd.analyticAt (hV.mem_nhds (by simpa [V] using hz))

/-- On an open subset of a finite complex coordinate space, complex Fréchet differentiability and
analyticity are equivalent. -/
theorem differentiableOn_iff_analyticOnNhd_pi {U : Set (ι → ℂ)} {f : (ι → ℂ) → F}
    (hU : IsOpen U) : DifferentiableOn ℂ f U ↔ AnalyticOnNhd ℂ f U :=
  ⟨fun hf ↦ hf.analyticOnNhd_pi hU, fun hf ↦ hf.differentiableOn⟩

end Coordinates

section FiniteDimensional

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Complex differentiability on an open finite-dimensional domain implies analyticity. No choice of
coordinates occurs in the statement. -/
theorem DifferentiableOn.analyticOnNhd_of_finiteDimensional {U : Set E} {f : E → F}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) : AnalyticOnNhd ℂ f U := by
  let e := (Module.finBasis ℂ E).equivFunL
  have hg : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' U) :=
    hf.comp e.symm.differentiable.differentiableOn (fun _ hx => hx)
  have ha := hg.analyticOnNhd_pi (hU.preimage e.symm.continuous)
  intro x hx
  have hmem : e x ∈ e.symm ⁻¹' U := by simpa using hx
  simpa [Function.comp_def] using
    (ha (e x) hmem).comp_of_eq (e.toContinuousLinearMap.analyticAt x) rfl

/-- On an open finite-dimensional domain, holomorphy may be expressed using either complex Fréchet
differentiability or Mathlib's analytic predicate. -/
theorem differentiableOn_iff_analyticOnNhd_of_finiteDimensional {U : Set E} {f : E → F}
    (hU : IsOpen U) : DifferentiableOn ℂ f U ↔ AnalyticOnNhd ℂ f U :=
  ⟨fun hf => hf.analyticOnNhd_of_finiteDimensional hU, fun hf => hf.differentiableOn⟩

/-- An everywhere complex-differentiable map on a finite-dimensional space is entire. -/
theorem Differentiable.analyticOnNhd_of_finiteDimensional {f : E → F}
    (hf : Differentiable ℂ f) : AnalyticOnNhd ℂ f Set.univ :=
  hf.differentiableOn.analyticOnNhd_of_finiteDimensional isOpen_univ

end FiniteDimensional

end

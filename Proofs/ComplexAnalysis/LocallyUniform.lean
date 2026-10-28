/-
Isolated pinned-toolchain port of https://github.com/bjbraams/lean-SCV
Revision: 50392764ae64d75779abbea1396fe93d80b677cc
Original file: ComplexAnalysis/LocallyUniform.lean; copied scope: the complete original file.
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

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Iterated derivatives of locally uniform limits in one complex variable

If holomorphic functions on an open subset of the complex plane, with values in a complex
Banach space, converge locally uniformly along a filter, then so do their iterated derivatives
of every order, to the iterated derivatives of the limit. This iterates Mathlib's
`TendstoLocallyUniformlyOn.deriv`. The pointwise statement for sequences of scalar functions is
recorded as a corollary.

## Main results

* `TendstoLocallyUniformlyOn.iteratedDeriv`: Iterated derivatives converge locally uniformly.
* `Complex.tendsto_iteratedDeriv_of_tendstoLocallyUniformlyOn`: Iterated derivatives converge
  along a locally uniform limit of holomorphic one-variable functions, evaluated at any point of
  the domain.

## References

* J. B. Conway, *Functions of One Complex Variable I*, second edition, Springer, 1978
  (background on one-variable holomorphic functions).
-/

public noncomputable section

open Filter Set
open scoped Topology

namespace Complex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Iterated derivatives of locally uniform limits.** If holomorphic functions `F n` with
values in a complex Banach space converge locally uniformly on an open set `U` along a filter,
then so do their iterated derivatives of every order. -/
theorem _root_.TendstoLocallyUniformlyOn.iteratedDeriv {φ : Filter ι} {U : Set ℂ} (hU : IsOpen U)
    (j : ℕ) : ∀ {F : ι → ℂ → E} {f : ℂ → E}, TendstoLocallyUniformlyOn F f φ U →
      (∀ᶠ n in φ, DifferentiableOn ℂ (F n) U) →
      TendstoLocallyUniformlyOn (iteratedDeriv j ∘ F) (iteratedDeriv j f) φ U := by
  induction j with
  | zero =>
    intro F f hF _
    simpa [iteratedDeriv_zero, Function.comp_def] using hF
  | succ j ih =>
    intro F f hF hFd
    have hderiv : TendstoLocallyUniformlyOn (deriv ∘ F) (deriv f) φ U := hF.deriv hFd hU
    have hderivDiff : ∀ᶠ n in φ, DifferentiableOn ℂ ((deriv ∘ F) n) U :=
      hFd.mono fun n hn ↦ (hn.analyticOnNhd hU).deriv.differentiableOn
    simpa [iteratedDeriv_succ', Function.comp_def] using ih hderiv hderivDiff

/-- Iterated derivatives converge along a locally uniform limit of holomorphic one-variable
functions, evaluated at any point of the domain. This is the pointwise form of
`TendstoLocallyUniformlyOn.iteratedDeriv` for sequences of scalar functions. -/
theorem tendsto_iteratedDeriv_of_tendstoLocallyUniformlyOn {V : Set ℂ} (hV : IsOpen V) (j : ℕ) :
    ∀ (F : ℕ → ℂ → ℂ) (f' : ℂ → ℂ), TendstoLocallyUniformlyOn F f' atTop V →
      (∀ n, DifferentiableOn ℂ (F n) V) → ∀ {x : ℂ}, x ∈ V →
      Tendsto (fun n ↦ iteratedDeriv j (F n) x) atTop (𝓝 (iteratedDeriv j f' x)) :=
  fun _ _ hF hFa _ hx ↦
    (hF.iteratedDeriv hV j (Eventually.of_forall hFa)).tendsto_at hx

end Complex

end

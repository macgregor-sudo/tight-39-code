/-
Isolated pinned-toolchain port of https://github.com/bjbraams/lean-SCV
Revision: 50392764ae64d75779abbea1396fe93d80b677cc
Original file: ToMathlib/Analysis/Integral/CompactSupport.lean; copied scope: the complete original file.
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

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integration helpers for compactly supported and weighted functions

An integrable scalar weight can be multiplied by a continuous normed-space-valued function on a
compact set without losing integrability. A second result gives integrability on a half-line for
continuous functions that vanish beyond a finite radius.

## Main results

* `MeasureTheory.IntegrableOn.smul_continuousOn_of_isCompact`: An integrable scalar weight times
  a continuous normed-space-valued function on a compact set is integrable. Compactness gives
  both boundedness and a separable image, so no countability assumption on either ambient space
  is required.
* `MeasureTheory.integrableOn_Ioi_of_continuousOn_of_eq_zero`: A function continuous on
  `[a, R]` and vanishing beyond `R` is integrable on `(a, ∞)`.
-/

public noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Topology

variable {𝕜 α E : Type*} [NormedRing 𝕜] [MeasurableSpace α]
  [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- An integrable scalar weight times a continuous normed-space-valued function on a compact set is
integrable. Compactness gives both boundedness and a separable image, so no countability
assumption on either ambient space is required. -/
theorem MeasureTheory.IntegrableOn.smul_continuousOn_of_isCompact
    [TopologicalSpace α] [BorelSpace α] [T2Space α]
    {μ : Measure α} {K : Set α} {g : α → 𝕜} {H : α → E}
    (hg : IntegrableOn g K μ) (hH : ContinuousOn H K) (hK : IsCompact K) :
    IntegrableOn (fun t ↦ g t • H t) K μ := by
  obtain ⟨M, hM⟩ := hK.bddAbove_image hH.norm
  apply (hg.norm.mul_const M).mono'
    (hg.aestronglyMeasurable.smul (hH.aestronglyMeasurable_of_isCompact hK hK.measurableSet))
  filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
  change ‖g t • H t‖ ≤ ‖g t‖ * M
  exact (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hM ⟨t, ht, rfl⟩) (norm_nonneg _))

end

public section

open MeasureTheory Set

namespace MeasureTheory

variable {F : Type*} [NormedAddCommGroup F]

/-- A function continuous on `[a, R]` and vanishing beyond `R` is integrable on `(a, ∞)`.
No continuity is needed beyond `R`, and `R < a` is allowed. -/
theorem integrableOn_Ioi_of_continuousOn_of_eq_zero {g : ℝ → F} {a R : ℝ}
    (hg : ContinuousOn g (Icc a R)) (hz : ∀ r, R < r → g r = 0) : IntegrableOn g (Ioi a) := by
  have h1 : IntegrableOn g (Icc a R) := hg.integrableOn_Icc
  have h2 : IntegrableOn g (Ioi R) :=
    ((integrable_zero _ _ _).integrableOn).congr_fun (fun r hr ↦ (hz r hr).symm) measurableSet_Ioi
  refine (h1.union h2).mono_set fun r hr ↦ ?_
  rcases le_or_gt r R with h | h
  · exact Or.inl ⟨le_of_lt hr, h⟩
  · exact Or.inr h

end MeasureTheory

end

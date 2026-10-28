module

public import NativeTrialityReuseAlgebraLaws
public import NativeTrialityReuseCubicJordan

/-!
# The native Newton cubic identity and the Jordan identity

`cubicResidual_eq_zero`: the native compact product satisfies the Newton cubic identity
`6 x³ - 6 tr(x) x² + (3 tr(x)² - 3 tr(x²)) x - (tr(x)³ - 3 tr(x) tr(x²) + 2 tr(x³)) 1 = 0`,
checked in all 27 native coordinates. With commutativity, the unit and trace associativity, the
generic implication `CubicJordan.jordan_of_cubic_trace_identity` gives the Jordan identity.
The closure's `Glennie.jordanLinear` and `Glennie.traceLinear` are used (not redefined).
-/

/-
Provenance (ported block: `cubicResidual_eq_zero`, `jordan_identity`).
Repository: https://github.com/macgregor-sudo/compact-albert-recognition
Commit: 40d3b344180d9ddb78aaa2876873377c1e631515
File: Glennie/Native/CubicIdentity.lean, lines 30–59 (lines 14–28, `jordanLinear`, `traceLinear` and their
`_apply` lemmas, are already in the closure, textually identical, and are reused from there).
Author: the upstream file header carries no author line; THIRD-PARTY-NOTICES.md of that commit states
that Robert MacGregor directs the AI-generated development and is the maintainer.
SPDX-License-Identifier: Apache-2.0
Modification: declarations moved from namespace `Glennie` to `CKM.NativeDerivationTriality.Reuse` (with `open Glennie`);
`CubicJordan.*` and `inner_jordan_associative` now resolve to their `CKM.NativeDerivationTriality.Reuse` ports; bodies unchanged.

Second-hand copy: this file is identical to the earlier source port `RealOrbitSlice/Reuse/CubicIdentity.lean`
(sha256 366cdb933161ae389e9b15890581fa7ac0d3f2edb2f45d109a7fddce33625ca9, package claude-real-orbit-slice-2026-10-24) except that the
namespace `RealOrbitSlice.Reuse` is renamed `CKM.NativeDerivationTriality.Reuse` and module names are flattened.
-/

@[expose] public section

namespace CKM.NativeDerivationTriality.Reuse

noncomputable section

open Glennie

set_option linter.unusedSimpArgs false

set_option maxHeartbeats 8000000 in
/-- The Newton residual is proved in all 27 native compact coordinates. -/
theorem cubicResidual_eq_zero (x : Albert) :
    CubicJordan.residual jordanLinear traceLinear (1 : Albert) x = 0 := by
  change (6 : ℝ) • jordan x (jordan x x) - (6 * trace x) • jordan x x +
    (3 * (trace x) ^ 2 - 3 * trace (jordan x x)) • x -
    ((trace x) ^ 3 - 3 * trace x * trace (jordan x x) +
      2 * trace (jordan x (jordan x x))) • (1 : Albert) = 0
  ext
  all_goals simp [jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02,
    jordan_o12, trace, octDot_coordinates, octNormSq, Quaternion.normSq_def',
    octMul, octConj, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, smul_eq_mul]
  all_goals ring

set_option maxHeartbeats 2000000 in
/-- The native compact Hermitian product satisfies the Jordan identity. -/
theorem jordan_identity (x y : Albert) :
    jordan (jordan x y) (jordan x x) = jordan x (jordan y (jordan x x)) := by
  have hc : ∀ a b, jordanLinear a b = jordanLinear b a := fun a b => by
    simpa only [jordanLinear_apply] using jordan_comm a b
  have hu : ∀ a, jordanLinear 1 a = a := fun a => by
    simpa only [jordanLinear_apply] using jordan_unit_left a
  have ht : ∀ a b c, traceLinear (jordanLinear (jordanLinear a b) c) =
      traceLinear (jordanLinear a (jordanLinear b c)) := fun a b c => by
    simp only [jordanLinear_apply, traceLinear_apply]
    exact inner_jordan_associative a b c
  have h := CubicJordan.jordan_of_cubic_trace_identity jordanLinear traceLinear 1
    hc hu ht cubicResidual_eq_zero x y
  simpa only [jordanLinear_apply] using h

end

end CKM.NativeDerivationTriality.Reuse

#print axioms CKM.NativeDerivationTriality.Reuse.cubicResidual_eq_zero
#print axioms CKM.NativeDerivationTriality.Reuse.jordan_identity

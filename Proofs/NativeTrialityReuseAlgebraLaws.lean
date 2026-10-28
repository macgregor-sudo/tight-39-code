module

public import NativePolynomialEvaluationStaged

/-!
# Bilinearity of the native trace form and trace associativity

The native Jordan product `Glennie.jordan` already has its additivity, homogeneity and unit laws in
the closure (`NativePolynomialEvaluationStaged`). This file adds negation, subtraction and zero laws,
the bilinearity of the native trace form `Glennie.inner x y = trace (x ∘ y)`, and trace associativity
`⟪x ∘ y, z⟫ = ⟪x, y ∘ z⟫`, proved in the 27 native coordinates.
-/

/-
Provenance (ported block: all declarations of this file).
Repository: https://github.com/macgregor-sudo/compact-albert-recognition
Commit: 40d3b344180d9ddb78aaa2876873377c1e631515
File: Glennie/Native/AlgebraLaws.lean, lines 119–130 and 141–180 (lines 79–118 and 131–139 are already in
the closure, textually identical, and are reused from there).
Author: the upstream file header carries no author line; THIRD-PARTY-NOTICES.md of that commit states
that Robert MacGregor directs the AI-generated development and is the maintainer.
SPDX-License-Identifier: Apache-2.0
Modification: declarations moved from namespace `Glennie` to `CKM.NativeDerivationTriality.Reuse` (with `open Glennie`),
laws already present in the closure omitted; bodies unchanged.

Second-hand copy: this file is identical to the earlier source port `RealOrbitSlice/Reuse/AlgebraLaws.lean`
(sha256 0f58e39c850d1148b46e9327358fa5a0d787822a39da3761f900c6ccda246fb5, package claude-real-orbit-slice-2026-10-24) except that the
namespace `RealOrbitSlice.Reuse` is renamed `CKM.NativeDerivationTriality.Reuse` and module names are flattened.
-/

@[expose] public section

namespace CKM.NativeDerivationTriality.Reuse

noncomputable section

open Glennie

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

@[simp] theorem jordan_neg_left (x y : Albert) : jordan (-x) y = -jordan x y := by
  simpa using jordan_smul_left (-1 : ℝ) x y

@[simp] theorem jordan_neg_right (x y : Albert) : jordan x (-y) = -jordan x y := by
  simpa using jordan_smul_right (-1 : ℝ) x y

theorem jordan_sub_left (x y z : Albert) : jordan (x-y) z = jordan x z-jordan y z := by
  simp [sub_eq_add_neg, jordan_add_left]

theorem jordan_sub_right (x y z : Albert) : jordan x (y-z) = jordan x y-jordan x z := by
  simp [sub_eq_add_neg, jordan_add_right]

@[simp] theorem jordan_zero_left (x : Albert) : jordan 0 x = 0 := by
  simpa using jordan_smul_left (0 : ℝ) x x

@[simp] theorem jordan_zero_right (x : Albert) : jordan x 0 = 0 := by
  rw [jordan_comm, jordan_zero_left]

theorem inner_add_left (x y z : Albert) : inner (x+y) z = inner x z+inner y z := by
  simp [inner_coordinates, octDot_coordinates]
  ring

theorem inner_add_right (x y z : Albert) : inner x (y+z) = inner x y+inner x z := by
  rw [inner_comm, inner_add_left, inner_comm x y, inner_comm x z]

theorem inner_smul_left (r : ℝ) (x y : Albert) : inner (r • x) y = r * inner x y := by
  simp [inner_coordinates, octDot_coordinates, smul_eq_mul]
  ring

theorem inner_smul_right (r : ℝ) (x y : Albert) : inner x (r • y) = r * inner x y := by
  rw [inner_comm, inner_smul_left, inner_comm x y]

@[simp] theorem inner_neg_left (x y : Albert) : inner (-x) y = -inner x y := by
  simpa using inner_smul_left (-1 : ℝ) x y

@[simp] theorem inner_neg_right (x y : Albert) : inner x (-y) = -inner x y := by
  simpa using inner_smul_right (-1 : ℝ) x y

theorem inner_sub_left (x y z : Albert) : inner (x-y) z = inner x z-inner y z := by
  simp [sub_eq_add_neg, inner_add_left]

theorem inner_sub_right (x y z : Albert) : inner x (y-z) = inner x y-inner x z := by
  simp [sub_eq_add_neg, inner_add_right]

set_option maxHeartbeats 2000000 in
theorem inner_jordan_associative (x y z : Albert) :
    inner (jordan x y) z = inner x (jordan y z) := by
  simp [inner_coordinates, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot_coordinates,
    octMul, octConj, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul, smul_eq_mul]
  ring

end

end CKM.NativeDerivationTriality.Reuse

#print axioms CKM.NativeDerivationTriality.Reuse.jordan_sub_left
#print axioms CKM.NativeDerivationTriality.Reuse.jordan_zero_left
#print axioms CKM.NativeDerivationTriality.Reuse.inner_sub_right
#print axioms CKM.NativeDerivationTriality.Reuse.inner_jordan_associative

module

public import NativePolynomialEvaluationStaged

/-!
# Octonion laws of the native compact Cayley–Dickson octonions

Norm multiplicativity, the conjugate inverse, the left and right alternative laws, the Moufang law
and associativity of the real part, for `Glennie.octMul` exactly as used by the accepted native
closure (`NativeIncludedQuartetReadouts`). Every law is proved by expanding the two quaternion
components; nothing is assumed.
-/

/-
Provenance (ported block: all declarations of this file).
Repository: https://github.com/macgregor-sudo/compact-albert-recognition
Commit: 40d3b344180d9ddb78aaa2876873377c1e631515
File: Glennie/Native/AlgebraLaws.lean, lines 15–77.
Author: the upstream file header carries no author line; THIRD-PARTY-NOTICES.md of that commit states
that Robert MacGregor directs the AI-generated development and is the maintainer.
SPDX-License-Identifier: Apache-2.0
Modification: declarations moved from namespace `Glennie` to `CKM.NativeDerivationTriality.Reuse` (with `open Glennie`)
and imported against the closure's identical `Glennie` definitions; bodies unchanged.

Second-hand copy: this file is identical to the earlier source port `RealOrbitSlice/Reuse/OctonionLaws.lean`
(sha256 df10200fcd85014c4ac769ad3b4a0bdc8d1ebccd8b0612c192ba0c1bfff1cd25, package claude-real-orbit-slice-2026-10-24) except that the
namespace `RealOrbitSlice.Reuse` is renamed `CKM.NativeDerivationTriality.Reuse` and module names are flattened.
-/

@[expose] public section

namespace CKM.NativeDerivationTriality.Reuse

noncomputable section

open Glennie

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem octMul_self_conj (x : Octonion) :
    octMul x (octConj x) = octScalar (octNormSq x) := by
  apply Prod.ext
  · simp [octMul, octConj, octScalar, octNormSq,
      Quaternion.self_mul_star, Quaternion.star_mul_self]
  · simp [octMul, octConj, octScalar]

theorem octMul_conj_self (x : Octonion) :
    octMul (octConj x) x = octScalar (octNormSq x) := by
  apply Prod.ext
  · simp [octMul, octConj, octScalar, octNormSq,
      Quaternion.self_mul_star, Quaternion.star_mul_self]
  · simp [octMul, octConj, octScalar]

theorem octScalar_smul (r s : ℝ) : r • octScalar s = octScalar (r*s) := by
  apply Prod.ext <;> apply Quaternion.ext <;> simp [octScalar, smul_eq_mul]

/-- Conjugate-over-positive-norm inverse in the native division octonions. -/
def octInv (x : Octonion) : Octonion := (octNormSq x)⁻¹ • octConj x

theorem octMul_inv (x : Octonion) (hx : x ≠ 0) :
    octMul x (octInv x) = octScalar 1 := by
  have hn : octNormSq x ≠ 0 := fun h => hx ((octNormSq_eq_zero x).mp h)
  rw [octInv, octMul_smul_right, octMul_self_conj, octScalar_smul, inv_mul_cancel₀ hn]

theorem octInv_mul (x : Octonion) (hx : x ≠ 0) :
    octMul (octInv x) x = octScalar 1 := by
  have hn : octNormSq x ≠ 0 := fun h => hx ((octNormSq_eq_zero x).mp h)
  rw [octInv, octMul_smul_left, octMul_conj_self, octScalar_smul, inv_mul_cancel₀ hn]

set_option maxHeartbeats 2000000 in
theorem octNormSq_mul (x y : Octonion) :
    octNormSq (octMul x y) = octNormSq x * octNormSq y := by
  simp [octNormSq, octMul, Quaternion.normSq_def', Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

set_option maxHeartbeats 2000000 in
theorem octMul_left_alternative (x y : Octonion) :
    octMul x (octMul x y) = octMul (octMul x x) y := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [octMul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

set_option maxHeartbeats 2000000 in
theorem octMul_right_alternative (x y : Octonion) :
    octMul (octMul x y) y = octMul x (octMul y y) := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [octMul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

set_option maxHeartbeats 8000000 in
theorem octMul_moufang (x y z : Octonion) :
    octMul (octMul x y) (octMul z x) = octMul (octMul x (octMul y z)) x := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [octMul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

theorem octRe_associative (x y z : Octonion) :
    octRe (octMul (octMul x y) z) = octRe (octMul x (octMul y z)) := by
  simp [octRe, octMul, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul]
  ring

end

end CKM.NativeDerivationTriality.Reuse

#print axioms CKM.NativeDerivationTriality.Reuse.octNormSq_mul
#print axioms CKM.NativeDerivationTriality.Reuse.octMul_inv
#print axioms CKM.NativeDerivationTriality.Reuse.octInv_mul
#print axioms CKM.NativeDerivationTriality.Reuse.octMul_left_alternative
#print axioms CKM.NativeDerivationTriality.Reuse.octMul_right_alternative
#print axioms CKM.NativeDerivationTriality.Reuse.octMul_moufang
#print axioms CKM.NativeDerivationTriality.Reuse.octRe_associative

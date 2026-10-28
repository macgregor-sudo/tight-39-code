module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Module

/-!
# The cubic trace identity implies the Jordan identity (generic)

For a commutative real bilinear product with unit `e` and an associative trace functional `T`, the
Newton cubic residual (six times the cubic characteristic identity) vanishing identically implies
the Jordan identity `(x ∘ y) ∘ (x ∘ x) = x ∘ (y ∘ (x ∘ x))`. The proof polarizes the residual once
(`linearResidual_eq_zero`) and writes the Jordan defect as an explicit combination of residuals.
-/

/-
Provenance (ported block: all declarations of this file).
Repository: https://github.com/macgregor-sudo/compact-albert-recognition
Commit: 40d3b344180d9ddb78aaa2876873377c1e631515
File: Glennie/Native/CubicJordan.lean, lines 16–89.
Author: the upstream file header carries no author line. That file is itself "Adapted from
AlbertLean/CubicJordan.lean in albert-lean-public-clean at dd06ef5d423a0e4a5d814d2c221e999b98887ee1,
source SHA256 cc885b590ac2317fbde15b490d8205d684fafbf7dbe4ffd883155275a0986826" (Apache-2.0; that
original file has no separate copyright/author header, per the upstream THIRD-PARTY-NOTICES.md).
Resolved ancestor repository: https://github.com/macgregor-sudo/albert-frame-triple-invariants; retained grant: LICENSES/Native-Albert-Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
Modification: namespace `Glennie.CubicJordan` renamed to `CKM.NativeDerivationTriality.Reuse.CubicJordan`; bodies unchanged.

Second-hand copy: this file is identical to the earlier source port `RealOrbitSlice/Reuse/CubicJordan.lean`
(sha256 b19ca8891e7f3ad46169f7e7374f428c29f2d65952c60174e017d0f933dcc6c3, package claude-real-orbit-slice-2026-10-24) except that the
namespace `RealOrbitSlice.Reuse` is renamed `CKM.NativeDerivationTriality.Reuse` and module names are flattened.
-/

@[expose] public section

namespace CKM.NativeDerivationTriality.Reuse.CubicJordan

noncomputable section

set_option maxHeartbeats 2000000

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Six times the cubic characteristic identity, with Newton coefficients. -/
def residual (mul : V →ₗ[ℝ] V →ₗ[ℝ] V) (T : V →ₗ[ℝ] ℝ) (e x : V) : V :=
  (6 : ℝ) • mul x (mul x x) - (6 * T x) • mul x x +
    (3 * (T x) ^ 2 - 3 * T (mul x x)) • x -
    ((T x) ^ 3 - 3 * T x * T (mul x x) + 2 * T (mul x (mul x x))) • e

/-- Twice the coefficient of the linear perturbation in the cubic identity. -/
def linearResidual (mul : V →ₗ[ℝ] V →ₗ[ℝ] V)
    (T : V →ₗ[ℝ] ℝ) (e x y : V) : V :=
  (4 : ℝ) • mul x (mul x y) + (2 : ℝ) • mul (mul x x) y -
    (2 * T y) • mul x x - (4 * T x) • mul x y +
    (2 * T x * T y - 2 * T (mul x y)) • x +
    ((T x) ^ 2 - T (mul x x)) • y -
    (((T x) ^ 2 - T (mul x x)) * T y -
      2 * T x * T (mul x y) + 2 * T (mul (mul x x) y)) • e

theorem linearResidual_eq_zero
    (mul : V →ₗ[ℝ] V →ₗ[ℝ] V) (T : V →ₗ[ℝ] ℝ) (e : V)
    (comm : ∀ x y, mul x y = mul y x)
    (assocTrace : ∀ x y z, T (mul (mul x y) z) = T (mul x (mul y z)))
    (char : ∀ x, residual mul T e x = 0) (x y : V) :
    linearResidual mul T e x y = 0 := by
  calc
    linearResidual mul T e x y = (1 / 6 : ℝ) •
        (residual mul T e (x + y) - residual mul T e (x - y) -
          (2 : ℝ) • residual mul T e y) := by
      simp only [linearResidual, residual, map_add, map_sub, map_smul,
        LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        smul_eq_mul]
      simp only [comm y x, comm y (mul x x), ← assocTrace x x y]
      module
    _ = 0 := by rw [char, char, char]; simp

/-- Concrete commutativity, unit, trace associativity and Newton residual imply Jordan. -/
theorem jordan_of_cubic_trace_identity
    (mul : V →ₗ[ℝ] V →ₗ[ℝ] V) (T : V →ₗ[ℝ] ℝ) (e : V)
    (comm : ∀ x y, mul x y = mul y x)
    (unit : ∀ x, mul e x = x)
    (assocTrace : ∀ x y z, T (mul (mul x y) z) = T (mul x (mul y z)))
    (char : ∀ x, residual mul T e x = 0) (x y : V) :
    mul (mul x y) (mul x x) = mul x (mul y (mul x x)) := by
  have unitR (z : V) : mul z e = z := by rw [comm, unit]
  have hB₁ : T (mul x (mul x y)) = T (mul (mul x x) y) :=
    (assocTrace x x y).symm
  have hB₂ : T (mul (mul x x) (mul x y)) =
      T (mul (mul x (mul x x)) y) := by
    rw [← assocTrace, comm (mul x x) x]
  have hlin := linearResidual_eq_zero mul T e comm assocTrace char
  have hj : mul (mul x x) (mul x y) - mul x (mul (mul x x) y) = 0 := by
    calc
      mul (mul x x) (mul x y) - mul x (mul (mul x x) y) =
          (-1 / 2 : ℝ) •
            (mul x (linearResidual mul T e x y) -
              linearResidual mul T e x (mul x y)) -
          (T y / 6) • residual mul T e x +
          ((1 / 6 : ℝ) * T (mul (residual mul T e x) y)) • e := by
        simp only [linearResidual, residual, map_add, map_sub, map_smul,
          LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
          smul_eq_mul, unit, unitR, hB₁, hB₂]
        module
      _ = 0 := by rw [hlin, hlin, char]; simp
  have heq := sub_eq_zero.mp hj
  simpa only [comm (mul x y) (mul x x), comm y (mul x x)] using heq

end

end CKM.NativeDerivationTriality.Reuse.CubicJordan

#print axioms CKM.NativeDerivationTriality.Reuse.CubicJordan.jordan_of_cubic_trace_identity

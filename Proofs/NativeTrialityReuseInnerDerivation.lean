module

public import NativeTrialityReuseCubicIdentity
public import Mathlib.Tactic.LinearCombination

/-!
# Inner derivations `D_{a,b} = [L_a, L_b]` of the native product

The inner operator `D_{a,b} z = a ∘ (b ∘ z) - b ∘ (a ∘ z)` of the native product is a derivation
(Leibniz law), kills the unit and is trace-free; derivations and trace-free maps are closed under
sums and real multiples.

Proof route. No literature statement is assumed. The native Jordan identity `jordan_identity` is
polarized in its cubic argument for an abstract commutative real bilinear product; the Leibniz law
is then the difference of two instances of the polarized identity:
`polar(x, a, z; b) - polar(x, b, z; a) = x ∘ Dz - D(z ∘ x) + z ∘ Dx`.
-/

/-
Provenance (ported block: all declarations of this file).
Repository: https://github.com/macgregor-sudo/compact-albert-recognition
Commit: 40d3b344180d9ddb78aaa2876873377c1e631515
File: Glennie/Compact/InnerDerivation.lean, lines 17–182.
Author: the upstream file header carries no author line; THIRD-PARTY-NOTICES.md of that commit states
that Robert MacGregor directs the AI-generated development and is the maintainer.
SPDX-License-Identifier: Apache-2.0
Modification: namespaces `Glennie.Compact.InnerDerivation` and `Glennie.Compact` renamed to
`CKM.NativeDerivationTriality.Reuse.InnerDerivation` and `CKM.NativeDerivationTriality.Reuse` (with `open Glennie`), built on the
closure's `Glennie.Albert`; `jordan_identity`, `inner_jordan_associative` resolve to their
`CKM.NativeDerivationTriality.Reuse` ports; bodies unchanged.

Second-hand copy: this file is identical to the earlier source port `RealOrbitSlice/Reuse/InnerDerivation.lean`
(sha256 3fa9057738582b830f8f1123a54cc4b8646fbb1206e19b7489d688944bf825ca, package claude-real-orbit-slice-2026-10-24) except that the
namespace `RealOrbitSlice.Reuse` is renamed `CKM.NativeDerivationTriality.Reuse` and module names are flattened.
-/

@[expose] public section

namespace CKM.NativeDerivationTriality.Reuse.InnerDerivation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The Jordan defect (x o y) o (x o x) - x o (y o (x o x)): cubic in x, linear in y. -/
def defect (mul : V →ₗ[ℝ] V →ₗ[ℝ] V) (x y : V) : V :=
  mul (mul x y) (mul x x) - mul x (mul y (mul x x))

/-- Cyclic polarization of the defect in its cubic argument. -/
def polar (mul : V →ₗ[ℝ] V →ₗ[ℝ] V) (x₁ x₂ x₃ y : V) : V :=
  (mul (mul x₁ y) (mul x₂ x₃) - mul x₁ (mul y (mul x₂ x₃))) +
    (mul (mul x₂ y) (mul x₃ x₁) - mul x₂ (mul y (mul x₃ x₁))) +
    (mul (mul x₃ y) (mul x₁ x₂) - mul x₃ (mul y (mul x₁ x₂)))

/-- The inner operator D_{a,b} z = a o (b o z) - b o (a o z). -/
def der (mul : V →ₗ[ℝ] V →ₗ[ℝ] V) (a b z : V) : V :=
  mul a (mul b z) - mul b (mul a z)

/-- Polarization: the cyclic polar form is half the seven-term alternating sum. -/
theorem polar_eq_half (mul : V →ₗ[ℝ] V →ₗ[ℝ] V) (comm : ∀ x y, mul x y = mul y x)
    (x₁ x₂ x₃ y : V) :
    polar mul x₁ x₂ x₃ y = (1 / 2 : ℝ) •
      (defect mul (x₁ + x₂ + x₃) y - defect mul (x₁ + x₂) y - defect mul (x₁ + x₃) y -
        defect mul (x₂ + x₃) y + defect mul x₁ y + defect mul x₂ y + defect mul x₃ y) := by
  simp only [polar, defect, map_add, LinearMap.add_apply]
  simp only [comm x₂ x₁, comm x₃ x₁, comm x₃ x₂]
  module

theorem polar_eq_zero (mul : V →ₗ[ℝ] V →ₗ[ℝ] V) (comm : ∀ x y, mul x y = mul y x)
    (hJ : ∀ x y, defect mul x y = 0) (x₁ x₂ x₃ y : V) :
    polar mul x₁ x₂ x₃ y = 0 := by
  rw [polar_eq_half mul comm]
  simp [hJ]

/-- Leibniz law for D_{a,b}: the difference of two polarized Jordan identities. -/
theorem der_leibniz (mul : V →ₗ[ℝ] V →ₗ[ℝ] V) (comm : ∀ x y, mul x y = mul y x)
    (hJ : ∀ x y, defect mul x y = 0) (a b z x : V) :
    der mul a b (mul z x) = mul (der mul a b z) x + mul z (der mul a b x) := by
  have E1 := polar_eq_zero mul comm hJ x a z b
  have E2 := polar_eq_zero mul comm hJ x b z a
  simp only [polar, der, map_sub, LinearMap.sub_apply] at E1 E2 ⊢
  simp only [comm x a, comm x b, comm z a, comm z b, comm b a,
    comm (mul b z) (mul a x), comm (mul a z) (mul b x),
    comm (mul a (mul b z)) x, comm (mul b (mul a z)) x] at E1 E2 ⊢
  linear_combination (norm := module) E2 - E1

end

end CKM.NativeDerivationTriality.Reuse.InnerDerivation

namespace CKM.NativeDerivationTriality.Reuse

noncomputable section

open Glennie

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem jordanLinear_comm (x y : Albert) : jordanLinear x y = jordanLinear y x := by
  simpa only [jordanLinear_apply] using jordan_comm x y

theorem defect_jordanLinear (x y : Albert) : InnerDerivation.defect jordanLinear x y = 0 := by
  simp only [InnerDerivation.defect, jordanLinear_apply]
  rw [jordan_identity, sub_self]

/-- The native inner operator D_{a,b} = [L_a, L_b]. -/
def innerDer (a b z : Albert) : Albert := jordan a (jordan b z) - jordan b (jordan a z)

/-- Leibniz law for the native inner operator. -/
theorem innerDer_jordan (a b z x : Albert) :
    innerDer a b (jordan z x) = jordan (innerDer a b z) x + jordan z (innerDer a b x) := by
  have h := InnerDerivation.der_leibniz jordanLinear jordanLinear_comm defect_jordanLinear
    a b z x
  simpa only [InnerDerivation.der, jordanLinear_apply, innerDer] using h

theorem innerDer_one (a b : Albert) : innerDer a b 1 = 0 := by
  simp only [innerDer, jordan_unit_right]
  rw [jordan_comm a b, sub_self]

/-- D_{a,b} is trace-free: derived from trace associativity, not assumed. -/
theorem trace_innerDer (a b z : Albert) : trace (innerDer a b z) = 0 := by
  have h1 := inner_jordan_associative a b z
  have h2 := inner_jordan_associative b a z
  simp only [inner] at h1 h2
  rw [innerDer, trace_sub, ← h1, ← h2, jordan_comm b a, sub_self]

/-- D_{a,b} as a real-linear map. -/
def innerDerLinear (a b : Albert) : Albert →ₗ[ℝ] Albert :=
  (jordanLinear a).comp (jordanLinear b) - (jordanLinear b).comp (jordanLinear a)

@[simp] theorem innerDerLinear_apply (a b z : Albert) :
    innerDerLinear a b z = innerDer a b z := rfl

/-- A real-linear map obeying the Leibniz law for the native product. -/
def IsJordanDerivation (D : Albert →ₗ[ℝ] Albert) : Prop :=
  ∀ x y, D (jordan x y) = jordan (D x) y + jordan x (D y)

/-- A real-linear map with trace-free image. -/
def TraceFree (D : Albert →ₗ[ℝ] Albert) : Prop := ∀ x, trace (D x) = 0

theorem isJordanDerivation_innerDerLinear (a b : Albert) :
    IsJordanDerivation (innerDerLinear a b) := by
  intro x y
  simp only [innerDerLinear_apply]
  exact innerDer_jordan a b x y

theorem traceFree_innerDerLinear (a b : Albert) : TraceFree (innerDerLinear a b) := by
  intro z
  rw [innerDerLinear_apply]
  exact trace_innerDer a b z

theorem IsJordanDerivation.zero : IsJordanDerivation 0 := by
  intro x y
  simp

theorem IsJordanDerivation.add {D E : Albert →ₗ[ℝ] Albert} (hD : IsJordanDerivation D)
    (hE : IsJordanDerivation E) : IsJordanDerivation (D + E) := by
  intro x y
  simp only [LinearMap.add_apply, hD x y, hE x y, jordan_add_left, jordan_add_right]
  module

theorem IsJordanDerivation.smul (r : ℝ) {D : Albert →ₗ[ℝ] Albert}
    (hD : IsJordanDerivation D) : IsJordanDerivation (r • D) := by
  intro x y
  simp only [LinearMap.smul_apply, hD x y, jordan_smul_left, jordan_smul_right, smul_add]

theorem IsJordanDerivation.sum {ι : Type*} (s : Finset ι) (D : ι → Albert →ₗ[ℝ] Albert)
    (hD : ∀ i ∈ s, IsJordanDerivation (D i)) : IsJordanDerivation (∑ i ∈ s, D i) :=
  Finset.sum_induction D IsJordanDerivation (fun _ _ h₁ h₂ => h₁.add h₂)
    IsJordanDerivation.zero hD

/-- Every derivation kills the unit: D 1 = D (1 o 1) = 2 D 1. -/
theorem IsJordanDerivation.map_one {D : Albert →ₗ[ℝ] Albert} (hD : IsJordanDerivation D) :
    D 1 = 0 := by
  have h := hD 1 1
  simp only [jordan_unit_left, jordan_unit_right] at h
  have h2 : D 1 + D 1 = D 1 + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel h2

theorem TraceFree.zero : TraceFree 0 := by
  intro x
  simp [trace]

theorem TraceFree.add {D E : Albert →ₗ[ℝ] Albert} (hD : TraceFree D) (hE : TraceFree E) :
    TraceFree (D + E) := by
  intro x
  simp only [LinearMap.add_apply, trace_add, hD x, hE x, add_zero]

theorem TraceFree.smul (r : ℝ) {D : Albert →ₗ[ℝ] Albert} (hD : TraceFree D) :
    TraceFree (r • D) := by
  intro x
  simp only [LinearMap.smul_apply, trace_smul, hD x, mul_zero]

theorem TraceFree.sum {ι : Type*} (s : Finset ι) (D : ι → Albert →ₗ[ℝ] Albert)
    (hD : ∀ i ∈ s, TraceFree (D i)) : TraceFree (∑ i ∈ s, D i) :=
  Finset.sum_induction D TraceFree (fun _ _ h₁ h₂ => h₁.add h₂) TraceFree.zero hD

end

end CKM.NativeDerivationTriality.Reuse

#print axioms CKM.NativeDerivationTriality.Reuse.innerDer_jordan
#print axioms CKM.NativeDerivationTriality.Reuse.isJordanDerivation_innerDerLinear
#print axioms CKM.NativeDerivationTriality.Reuse.traceFree_innerDerLinear
#print axioms CKM.NativeDerivationTriality.Reuse.IsJordanDerivation.map_one
#print axioms CKM.NativeDerivationTriality.Reuse.IsJordanDerivation.sum
#print axioms CKM.NativeDerivationTriality.Reuse.TraceFree.sum

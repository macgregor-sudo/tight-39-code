module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Optional finite-overlap scalar gap from actual curvature

Dependency pin: Lean 4.35.0-rc2 / Mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55. This file has no core-prototype
dependency and imports no integral Taylor theorem. No native overlaps,
quartic distance floor, probability statement or sharpness are asserted.
-/

open scoped BigOperators

namespace SupportedStress

theorem scalar_curvature_lower_taylor_gap
    (φ : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hconvex : Convex ℝ U)
    (hφ : ContDiffOn ℝ 2 φ U) (k : ℝ)
    (hcurv : ∀ x ∈ U, k ≤ deriv (deriv φ) x)
    (a x : ℝ) (ha : a ∈ U) (hx : x ∈ U) :
    (k / 2) * (x - a) ^ 2 ≤ φ x - φ a - deriv φ a * (x - a) := by
  let ψ : ℝ → ℝ := fun y => φ y - (k / 2) * y ^ 2
  let ψ' : ℝ → ℝ := fun y => deriv φ y - k * y
  have hφ' : ContDiffOn ℝ 1 (deriv φ) U := hφ.deriv_of_isOpen hU (by norm_num)
  have hφderiv : ∀ y ∈ U, HasDerivAt φ (deriv φ y) y := by
    intro y hy
    exact ((hφ.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hy)).hasDerivAt
  have hφsecond : ∀ y ∈ U, HasDerivAt (deriv φ) (deriv (deriv φ) y) y := by
    intro y hy
    exact (hφ'.differentiableOn_one.differentiableAt (hU.mem_nhds hy)).hasDerivAt
  have hpolynomial : ∀ y : ℝ, HasDerivAt (fun z : ℝ => (k / 2) * z ^ 2) (k * y) y := by
    intro y
    apply (HasDerivAt.const_mul (k / 2) (hasDerivAt_pow 2 y)).congr_deriv
    norm_num <;> ring
  have hψderiv : ∀ y ∈ U, HasDerivAt ψ (ψ' y) y := by
    intro y hy
    exact (hφderiv y hy).sub (hpolynomial y)
  have hψsecond : ∀ y ∈ U,
      HasDerivAt ψ' (deriv (deriv φ) y - k) y := by
    intro y hy
    have hlinear : HasDerivAt (fun z : ℝ => k * z) k y := hasDerivAt_const_mul k
    exact (hφsecond y hy).sub hlinear
  have hψcontinuous : ContinuousOn ψ U := by
    intro y hy
    exact (hψderiv y hy).continuousAt.continuousWithinAt
  have hψconvex : ConvexOn ℝ U ψ :=
    convexOn_of_hasDerivWithinAt2_nonneg (f' := ψ')
      (f'' := fun y => deriv (deriv φ) y - k) hconvex hψcontinuous
      (fun y hy => (hψderiv y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => (hψsecond y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => sub_nonneg.mpr (hcurv y (interior_subset hy)))
  have htangent : ψ' a * (x - a) ≤ ψ x - ψ a := by
    rcases lt_trichotomy a x with hax | hax | hxa
    · have h := hψconvex.le_slope_of_hasDerivAt ha hx hax (hψderiv a ha)
      rw [slope_def_field] at h
      exact (le_div_iff₀ (sub_pos.mpr hax)).mp h
    · subst x
      simp
    · have h := hψconvex.slope_le_of_hasDerivAt hx ha hxa (hψderiv a ha)
      rw [slope_def_field] at h
      have hmul := (div_le_iff₀ (sub_pos.mpr hxa)).mp h
      nlinarith
  dsimp [ψ, ψ'] at htangent
  nlinarith

theorem finite_overlap_gap_of_curvature
    {ι : Type*} [Fintype ι]
    (φ : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hconvex : Convex ℝ U)
    (hφ : ContDiffOn ℝ 2 φ U)
    (a m M : ℝ) (ha : a ∈ U) (hm : 0 < m)
    (hcurv : ∀ x ∈ U, m ≤ deriv (deriv φ) x ∧ deriv (deriv φ) x ≤ M)
    (δ : ι → ℝ) (hshift : ∀ i : ι, a + δ i ∈ U) (hsum : ∑ i, δ i = 0) :
    (m / 2) * (∑ i, (δ i) ^ 2) ≤ ∑ i, (φ (a + δ i) - φ a) ∧
      (∑ i, (φ (a + δ i) - φ a)) ≤ (M / 2) * (∑ i, (δ i) ^ 2) := by
  classical
  have hnegD : deriv (-φ) = -deriv φ := by
    ext x
    exact deriv.neg
  have hnegCurv : ∀ x ∈ U, -M ≤ deriv (deriv (-φ)) x := by
    intro x hx
    rw [hnegD, deriv.neg]
    exact neg_le_neg (hcurv x hx).2
  have hpoint : ∀ i : ι,
      (m / 2) * (δ i) ^ 2 ≤ φ (a + δ i) - φ a - deriv φ a * δ i ∧
      φ (a + δ i) - φ a - deriv φ a * δ i ≤ (M / 2) * (δ i) ^ 2 := by
    intro i
    have hlo := scalar_curvature_lower_taylor_gap φ U hU hconvex hφ m
      (fun x hx => (hcurv x hx).1) a (a + δ i) ha (hshift i)
    have hup := scalar_curvature_lower_taylor_gap (-φ) U hU hconvex hφ.neg (-M)
      hnegCurv a (a + δ i) ha (hshift i)
    simp only [add_sub_cancel_left] at hlo
    simp only [Pi.neg_apply, deriv.neg, add_sub_cancel_left] at hup
    exact ⟨hlo, by nlinarith [hup]⟩
  have hlo : (∑ i, (m / 2) * (δ i) ^ 2) ≤
      ∑ i, (φ (a + δ i) - φ a - deriv φ a * δ i) :=
    Finset.sum_le_sum (fun i _ => (hpoint i).1)
  have hup : (∑ i, (φ (a + δ i) - φ a - deriv φ a * δ i)) ≤
      ∑ i, (M / 2) * (δ i) ^ 2 :=
    Finset.sum_le_sum (fun i _ => (hpoint i).2)
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_zero, sub_zero]
    using And.intro hlo hup

end SupportedStress

module

public import TCDefs

@[expose] public section

/-!
# A7: native pairing facts and nonnegative overlaps of pure points 

Route: `L_e` is self-adjoint for the trace pairing (`inner_jordan_associative` + `jordan_comm`). For an
idempotent `e` the polarized Jordan identity (`InnerDerivation.polar_eq_zero` with
`(x₁, x₂, x₃, y) = (z, e, e, e)`, `defect_jordanLinear`) gives the Peirce cubic
`2 L_e³ - 3 L_e² + L_e = 0`. Since `L = L(2L - 1) + 2 L(1 - L)` identically and `E = L(2L - 1)`,
`4L(1 - L)` are idempotent modulo the cubic, `⟨L z, z⟩ = ⟨E z, E z⟩ + 8 ⟨F z, F z⟩` with
`F = L(1 - L)`, hence `≥ 0`. Then `⟨p, q⟩ = ⟨p, q ∘ q⟩ = ⟨p ∘ q, q⟩ = ⟨L_p q, q⟩ ≥ 0`.
Peirce decomposition: K. McCrimmon, *A Taste of Jordan Algebras* (Springer, 2004), Peirce
Decomposition Theorem 8.1.2 (pp. 236–237; the remark on p. 237 that `L_e` satisfies
`(t - 1)(t - 1/2)t = 0`) and Peirce Eigenspace Laws 8.1.4 (p. 238; eigenvalues `0, 1/2, 1`). The
cubic is proved here from the accepted native Jordan identity, not imported.
-/

noncomputable section

namespace CKM.NativeTightCode

open Glennie

theorem inner_one_right (x : Albert) : inner x 1 = trace x := by
  rw [inner, jordan_unit_right]

theorem inner_one_one : inner (1 : Albert) 1 = 3 := by
  rw [inner_one_right, trace_unit]

theorem inner_self_of_pure {p : Albert} (hp : IsPure p) : inner p p = 1 := by
  rw [inner, hp.1, hp.2]

theorem trace_centered {p : Albert} (hp : IsPure p) : trace (centered p) = 0 := by
  rw [centered, trace_sub, trace_smul, trace_unit, hp.2]
  norm_num

/-- `⟨P i - 1/3, P j - 1/3⟩ = ⟨P i, P j⟩ - 1/3` for pure points. -/
theorem inner_centered {p q : Albert} (hp : IsPure p) (hq : IsPure q) :
    inner (centered p) (centered q) = inner p q - 1 / 3 := by
  have h1 : inner (1 : Albert) q = 1 := by rw [inner_comm, inner_one_right, hq.2]
  have h2 : inner p (1 : Albert) = 1 := by rw [inner_one_right, hp.2]
  simp only [centered, NativeDerivationTriality.Reuse.inner_sub_left, NativeDerivationTriality.Reuse.inner_sub_right,
    NativeDerivationTriality.Reuse.inner_smul_left, NativeDerivationTriality.Reuse.inner_smul_right, h1, h2, inner_one_one]
  ring

/-- `L_e` is self-adjoint for the native trace pairing. -/
theorem inner_jordan_left_right (e x y : Albert) :
    inner (jordan e x) y = inner x (jordan e y) := by
  rw [jordan_comm e x, NativeDerivationTriality.Reuse.inner_jordan_associative]

/-- The Peirce cubic `2 L_e³ - 3 L_e² + L_e = 0` for a native idempotent. -/
theorem peirce_cubic {e : Albert} (he : jordan e e = e) (z : Albert) :
    (2 : ℝ) • jordan e (jordan e (jordan e z)) - (3 : ℝ) • jordan e (jordan e z) + jordan e z = 0 := by
  have h := NativeDerivationTriality.Reuse.InnerDerivation.polar_eq_zero jordanLinear
    NativeDerivationTriality.Reuse.jordanLinear_comm NativeDerivationTriality.Reuse.defect_jordanLinear z e e e
  simp only [NativeDerivationTriality.Reuse.InnerDerivation.polar, jordanLinear_apply, he] at h
  rw [jordan_comm z e, jordan_comm (jordan e z) e] at h
  linear_combination (norm := module) (-1 : ℝ) • h

/-- `L_e` is positive semidefinite for a native idempotent `e`. -/
theorem inner_jordan_self_nonneg {e : Albert} (he : jordan e e = e) (z : Albert) :
    0 ≤ inner (jordan e z) z := by
  -- a = L z, b = L² z, c = L³ z; the cubic reads 2c - 3b + a = 0.
  have hc := peirce_cubic he z
  have hz : inner z ((2 : ℝ) • jordan e (jordan e (jordan e z)) - (3 : ℝ) • jordan e (jordan e z) +
      jordan e z) = 0 := by rw [hc]; simp [inner, trace]
  have ha : inner (jordan e z) ((2 : ℝ) • jordan e (jordan e (jordan e z)) -
      (3 : ℝ) • jordan e (jordan e z) + jordan e z) = 0 := by rw [hc]; simp [inner, trace]
  simp only [NativeDerivationTriality.Reuse.inner_add_right, NativeDerivationTriality.Reuse.inner_sub_right, NativeDerivationTriality.Reuse.inner_smul_right] at hz ha
  have s1 := inner_jordan_left_right e z (jordan e z)
  have s2 := inner_jordan_left_right e z (jordan e (jordan e z))
  have s3 := inner_jordan_left_right e (jordan e z) (jordan e (jordan e z))
  -- `E z = 2 b - a` and `F z = a - b`; `⟨L z, z⟩ = ⟨E z, E z⟩ + 8 ⟨F z, F z⟩`.
  have hE := inner_self_nonneg ((2 : ℝ) • jordan e (jordan e z) - jordan e z)
  have hF := inner_self_nonneg (jordan e z - jordan e (jordan e z))
  simp only [NativeDerivationTriality.Reuse.inner_sub_left, NativeDerivationTriality.Reuse.inner_sub_right, NativeDerivationTriality.Reuse.inner_smul_left,
    NativeDerivationTriality.Reuse.inner_smul_right] at hE hF
  have c1 := inner_comm (jordan e z) z
  have c2 := inner_comm (jordan e (jordan e z)) (jordan e z)
  nlinarith

/-- Overlaps of native idempotents are nonnegative. -/
theorem overlap_nonneg {p q : Albert} (hp : jordan p p = p) (hq : jordan q q = q) :
    0 ≤ inner p q := by
  calc (0 : ℝ) ≤ inner (jordan p q) q := inner_jordan_self_nonneg hp q
    _ = inner p (jordan q q) := NativeDerivationTriality.Reuse.inner_jordan_associative p q q
    _ = inner p q := by rw [hq]

/-- Overlaps of pure points are at most one. -/
theorem overlap_le_one {p q : Albert} (hp : IsPure p) (hq : IsPure q) : inner p q ≤ 1 := by
  have h := inner_self_nonneg (p - q)
  simp only [NativeDerivationTriality.Reuse.inner_sub_left, NativeDerivationTriality.Reuse.inner_sub_right, inner_self_of_pure hp,
    inner_self_of_pure hq, inner_comm q p] at h
  linarith

#print axioms inner_centered
#print axioms peirce_cubic
#print axioms inner_jordan_self_nonneg
#print axioms overlap_nonneg
#print axioms overlap_le_one

end CKM.NativeTightCode

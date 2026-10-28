module

public import FourBlockQuarticConsequences
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
The literal four-complex-triple identity in BOOK-PROOF (12) and
notes/MASTER-IDENTITY, Appendix, 2026-10-25. All scalars for quadratic maps
are real; the three-coordinate norm is Euclidean, not the Pi supremum norm.
This proves no original-row covector, native eigenbasis or metric binding.
-/

noncomputable section

namespace Option2.NativeStress.BookHT

open scoped BigOperators InnerProductSpace ComplexConjugate
open WithLp

abbrev Triple := EuclideanSpace ℂ (Fin 3)
abbrev Blocks := Fin 4 → Triple

/-- The Book's polynomial gradient, not its real metric gradient. -/
def sigmaValue (v : Triple) : Triple :=
  toLp 2 ![v 1 * v 2, v 2 * v 0, v 0 * v 1]

/-- Literal H components in block order a,b,c,d, component order 0,1,2. -/
def HValue (z : Blocks) : Blocks :=
  let a := z 0; let b := z 1; let c := z 2; let d := z 3
  ![toLp 2 ![d 0 * conj (c 0) + b 1 * conj (d 1) - c 2 * conj (b 2),
      b 0 * conj (d 0) + c 1 * conj (b 1) - d 2 * conj (c 2),
      -c 0 * conj (b 0) - d 1 * conj (c 1) - b 2 * conj (d 2)],
    toLp 2 ![-a 1 * conj (d 0) + conj (a 2) * conj (c 0) + d 1 * c 2,
      -a 0 * conj (d 1) - conj (a 1) * conj (c 1) - c 0 * d 2,
      conj (a 0) * conj (c 2) + a 2 * conj (d 2) - d 0 * c 1],
    toLp 2 ![conj (a 0) * conj (d 0) - a 2 * conj (b 0) + d 2 * b 1,
      a 1 * conj (b 1) - conj (a 2) * conj (d 1) + d 0 * b 2,
      -a 0 * conj (b 2) - conj (a 1) * conj (d 2) - b 0 * d 1],
    toLp 2 ![-a 0 * conj (c 0) - conj (a 1) * conj (b 0) - c 1 * b 2,
      -conj (a 0) * conj (b 1) + a 2 * conj (c 1) + b 0 * c 2,
      a 1 * conj (c 2) + conj (a 2) * conj (b 2) - c 0 * b 1]]

/-- Literal T components with the same block and component orders. -/
def TValue (z : Blocks) : Blocks :=
  let a := z 0; let b := z 1; let c := z 2; let d := z 3
  ![toLp 2 ![-b 0 * conj (d 2) + d 0 * conj (c 2) - c 0 * conj (b 2),
      -b 0 * conj (c 1) - d 0 * conj (b 1) - c 0 * conj (d 1),
      -b 1 * conj (c 2) + d 1 * conj (b 2) + c 1 * conj (d 2)],
    toLp 2 ![a 0 * c 1 + conj (a 1) * d 1 - conj (d 0) * conj (c 2),
      -a 0 * conj (d 2) - conj (a 2) * conj (c 2) - c 0 * d 1,
      a 1 * c 0 - conj (a 2) * d 0 + conj (d 2) * conj (c 1)],
    toLp 2 ![a 0 * d 2 + conj (a 1) * b 2 + conj (d 0) * conj (b 1),
      -a 0 * conj (b 0) + conj (a 2) * conj (d 0) - d 1 * b 2,
      a 1 * d 1 - conj (a 2) * b 1 + conj (b 0) * conj (d 2)],
    toLp 2 ![a 0 * b 0 + conj (a 1) * c 0 - conj (c 2) * conj (b 1),
      -a 0 * conj (c 1) + conj (a 2) * conj (b 1) - c 0 * b 2,
      a 1 * b 2 + conj (a 2) * c 2 + conj (b 0) * conj (c 1)]]

private theorem triple_norm_sq (v : Triple) :
    ‖v‖ ^ 2 = ∑ a, Complex.normSq (v a) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Complex.normSq_eq_norm_sq]

private theorem triple_inner (v w : Triple) :
    ⟪v, w⟫_ℝ = (∑ a, conj (v a) * w a).re := by
  simp [PiLp.inner_apply, real_inner_eq_re_inner, RCLike.inner_apply,
    Fin.sum_univ_succ, mul_comm]

private theorem ofReal_re_eq (v : ℂ) : (v.re : ℂ) = (v + conj v) / 2 := by
  have h := Complex.add_conj v
  push_cast at h
  linear_combination -h / 2

/-- The all-input real quartic identity for the literal Appendix formulas. -/
theorem quartic_identity_values (z : Blocks) :
    FourBlock.delta z = FourBlock.totalSquaredLength (HValue z) +
      (1 / 2 : ℝ) * FourBlock.totalSquaredLength (TValue z) +
      3 * ∑ i, ⟪sigmaValue (z i), HValue z i⟫_ℝ := by
  simp only [FourBlock.delta, FourBlock.crossEnergy, FourBlock.totalSquaredLength,
    triple_norm_sq, triple_inner]
  simp only [Fin.sum_univ_succ, HValue, TValue, sigmaValue,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    PiLp.toLp_apply]
  norm_num only [Fin.reduceLT, ite_true, ite_false, add_zero, zero_add]
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.mul_conj, ofReal_re_eq, map_add, map_sub,
    map_mul, map_neg, starRingEnd_self_apply]
  ring

private theorem H_smul (r : ℝ) (z : Blocks) :
    HValue (r • z) = (r * r) • HValue z := by
  funext i; apply PiLp.ext; intro a
  fin_cases i <;> fin_cases a <;>
    simp [HValue, PiLp.smul_apply, Complex.real_smul] <;> ring

private theorem H_polar_add (x y z : Blocks) :
    QuadraticMap.polar HValue (x + y) z =
      QuadraticMap.polar HValue x z + QuadraticMap.polar HValue y z := by
  funext i; apply PiLp.ext; intro a
  fin_cases i <;> fin_cases a <;>
    simp [QuadraticMap.polar, HValue, PiLp.add_apply, PiLp.sub_apply] <;> ring

private theorem H_polar_smul (r : ℝ) (x y : Blocks) :
    QuadraticMap.polar HValue (r • x) y = r • QuadraticMap.polar HValue x y := by
  funext i; apply PiLp.ext; intro a
  fin_cases i <;> fin_cases a <;>
    simp [QuadraticMap.polar, HValue, PiLp.add_apply, PiLp.sub_apply,
      PiLp.smul_apply, Complex.real_smul] <;> ring

/-- The literal H, as a genuine real quadratic map. -/
def H : QuadraticMap ℝ Blocks Blocks :=
  QuadraticMap.ofPolar HValue (by exact H_smul) (by exact H_polar_add)
    (by exact H_polar_smul)

private theorem T_smul (r : ℝ) (z : Blocks) :
    TValue (r • z) = (r * r) • TValue z := by
  funext i; apply PiLp.ext; intro a
  fin_cases i <;> fin_cases a <;>
    simp [TValue, PiLp.smul_apply, Complex.real_smul] <;> ring

private theorem T_polar_add (x y z : Blocks) :
    QuadraticMap.polar TValue (x + y) z =
      QuadraticMap.polar TValue x z + QuadraticMap.polar TValue y z := by
  funext i; apply PiLp.ext; intro a
  fin_cases i <;> fin_cases a <;>
    simp [QuadraticMap.polar, TValue, PiLp.add_apply, PiLp.sub_apply] <;> ring

private theorem T_polar_smul (r : ℝ) (x y : Blocks) :
    QuadraticMap.polar TValue (r • x) y = r • QuadraticMap.polar TValue x y := by
  funext i; apply PiLp.ext; intro a
  fin_cases i <;> fin_cases a <;>
    simp [QuadraticMap.polar, TValue, PiLp.add_apply, PiLp.sub_apply,
      PiLp.smul_apply, Complex.real_smul] <;> ring

/-- The literal T, as a genuine real quadratic map. -/
def T : QuadraticMap ℝ Blocks Blocks :=
  QuadraticMap.ofPolar TValue (by exact T_smul) (by exact T_polar_add)
    (by exact T_polar_smul)

/-- The same polynomial gradient on each of the four blocks. -/
def sigma : QuadraticMap ℝ Triple Triple := QuadraticMap.ofPolar sigmaValue
  (by
    intro r z
    ext a
    fin_cases a <;> simp [sigmaValue, PiLp.smul_apply, Complex.real_smul] <;> ring)
  (by
    intro x y z
    ext a
    fin_cases a <;>
      simp [QuadraticMap.polar, sigmaValue, PiLp.add_apply, PiLp.sub_apply] <;> ring)
  (by
    intro r x y
    ext a
    fin_cases a <;>
      simp [QuadraticMap.polar, sigmaValue, PiLp.add_apply, PiLp.sub_apply,
        PiLp.smul_apply, Complex.real_smul] <;> ring)

@[simp] theorem H_apply (z : Blocks) : H z = HValue z := rfl
@[simp] theorem T_apply (z : Blocks) : T z = TValue z := rfl
@[simp] theorem sigma_apply (z : Triple) : sigma z = sigmaValue z := rfl

/-- The abstract identity premise is discharged for the literal Book quadrics. -/
theorem quartic_identity : FourBlock.QuarticIdentity H T (fun _ => sigma) :=
  quartic_identity_values

/-- Book (12), with conjugate-linear first slot and explicit Hermitian sums. -/
theorem quartic_identity_hermitian (z : Blocks) :
    FourBlock.delta z = (∑ i, ‖H z i‖ ^ 2) +
      (1 / 2 : ℝ) * (∑ i, ‖T z i‖ ^ 2) +
      3 * (∑ i, ∑ a, conj (sigma (z i) a) * H z i a).re := by
  have h := quartic_identity_values z
  simpa only [FourBlock.totalSquaredLength, triple_inner, H_apply, T_apply,
    sigma_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, Complex.add_re,
    Complex.zero_re, add_zero] using h

/-- Every literal component vanishes on each actual coordinate axis. -/
theorem axis_vanishing (i : Fin 4) (z : Blocks) (hz : FourBlock.OnAxis i z) :
    H z = 0 ∧ T z = 0 := by
  have heq : z = Pi.single i (z i) := by
    funext j
    by_cases hji : j = i
    · subst j; simp
    · simp [hji, hz j hji]
  rw [heq]
  constructor <;> ext j a <;> fin_cases i <;> fin_cases j <;> fin_cases a <;>
    simp [HValue, TValue]

/-- The exact real zero set, reusing the existing conditional cone theorem. -/
theorem zero_cone (z : Blocks) :
    (H z = 0 ∧ T z = 0) ↔ ∃ i, FourBlock.OnAxis i z :=
  FourBlock.zero_cone H T (fun _ => sigma) quartic_identity axis_vanishing z

/-- The full cross term is Q(w+n)-Q(w)-Q(n); no half-polar convention is used. -/
theorem kernel_stress_identity (i : Fin 4) (w n : Blocks)
    (hw : FourBlock.OnAxis i w) (hn : n i = 0)
    (hH : QuadraticMap.polar H w n = 0) (hT : QuadraticMap.polar T w n = 0) :
    3 * ⟪sigma (w i), H n i⟫_ℝ = ‖w i‖ ^ 2 * FourBlock.totalSquaredLength n :=
  FourBlock.kernel_stress_identity H T (fun _ => sigma) quartic_identity axis_vanishing
    i w n hw hn hH hT

theorem kernel_stress_pos (i : Fin 4) (w n : Blocks)
    (hw : FourBlock.OnAxis i w) (hn : n i = 0) (hw0 : w ≠ 0) (hn0 : n ≠ 0)
    (hH : QuadraticMap.polar H w n = 0) (hT : QuadraticMap.polar T w n = 0) :
    0 < 3 * ⟪sigma (w i), H n i⟫_ℝ :=
  FourBlock.kernel_stress_pos H T (fun _ => sigma) quartic_identity axis_vanishing
    i w n hw hn hw0 hn0 hH hT

theorem kernel_eq_zero_of_sigma_eq_zero (i : Fin 4) (w n : Blocks)
    (hw : FourBlock.OnAxis i w) (hn : n i = 0) (hw0 : w ≠ 0)
    (hsigma : sigma (w i) = 0)
    (hH : QuadraticMap.polar H w n = 0) (hT : QuadraticMap.polar T w n = 0) : n = 0 :=
  FourBlock.kernel_eq_zero_of_sigma_eq_zero H T (fun _ => sigma) quartic_identity
    axis_vanishing i w n hw hn hw0 hsigma hH hT

end Option2.NativeStress.BookHT

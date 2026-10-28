module

public import A4RootSystem

@[expose] public section

/-!
# Plane rotations of the native octonions and their conjugation action on `skewEnd`

`planeRot z` rotates coordinate plane `r` by the unit complex number `z r`; `adRot z` is conjugation
by it. On root vectors it rotates `(X, Y)` by `rootValue z α = z_r z_s^{±1}`; it fixes the Cartan
generators. The fixed space of any finite family of such conjugations, inside `skewEnd`, is the span
of the four Cartan generators and the root planes whose root values are all one.
-/

noncomputable section

namespace CKM.NativeIntrinsicTriality

open Glennie CKM.NativeDerivationTriality
open CKM.NativeFirstOrder (fixedSpace mem_fixedSpace)

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Plane rotations and their conjugation action -/

/-- Rotation of plane `r` by the complex number `z r` (`e_{2r} ↦ Re z e_{2r} + Im z e_{2r+1}`). -/
def planeRot (z : Fin 4 → ℂ) : Module.End ℝ Octonion where
  toFun x :=
    (⟨(z 0).re * x.1.re - (z 0).im * x.1.imI, (z 0).im * x.1.re + (z 0).re * x.1.imI,
      (z 1).re * x.1.imJ - (z 1).im * x.1.imK, (z 1).im * x.1.imJ + (z 1).re * x.1.imK⟩,
     ⟨(z 2).re * x.2.re - (z 2).im * x.2.imI, (z 2).im * x.2.re + (z 2).re * x.2.imI,
      (z 3).re * x.2.imJ - (z 3).im * x.2.imK, (z 3).im * x.2.imJ + (z 3).re * x.2.imK⟩)
  map_add' x y := by
    apply Prod.ext <;> apply Quaternion.ext <;> simp <;> ring
  map_smul' c x := by
    apply Prod.ext <;> apply Quaternion.ext <;> simp <;> ring

theorem planeRot_apply (z : Fin 4 → ℂ) (x : Octonion) :
    planeRot z x =
    (⟨(z 0).re * x.1.re - (z 0).im * x.1.imI, (z 0).im * x.1.re + (z 0).re * x.1.imI,
      (z 1).re * x.1.imJ - (z 1).im * x.1.imK, (z 1).im * x.1.imJ + (z 1).re * x.1.imK⟩,
     ⟨(z 2).re * x.2.re - (z 2).im * x.2.imI, (z 2).im * x.2.re + (z 2).re * x.2.imI,
      (z 3).re * x.2.imJ - (z 3).im * x.2.imK, (z 3).im * x.2.imJ + (z 3).re * x.2.imK⟩) := rfl

theorem planeRot_planeFst (z : Fin 4 → ℂ) (r : Fin 4) :
    planeRot z (octBasis (planeFst r)) =
      (z r).re • octBasis (planeFst r) + (z r).im • octBasis (planeSnd r) := by
  fin_cases r <;>
    (apply Prod.ext <;> apply Quaternion.ext <;>
      simp [planeRot_apply, octBasis, octOfCoord, planeFst, planeSnd, ])

theorem planeRot_planeSnd (z : Fin 4 → ℂ) (r : Fin 4) :
    planeRot z (octBasis (planeSnd r)) =
      -((z r).im • octBasis (planeFst r)) + (z r).re • octBasis (planeSnd r) := by
  fin_cases r <;>
    (apply Prod.ext <;> apply Quaternion.ext <;>
      simp [planeRot_apply, octBasis, octOfCoord, planeFst, planeSnd, ])

theorem planeRot_planeSnd' (z : Fin 4 → ℂ) (r : Fin 4) :
    planeRot z (octBasis (planeSnd r)) =
      (-(z r).im) • octBasis (planeFst r) + (z r).re • octBasis (planeSnd r) := by
  rw [planeRot_planeSnd, neg_smul]

theorem planeRot_mul (z w : Fin 4 → ℂ) : planeRot z * planeRot w = planeRot (z * w) := by
  refine LinearMap.ext fun x => ?_
  rw [Module.End.mul_apply]
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [planeRot_apply, Complex.mul_re, Complex.mul_im] <;> ring

theorem planeRot_one : planeRot 1 = 1 := by
  refine LinearMap.ext fun x => ?_
  apply Prod.ext <;> apply Quaternion.ext <;> simp [planeRot_apply]

theorem planeRot_octDot {z : Fin 4 → ℂ} (hz : ∀ r, Complex.normSq (z r) = 1) (x y : Octonion) :
    octDot (planeRot z x) (planeRot z y) = octDot x y := by
  have h : ∀ r, (z r).re * (z r).re + (z r).im * (z r).im = 1 := fun r => by
    rw [← Complex.normSq_apply]; exact hz r
  rw [octDot_coordinates, octDot_coordinates]
  dsimp only [planeRot_apply]
  linear_combination (x.1.re * y.1.re + x.1.imI * y.1.imI) * h 0 +
    (x.1.imJ * y.1.imJ + x.1.imK * y.1.imK) * h 1 +
    (x.2.re * y.2.re + x.2.imI * y.2.imI) * h 2 +
    (x.2.imJ * y.2.imJ + x.2.imK * y.2.imK) * h 3

/-- The conjugate of a unit tuple is a unit tuple. -/
theorem normSq_star_eq_one {z : Fin 4 → ℂ} (hz : ∀ r, Complex.normSq (z r) = 1) :
    ∀ r, Complex.normSq ((star z) r) = 1 := fun r => by
  rw [Pi.star_apply, Complex.star_def, Complex.normSq_conj]; exact hz r

theorem mul_star_eq_one {z : Fin 4 → ℂ} (hz : ∀ r, Complex.normSq (z r) = 1) : z * star z = 1 := by
  funext r
  rw [Pi.mul_apply, Pi.star_apply, Complex.star_def, Complex.mul_conj, hz r, Pi.one_apply,
    Complex.ofReal_one]

theorem star_mul_eq_one {z : Fin 4 → ℂ} (hz : ∀ r, Complex.normSq (z r) = 1) : star z * z = 1 := by
  rw [mul_comm]; exact mul_star_eq_one hz

theorem planeRot_mul_star {z : Fin 4 → ℂ} (hz : ∀ r, Complex.normSq (z r) = 1) :
    planeRot z * planeRot (star z) = 1 := by
  rw [planeRot_mul, mul_star_eq_one hz, planeRot_one]

theorem planeRot_star_mul {z : Fin 4 → ℂ} (hz : ∀ r, Complex.normSq (z r) = 1) :
    planeRot (star z) * planeRot z = 1 := by
  rw [planeRot_mul, star_mul_eq_one hz, planeRot_one]

/-- Adjointness of a unit plane rotation: `⟨v, R⁻¹ x⟩ = ⟨R v, x⟩`. -/
theorem octDot_planeRot_star {z : Fin 4 → ℂ} (hz : ∀ r, Complex.normSq (z r) = 1) (v x : Octonion) :
    octDot v (planeRot (star z) x) = octDot (planeRot z v) x := by
  conv_rhs => rw [← Module.End.one_apply (R := ℝ) x, ← planeRot_mul_star hz, Module.End.mul_apply]
  rw [planeRot_octDot hz]

/-- Bilinear expansion of the bivector map. -/
theorem wedge_lin (a b c d : ℝ) (u v u' v' : Octonion) :
    wedge (a • u + b • v) (c • u' + d • v') =
      (a * c) • wedge u u' + (a * d) • wedge u v' + (b * c) • wedge v u' + (b * d) • wedge v v' := by
  refine LinearMap.ext fun x => ?_
  simp only [wedge_apply, LinearMap.add_apply, LinearMap.smul_apply, octDot_add_left,
    octDot_smul_left]
  module

-- (integration) `wedge_self`, `wedge_swap` are taken from `A4RootSystem`.

/-- Conjugating a bivector map by a unit plane rotation rotates its two vectors. -/
theorem planeRot_wedge {z : Fin 4 → ℂ} (hz : ∀ r, Complex.normSq (z r) = 1) (u v : Octonion) :
    planeRot z * wedge u v * planeRot (star z) = wedge (planeRot z u) (planeRot z v) := by
  refine LinearMap.ext fun x => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, wedge_apply, wedge_apply, map_sub, map_smul,
    map_smul, octDot_planeRot_star hz, octDot_planeRot_star hz]

theorem planeRot_neg (z : Fin 4 → ℂ) : planeRot (-z) = -planeRot z := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.neg_apply]
  apply Prod.ext <;> apply Quaternion.ext <;> simp [planeRot_apply] <;> ring

/-- Membership in `skewEnd`, unfolded (same argument as the triality block's `mem_skewEnd_iff`,
`NativeTrialitySkewDim.lean`, which this file does not import). -/
theorem mem_skewEnd_iff' {T : Module.End ℝ Octonion} :
    T ∈ skewEnd ↔ ∀ x y, octDot (T x) y = -octDot x (T y) := by
  show T ∈ octDotForm.skewAdjointSubmodule ↔ _
  rw [LinearMap.mem_skewAdjointSubmodule]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  show octDotForm (T x) y = octDotForm x (-(T y)) ↔ _
  rw [map_neg]
  rfl

/-- Conjugation by `planeRot z` (inverse `planeRot (star z)` for unit `z`). -/
def adRot (z : Fin 4 → ℂ) : Module.End ℝ (Module.End ℝ Octonion) :=
  LinearMap.mulLeft ℝ (planeRot z) ∘ₗ LinearMap.mulRight ℝ (planeRot (star z))

theorem adRot_apply (z : Fin 4 → ℂ) (B : Module.End ℝ Octonion) :
    adRot z B = planeRot z * B * planeRot (star z) := by
  rw [adRot, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, mul_assoc]

/-- The root value `z_r z_s^{±1}` (`z_s^{-1} = star z_s` for unit `z`). -/
def rootValue (z : Fin 4 → ℂ) (α : PosRoot) : ℂ :=
  z α.r * (if α.plus then z α.s else star (z α.s))

theorem adRot_neg (z : Fin 4 → ℂ) : adRot (-z) = adRot z := by
  refine LinearMap.ext fun B => ?_
  refine LinearMap.ext fun x => ?_
  simp only [adRot_apply, star_neg, planeRot_neg, Module.End.mul_apply, LinearMap.neg_apply,
    map_neg, neg_neg]

theorem adRot_comm (z w : Fin 4 → ℂ) : adRot z * adRot w = adRot w * adRot z := by
  refine LinearMap.ext fun B => ?_
  have key : ∀ a b : Fin 4 → ℂ, planeRot a * (planeRot b * B * planeRot (star b)) * planeRot (star a) =
      planeRot (a * b) * B * planeRot (star b * star a) := by
    intro a b
    rw [← planeRot_mul, ← planeRot_mul]
    simp only [mul_assoc]
  rw [Module.End.mul_apply, Module.End.mul_apply, adRot_apply, adRot_apply, adRot_apply,
    adRot_apply, key, key, mul_comm z w, mul_comm (star w)]

theorem adRot_mul_apply {z : Fin 4 → ℂ} (hz : ∀ r, Complex.normSq (z r) = 1) (B B' : Module.End ℝ Octonion) :
    adRot z (B * B') = adRot z B * adRot z B' := by
  rw [adRot_apply, adRot_apply, adRot_apply]
  simp only [mul_assoc]
  rw [← mul_assoc (planeRot (star z)) (planeRot z), planeRot_star_mul hz, one_mul]

theorem adRot_mem_skewEnd {z : Fin 4 → ℂ} (hz : ∀ r, Complex.normSq (z r) = 1)
    {B : Module.End ℝ Octonion} (hB : B ∈ skewEnd) : adRot z B ∈ skewEnd := by
  rw [mem_skewEnd_iff'] at hB ⊢
  intro x y
  have hadj : ∀ u w, octDot (planeRot (star z) u) w = octDot u (planeRot z w) := fun u w => by
    rw [octDot_comm, octDot_planeRot_star hz, octDot_comm]
  rw [adRot_apply, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply,
    Module.End.mul_apply, ← octDot_planeRot_star hz, hB, hadj]

theorem adRot_cartanGen {z : Fin 4 → ℂ} (hz : ∀ r, Complex.normSq (z r) = 1) (q : Fin 4) :
    adRot z (cartanGen q) = cartanGen q := by
  have h : (z q).re * (z q).re + (z q).im * (z q).im = 1 := by
    rw [← Complex.normSq_apply]; exact hz q
  rw [adRot_apply, cartanGen, planeRot_wedge hz, planeRot_planeSnd', planeRot_planeFst, wedge_lin,
    wedge_self, wedge_self, wedge_swap (octBasis (planeFst q))]
  calc _ = ((z q).re * (z q).re + (z q).im * (z q).im) •
        wedge (octBasis (planeSnd q)) (octBasis (planeFst q)) := by module
    _ = _ := by rw [h, one_smul]

theorem adRot_rootX {z : Fin 4 → ℂ} (hz : ∀ r, Complex.normSq (z r) = 1) (α : PosRoot) :
    adRot z (rootX α) = (rootValue z α).re • rootX α + (rootValue z α).im • rootY α := by
  obtain ⟨⟨r, s, p⟩, hrs⟩ := α
  cases p
  · simp only [rootX, rootY, rootValue, PosRoot.plus, PosRoot.r, PosRoot.s, Bool.false_eq_true,
      ite_false, adRot_apply, add_mul, mul_add, planeRot_wedge hz, planeRot_planeFst, planeRot_planeSnd',
      wedge_lin, Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im]
    module
  · simp only [rootX, rootY, rootValue, PosRoot.plus, PosRoot.r, PosRoot.s, ite_true, adRot_apply,
      sub_mul, mul_sub, planeRot_wedge hz, planeRot_planeFst, planeRot_planeSnd',
      wedge_lin, Complex.mul_re, Complex.mul_im]
    module

theorem adRot_rootY {z : Fin 4 → ℂ} (hz : ∀ r, Complex.normSq (z r) = 1) (α : PosRoot) :
    adRot z (rootY α) = -((rootValue z α).im • rootX α) + (rootValue z α).re • rootY α := by
  obtain ⟨⟨r, s, p⟩, hrs⟩ := α
  cases p
  · simp only [rootX, rootY, rootValue, PosRoot.plus, PosRoot.r, PosRoot.s, Bool.false_eq_true,
      ite_false, adRot_apply, mul_sub, sub_mul, planeRot_wedge hz, planeRot_planeFst, planeRot_planeSnd',
      wedge_lin, Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
      Complex.conj_im]
    module
  · simp only [rootX, rootY, rootValue, PosRoot.plus, PosRoot.r, PosRoot.s, ite_true, adRot_apply,
      add_mul, mul_add, planeRot_wedge hz, planeRot_planeFst, planeRot_planeSnd',
      wedge_lin, Complex.mul_re, Complex.mul_im]
    module

theorem adRot_star_adRot {z : Fin 4 → ℂ} (hz : ∀ r, Complex.normSq (z r) = 1)
    (B : Module.End ℝ Octonion) : adRot (star z) (adRot z B) = B := by
  rw [adRot_apply, adRot_apply, star_star]
  simp only [mul_assoc]
  rw [← mul_assoc (planeRot (star z)) (planeRot z), planeRot_star_mul hz, one_mul, mul_one]

theorem adRot_adRot_star {z : Fin 4 → ℂ} (hz : ∀ r, Complex.normSq (z r) = 1)
    (B : Module.End ℝ Octonion) : adRot z (adRot (star z) B) = B := by
  have := adRot_star_adRot (normSq_star_eq_one hz) B
  rwa [star_star] at this

/-- Conjugation by a unit plane rotation, as a Lie automorphism of the skew endomorphisms. -/
def adRotEquiv (z : Fin 4 → ℂ) (hz : ∀ r, Complex.normSq (z r) = 1) : skewEnd ≃ₗ⁅ℝ⁆ skewEnd where
  toFun B := ⟨adRot z B, adRot_mem_skewEnd hz B.2⟩
  map_add' B B' := Subtype.ext (map_add (adRot z) (B : Module.End ℝ Octonion) B')
  map_smul' c B := Subtype.ext (map_smul (adRot z) c (B : Module.End ℝ Octonion))
  map_lie' {B B'} := by
    apply Subtype.ext
    simp only [LieSubalgebra.coe_bracket, Ring.lie_def, map_sub, adRot_mul_apply hz]
  invFun B := ⟨adRot (star z) B, adRot_mem_skewEnd (normSq_star_eq_one hz) B.2⟩
  left_inv B := Subtype.ext (adRot_star_adRot hz B)
  right_inv B := Subtype.ext (adRot_adRot_star hz B)

theorem adRotEquiv_apply (z : Fin 4 → ℂ) (hz : ∀ r, Complex.normSq (z r) = 1) (B : skewEnd) :
    ((adRotEquiv z hz B : skewEnd) : Module.End ℝ Octonion) = adRot z B := rfl

/-! ## Coordinates in the root basis -/

/-- The coordinates of `adRot z` in the root basis, given the root values `v`. -/
def rotCoeff (v : PosRoot → ℂ) (c : RootIndex → ℝ) : RootIndex → ℝ
  | .inl q => c (.inl q)
  | .inr (α, false) => (v α).re * c (.inr (α, false)) - (v α).im * c (.inr (α, true))
  | .inr (α, true) => (v α).im * c (.inr (α, false)) + (v α).re * c (.inr (α, true))

theorem sum_rootFamily_split (c : RootIndex → ℝ) :
    ∑ j, c j • rootFamily j = ∑ q, c (.inl q) • cartanGen q +
      ∑ α, (c (.inr (α, false)) • rootX α + c (.inr (α, true)) • rootY α) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, rootFamily]
  congr 1
  exact Finset.sum_congr rfl fun α _ => add_comm _ _

theorem adRot_sum {z : Fin 4 → ℂ} (hz : ∀ r, Complex.normSq (z r) = 1) (c : RootIndex → ℝ) :
    adRot z (∑ j, c j • rootFamily j) = ∑ j, rotCoeff (rootValue z) c j • rootFamily j := by
  rw [sum_rootFamily_split, sum_rootFamily_split, map_add, map_sum, map_sum]
  simp only [map_add, map_smul, adRot_cartanGen hz, adRot_rootX hz, adRot_rootY hz, rotCoeff]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  module

/-- A rotation by a unit complex number other than one fixes no nonzero real 2-vector. -/
theorem rot_fixed_eq_zero {v : ℂ} (hv : v ≠ 1) {a b : ℝ} (h1 : v.re * a - v.im * b = a)
    (h2 : v.im * a + v.re * b = b) : a = 0 ∧ b = 0 := by
  have hd : (v.re - 1) ^ 2 + v.im ^ 2 ≠ 0 := by
    intro h
    apply hv
    apply Complex.ext
    · rw [Complex.one_re]; nlinarith [sq_nonneg (v.re - 1), sq_nonneg v.im]
    · rw [Complex.one_im]; nlinarith [sq_nonneg (v.re - 1), sq_nonneg v.im]
  constructor
  · have h : a * ((v.re - 1) ^ 2 + v.im ^ 2) = 0 := by
      linear_combination (v.re - 1) * h1 + v.im * h2
    exact (mul_eq_zero.mp h).resolve_right hd
  · have h : b * ((v.re - 1) ^ 2 + v.im ^ 2) = 0 := by
      linear_combination (-v.im) * h1 + (v.re - 1) * h2
    exact (mul_eq_zero.mp h).resolve_right hd

/-- **Fixed space of plane-rotation conjugations.** For any finite family of unit tuples, the common
fixed vectors in `skewEnd` are spanned by the Cartan generators and the root vectors of the roots
whose values are all one. -/
theorem fixed_adRot_eq {ι : Type*} [Finite ι] (Z : ι → Fin 4 → ℂ)
    (hZ : ∀ i r, Complex.normSq (Z i r) = 1) :
    (⨅ i, fixedSpace (adRot (Z i))) ⊓ skewEnd.toSubmodule =
      Submodule.span ℝ (Set.range cartanGen ∪
        {B | ∃ α : PosRoot, (∀ i, rootValue (Z i) α = 1) ∧ (B = rootX α ∨ B = rootY α)}) := by
  apply le_antisymm
  · intro B hB
    obtain ⟨hfix, hskew⟩ := Submodule.mem_inf.mp hB
    rw [Submodule.mem_iInf] at hfix
    rw [← span_rootFamily] at hskew
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hskew
    have hcoef : ∀ i j, rotCoeff (rootValue (Z i)) c j = c j := by
      intro i
      have h := mem_fixedSpace.mp (hfix i)
      rw [adRot_sum (hZ i)] at h
      have h0 := Fintype.linearIndependent_iff.mp rootFamily_linearIndependent
        (fun j => rotCoeff (rootValue (Z i)) c j - c j)
        (by simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self])
      exact fun j => sub_eq_zero.mp (h0 j)
    rw [sum_rootFamily_split]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_union_left _ (Set.mem_range_self q))))
      (Submodule.sum_mem _ fun α _ => ?_)
    by_cases hα : ∀ i, rootValue (Z i) α = 1
    · exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span
          (Set.mem_union_right _ (Set.mem_ofPred.mpr ⟨α, hα, Or.inl rfl⟩))))
        (Submodule.smul_mem _ _ (Submodule.subset_span
          (Set.mem_union_right _ (Set.mem_ofPred.mpr ⟨α, hα, Or.inr rfl⟩))))
    · obtain ⟨i, hi⟩ := not_forall.mp hα
      obtain ⟨h1, h2⟩ := rot_fixed_eq_zero hi (hcoef i (.inr (α, false))) (hcoef i (.inr (α, true)))
      rw [h1, h2, zero_smul, zero_smul, add_zero]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro B (⟨q, rfl⟩ | ⟨α, hα, rfl | rfl⟩)
    · refine Submodule.mem_inf.mpr ⟨Submodule.mem_iInf _ |>.mpr fun i => ?_, cartanGen_mem q⟩
      exact mem_fixedSpace.mpr (adRot_cartanGen (hZ i) q)
    · refine Submodule.mem_inf.mpr ⟨Submodule.mem_iInf _ |>.mpr fun i => ?_, rootX_mem α⟩
      rw [mem_fixedSpace, adRot_rootX (hZ i), hα i, Complex.one_re, Complex.one_im, one_smul,
        zero_smul, add_zero]
    · refine Submodule.mem_inf.mpr ⟨Submodule.mem_iInf _ |>.mpr fun i => ?_, rootY_mem α⟩
      rw [mem_fixedSpace, adRot_rootY (hZ i), hα i, Complex.one_re, Complex.one_im, one_smul,
        zero_smul, neg_zero, zero_add]

theorem finrank_fixed_adRot {ι : Type*} [Finite ι] (Z : ι → Fin 4 → ℂ)
    (hZ : ∀ i r, Complex.normSq (Z i r) = 1) :
    Module.finrank ℝ ↥((⨅ i, fixedSpace (adRot (Z i))) ⊓ skewEnd.toSubmodule) =
      4 + 2 * Nat.card {α : PosRoot // ∀ i, rootValue (Z i) α = 1} := by
  classical
  set G := {α : PosRoot // ∀ i, rootValue (Z i) α = 1}
  set g : Fin 4 ⊕ (G × Bool) → RootIndex := Sum.map id (Prod.map Subtype.val id) with hg
  have hinj : Function.Injective g :=
    Function.injective_id.sumMap (Subtype.val_injective.prodMap Function.injective_id)
  have hli : LinearIndependent ℝ (rootFamily ∘ g) := rootFamily_linearIndependent.comp g hinj
  have hset : Set.range cartanGen ∪
      {B | ∃ α : PosRoot, (∀ i, rootValue (Z i) α = 1) ∧ (B = rootX α ∨ B = rootY α)} =
      Set.range (rootFamily ∘ g) := by
    ext B
    constructor
    · rintro (⟨q, rfl⟩ | ⟨α, hα, rfl | rfl⟩)
      · exact ⟨.inl q, rfl⟩
      · exact ⟨.inr (⟨α, hα⟩, false), rfl⟩
      · exact ⟨.inr (⟨α, hα⟩, true), rfl⟩
    · rintro ⟨(q | ⟨α, (_ | _)⟩), rfl⟩
      · exact Or.inl ⟨q, rfl⟩
      · exact Or.inr ⟨α.1, α.2, Or.inl rfl⟩
      · exact Or.inr ⟨α.1, α.2, Or.inr rfl⟩
  rw [fixed_adRot_eq Z hZ, hset, finrank_span_eq_card hli, Nat.card_eq_fintype_card,
    Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm]

#print axioms planeRot_planeFst
#print axioms planeRot_planeSnd
#print axioms planeRot_mul
#print axioms planeRot_one
#print axioms planeRot_octDot
#print axioms adRot_apply
#print axioms adRot_neg
#print axioms adRot_comm
#print axioms adRot_mul_apply
#print axioms adRot_mem_skewEnd
#print axioms adRot_cartanGen
#print axioms adRot_rootX
#print axioms adRot_rootY
#print axioms adRotEquiv
#print axioms adRotEquiv_apply
#print axioms fixed_adRot_eq
#print axioms finrank_fixed_adRot

end CKM.NativeIntrinsicTriality

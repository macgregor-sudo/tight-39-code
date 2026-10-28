module

public import GSAnalytic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Projection

@[expose] public section

/-!
# The automorphism group of a finite-dimensional algebra near the identity

Mathlib-only module. `V` is a finite-dimensional real normed space with a continuous bilinear
product `m` (no associativity, commutativity or unit is assumed).

* `autOf m`: **all** bijective continuous linear maps preserving `m`.
* `derOf m`: all continuous linear maps obeying the Leibniz law for `m`.
* `expChart m : derOf m → (V →L[ℝ] V)`, `D ↦ exp D`: analytic, with derivative the inclusion at
  `0`, and values in `autOf m`.
* `exists_expChart_local`: there are open neighbourhoods `U ∋ 0` in `derOf m` and `W ∋ 1` in
  `V →L[ℝ] V` with `expChart m` injective on `U`, `expChart m '' U = autOf m ∩ W` (the image is the
  **full** automorphism set near the identity, not a chosen family), and an inverse chart `inv`
  analytic on `W`.

Route (MASTER §6.8, streamlined). Let `C` be a complement of `derOf m` (`Submodule.exists_isCompl`)
and `Ψ (D, c) = exp D * (1 + c)` on `derOf m × C`. Its strict derivative at `0` is
`(D, c) ↦ D + c`, invertible since `derOf m ⊕ C = V →L[ℝ] V`; take its `OpenPartialHomeomorph`
and analytic inverse (`analyticAt_toOpenPartialHomeomorph_symm`). If `g = Ψ (D, c)` is an
automorphism then so is `exp (-D) * g = 1 + c`, and `1 + c` preserving `m` reads
`L c = m (c ·) (c ·)` with `L c = c ∘ m - m (c ·) · - m · (c ·)` (the derivation defect). `L` is
injective on `C` (its kernel is `derOf m`), hence bounded below by some `κ > 0` (finite dimension),
while the right side is `≤ ‖m‖ ‖c‖²`; so `c = 0` once `‖c‖ < κ / ‖m‖`. Hence `g = exp D`.
-/

noncomputable section

namespace CKM.NativeGroupSlice

open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- All bijective continuous linear maps preserving the product `m`. -/
def autOf (m : V →L[ℝ] V →L[ℝ] V) : Set (V →L[ℝ] V) :=
  {A | Function.Bijective A ∧ ∀ a b, A (m a b) = m (A a) (A b)}

/-- All continuous linear maps obeying the Leibniz law for `m`. -/
def derOf (m : V →L[ℝ] V →L[ℝ] V) : Submodule ℝ (V →L[ℝ] V) where
  carrier := {D | IsDerivationOf m D}
  add_mem' := by
    intro D E hD hE a b
    have h1 : D (m a b) = m (D a) b + m a (D b) := hD a b
    have h2 : E (m a b) = m (E a) b + m a (E b) := hE a b
    simp only [add_apply, h1, h2, map_add]
    abel
  zero_mem' := by
    intro a b
    simp
  smul_mem' := by
    intro c D hD a b
    have h1 : D (m a b) = m (D a) b + m a (D b) := hD a b
    simp only [smul_apply, h1, map_smul, smul_add]

theorem mem_derOf {m : V →L[ℝ] V →L[ℝ] V} {D : V →L[ℝ] V} : D ∈ derOf m ↔ IsDerivationOf m D :=
  Iff.rfl

/-- The exponential chart `D ↦ exp D` on the derivations. -/
def expChart (m : V →L[ℝ] V →L[ℝ] V) (D : derOf m) : V →L[ℝ] V :=
  NormedSpace.exp (D : V →L[ℝ] V)

variable [FiniteDimensional ℝ V]

theorem expChart_zero (m : V →L[ℝ] V →L[ℝ] V) : expChart m 0 = 1 := by
  simp [expChart, NormedSpace.exp_zero]

theorem expChart_mem_autOf (m : V →L[ℝ] V →L[ℝ] V) (D : derOf m) : expChart m D ∈ autOf m := by
  refine ⟨Function.bijective_iff_has_inverse.2 ⟨⇑(NormedSpace.exp (-(D : V →L[ℝ] V))), ?_, ?_⟩,
    exp_map_bilinear m D.2⟩
  · intro x
    have h := congrArg (fun T : V →L[ℝ] V => T x) (exp_neg_mul_exp (D : V →L[ℝ] V))
    simpa [expChart] using h
  · intro x
    have h := congrArg (fun T : V →L[ℝ] V => T x) (exp_mul_exp_neg (D : V →L[ℝ] V))
    simpa [expChart] using h

theorem analyticAt_expChart (m : V →L[ℝ] V →L[ℝ] V) (D : derOf m) : AnalyticAt ℝ (expChart m) D := by
  have h : AnalyticAt ℝ (NormedSpace.exp ∘ (derOf m).subtypeL) D :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) ((derOf m).subtypeL D)).comp
      (ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := derOf m) (F := V →L[ℝ] V)
        (derOf m).subtypeL D)
  exact h

/-- The tangent of the chart at the identity is the inclusion of the derivations. -/
theorem hasStrictFDerivAt_expChart (m : V →L[ℝ] V →L[ℝ] V) :
    HasStrictFDerivAt (expChart m) (derOf m).subtypeL 0 := by
  have h0 : (derOf m).subtypeL (0 : derOf m) = 0 := map_zero _
  have h := (h0 ▸ hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := V →L[ℝ] V)).comp (0 : derOf m)
    (derOf m).subtypeL.hasStrictFDerivAt
  exact h.congr_fderiv (by ext; simp)

theorem one_mem_autOf (m : V →L[ℝ] V →L[ℝ] V) : (1 : V →L[ℝ] V) ∈ autOf m := by
  refine ⟨?_, fun a b => rfl⟩
  exact Function.bijective_id

theorem mul_mem_autOf {m : V →L[ℝ] V →L[ℝ] V} {A B : V →L[ℝ] V} (hA : A ∈ autOf m)
    (hB : B ∈ autOf m) : A * B ∈ autOf m := by
  refine ⟨hA.1.comp hB.1, fun a b => ?_⟩
  simp only [mul_apply_eq_comp, hB.2, hA.2]

/-- A bijective continuous linear map of a finite-dimensional space is a unit. -/
theorem autChart_isUnit_of_bijective {A : V →L[ℝ] V} (hA : Function.Bijective A) : IsUnit A := by
  let e : V ≃L[ℝ] V := (LinearEquiv.ofBijective (A : V →ₗ[ℝ] V) hA).toContinuousLinearEquiv
  refine isUnit_iff_exists.2 ⟨(e.symm : V →L[ℝ] V), ?_, ?_⟩
  · ext x
    exact e.apply_symm_apply x
  · ext x
    exact e.symm_apply_apply x

theorem inverse_mem_autOf {m : V →L[ℝ] V →L[ℝ] V} {A : V →L[ℝ] V} (hA : A ∈ autOf m) :
    Ring.inverse A ∈ autOf m := by
  have hu := autChart_isUnit_of_bijective hA.1
  have h1 : ∀ x, A (Ring.inverse A x) = x := fun x => by
    simpa using congrArg (fun T : V →L[ℝ] V => T x) (Ring.mul_inverse_cancel A hu)
  have h2 : ∀ x, Ring.inverse A (A x) = x := fun x => by
    simpa using congrArg (fun T : V →L[ℝ] V => T x) (Ring.inverse_mul_cancel A hu)
  refine ⟨Function.bijective_iff_has_inverse.2 ⟨A, h1, h2⟩, fun a b => hA.1.1 ?_⟩
  rw [h1, hA.2, h1, h1]

theorem mul_inverse_of_mem_autOf {m : V →L[ℝ] V →L[ℝ] V} {A : V →L[ℝ] V} (hA : A ∈ autOf m) :
    A * Ring.inverse A = 1 ∧ Ring.inverse A * A = 1 := by
  exact ⟨Ring.mul_inverse_cancel A (autChart_isUnit_of_bijective hA.1),
    Ring.inverse_mul_cancel A (autChart_isUnit_of_bijective hA.1)⟩

/-- The derivation defect `L c = c ∘ m - m (c ·) · - m · (c ·)`. -/
def autChart_defect (m : V →L[ℝ] V →L[ℝ] V) : (V →L[ℝ] V) →ₗ[ℝ] (V →L[ℝ] V →L[ℝ] V) where
  toFun c := (ContinuousLinearMap.compL ℝ V V V c).comp m - m.comp c
    - ((ContinuousLinearMap.compL ℝ V V V).flip c).comp m
  map_add' c d := by
    ext a b
    simp
    abel
  map_smul' r c := by
    ext a b
    simp [smul_sub]

omit [FiniteDimensional ℝ V] in
theorem autChart_defect_apply (m : V →L[ℝ] V →L[ℝ] V) (c : V →L[ℝ] V) (a b : V) :
    autChart_defect m c a b = c (m a b) - m (c a) b - m a (c b) := by
  simp [autChart_defect]

omit [FiniteDimensional ℝ V] in
theorem autChart_defect_eq_zero_iff {m : V →L[ℝ] V →L[ℝ] V} {c : V →L[ℝ] V} :
    autChart_defect m c = 0 ↔ c ∈ derOf m := by
  constructor
  · intro h a b
    have h' := congrArg (fun T : V →L[ℝ] V →L[ℝ] V => T a b) h
    simp only [autChart_defect_apply, zero_apply] at h'
    rw [sub_sub, sub_eq_zero] at h'
    exact h'
  · intro h
    ext a b
    have h1 : c (m a b) = m (c a) b + m a (c b) := mem_derOf.1 h a b
    rw [autChart_defect_apply, h1]
    simp

omit [FiniteDimensional ℝ V] in
/-- If `1 + c` is an automorphism, the defect of `c` is quadratic in `c`. -/
theorem autChart_norm_defect_le {m : V →L[ℝ] V →L[ℝ] V} {c : V →L[ℝ] V}
    (h : 1 + c ∈ autOf m) : ‖autChart_defect m c‖ ≤ ‖m‖ * ‖c‖ ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun a b => ?_
  have H := h.2 a b
  simp only [add_apply, one_apply_eq_self, map_add] at H
  have H' : autChart_defect m c a b = m (c a) (c b) := by
    rw [autChart_defect_apply]
    have H2 := congrArg (fun t => t - m a b) H
    simp only [add_sub_cancel_left] at H2
    rw [H2]
    abel
  rw [H']
  calc ‖m (c a) (c b)‖ ≤ ‖m‖ * ‖c a‖ * ‖c b‖ := m.le_opNorm₂ _ _
    _ ≤ ‖m‖ * (‖c‖ * ‖a‖) * (‖c‖ * ‖b‖) := by
        gcongr
        · exact c.le_opNorm a
        · exact c.le_opNorm b
    _ = ‖m‖ * ‖c‖ ^ 2 * ‖a‖ * ‖b‖ := by ring

/-- On a complement of the derivations, small `c` with `1 + c` an automorphism vanish. -/
theorem autChart_small_complement (m : V →L[ℝ] V →L[ℝ] V) {C : Submodule ℝ (V →L[ℝ] V)}
    (hC : IsCompl (derOf m) C) :
    ∃ r > 0, ∀ c : C, ‖(c : V →L[ℝ] V)‖ < r → 1 + (c : V →L[ℝ] V) ∈ autOf m →
      (c : V →L[ℝ] V) = 0 := by
  have hker : LinearMap.ker ((autChart_defect m).comp C.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    have hD : (c : V →L[ℝ] V) ∈ derOf m := autChart_defect_eq_zero_iff.1 hc
    exact Subtype.ext (Submodule.disjoint_def.1 hC.disjoint _ hD c.2)
  obtain ⟨K, -, hK⟩ := LinearMap.exists_antilipschitzWith (𝕜 := ℝ) (E := C)
    (F := V →L[ℝ] V →L[ℝ] V) ((autChart_defect m).comp C.subtype) hker
  set k : ℝ := (K : ℝ) * ‖m‖ with hk
  have hk0 : 0 ≤ k := by positivity
  refine ⟨1 / (k + 1), by positivity, fun c hcr hc1 => ?_⟩
  have hb := ZeroHomClass.bound_of_antilipschitz ((autChart_defect m).comp C.subtype) hK c
  have hq : ‖((autChart_defect m).comp C.subtype) c‖ ≤ ‖m‖ * ‖(c : V →L[ℝ] V)‖ ^ 2 :=
    autChart_norm_defect_le hc1
  have hx : ‖(c : V →L[ℝ] V)‖ ≤ k * ‖(c : V →L[ℝ] V)‖ ^ 2 := by
    have : ‖c‖ = ‖(c : V →L[ℝ] V)‖ := rfl
    rw [this] at hb
    calc ‖(c : V →L[ℝ] V)‖ ≤ K * (‖m‖ * ‖(c : V →L[ℝ] V)‖ ^ 2) :=
          hb.trans (mul_le_mul_of_nonneg_left hq K.2)
      _ = k * ‖(c : V →L[ℝ] V)‖ ^ 2 := by rw [hk]; ring
  set x := ‖(c : V →L[ℝ] V)‖ with hxdef
  have hx0 : 0 ≤ x := norm_nonneg _
  have hkx : k * x < 1 := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < k + 1)).1 hcr
    nlinarith
  have hx00 : x = 0 := by
    by_contra hne
    have hpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hne)
    have : k * x * x < x := mul_lt_of_lt_one_left hpos hkx
    nlinarith
  exact norm_eq_zero.1 hx00

/-- The product chart `Ψ (D, c) = exp D * (1 + c)` on `derOf m × C`. -/
def autChart_psi (m : V →L[ℝ] V →L[ℝ] V) (C : Submodule ℝ (V →L[ℝ] V)) (p : derOf m × C) :
    V →L[ℝ] V :=
  NormedSpace.exp (p.1 : V →L[ℝ] V) * (1 + (p.2 : V →L[ℝ] V))

omit [FiniteDimensional ℝ V] in
theorem autChart_psi_D0 (m : V →L[ℝ] V →L[ℝ] V) (C : Submodule ℝ (V →L[ℝ] V)) (D : derOf m) :
    autChart_psi m C (D, 0) = expChart m D := by
  simp [autChart_psi, expChart]

omit [FiniteDimensional ℝ V] in
theorem autChart_psi_zero (m : V →L[ℝ] V →L[ℝ] V) (C : Submodule ℝ (V →L[ℝ] V)) :
    autChart_psi m C 0 = 1 := by
  simp [autChart_psi, NormedSpace.exp_zero]

/-- Generic wrapper: a linear equivalence of finite-dimensional spaces as a `≃L[ℝ]`. -/
def autChart_toCLE {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (e : E ≃ₗ[ℝ] F) :
    E ≃L[ℝ] F :=
  e.toContinuousLinearEquiv

omit [FiniteDimensional ℝ V] in
theorem autChart_toCLE_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃ₗ[ℝ] F) (x : E) : autChart_toCLE e x = e x := rfl

/-- The linear isomorphism `(D, c) ↦ D + c`. -/
def autChart_sumCLE (m : V →L[ℝ] V →L[ℝ] V) {C : Submodule ℝ (V →L[ℝ] V)}
    (hC : IsCompl (derOf m) C) : (derOf m × C) ≃L[ℝ] (V →L[ℝ] V) :=
  autChart_toCLE (E := derOf m × C) (F := V →L[ℝ] V)
    (Submodule.prodEquivOfIsCompl (derOf m) C hC)

theorem autChart_sumCLE_apply (m : V →L[ℝ] V →L[ℝ] V) {C : Submodule ℝ (V →L[ℝ] V)}
    (hC : IsCompl (derOf m) C) (p : derOf m × C) :
    autChart_sumCLE m hC p = (p.1 : V →L[ℝ] V) + (p.2 : V →L[ℝ] V) := rfl

/-- First-factor inclusion `derOf m × C → V →L[ℝ] V`. -/
def autChart_i1 (m : V →L[ℝ] V →L[ℝ] V) (C : Submodule ℝ (V →L[ℝ] V)) :
    (derOf m × C) →L[ℝ] (V →L[ℝ] V) :=
  (derOf m).subtypeL.comp (ContinuousLinearMap.fst ℝ (derOf m) C)

/-- Second-factor inclusion `derOf m × C → V →L[ℝ] V`. -/
def autChart_i2 (m : V →L[ℝ] V →L[ℝ] V) (C : Submodule ℝ (V →L[ℝ] V)) :
    (derOf m × C) →L[ℝ] (V →L[ℝ] V) :=
  C.subtypeL.comp (ContinuousLinearMap.snd ℝ (derOf m) C)

omit [FiniteDimensional ℝ V] in
theorem autChart_i1_apply (m : V →L[ℝ] V →L[ℝ] V) (C : Submodule ℝ (V →L[ℝ] V))
    (p : derOf m × C) : autChart_i1 m C p = (p.1 : V →L[ℝ] V) := rfl

omit [FiniteDimensional ℝ V] in
theorem autChart_i2_apply (m : V →L[ℝ] V →L[ℝ] V) (C : Submodule ℝ (V →L[ℝ] V))
    (p : derOf m × C) : autChart_i2 m C p = (p.2 : V →L[ℝ] V) := rfl

theorem autChart_psi_analyticAt (m : V →L[ℝ] V →L[ℝ] V) (C : Submodule ℝ (V →L[ℝ] V))
    (p : derOf m × C) : AnalyticAt ℝ (autChart_psi m C) p := by
  have h1 : AnalyticAt ℝ (autChart_i1 m C) p :=
    ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := derOf m × C) (F := V →L[ℝ] V)
      (autChart_i1 m C) p
  have h2 : AnalyticAt ℝ (autChart_i2 m C) p :=
    ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := derOf m × C) (F := V →L[ℝ] V)
      (autChart_i2 m C) p
  have he : AnalyticAt ℝ (fun q : derOf m × C => NormedSpace.exp (autChart_i1 m C q)) p :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) _).comp h1
  exact he.mul ((analyticAt_const (v := (1 : V →L[ℝ] V))).add h2)

theorem autChart_psi_hasStrictFDerivAt (m : V →L[ℝ] V →L[ℝ] V) {C : Submodule ℝ (V →L[ℝ] V)}
    (hC : IsCompl (derOf m) C) :
    HasStrictFDerivAt (autChart_psi m C)
      ((autChart_sumCLE m hC : (derOf m × C) ≃L[ℝ] (V →L[ℝ] V)) :
        (derOf m × C) →L[ℝ] (V →L[ℝ] V)) 0 := by
  set i1 := autChart_i1 m C
  set i2 := autChart_i2 m C
  have h0 : i1 0 = 0 := map_zero _
  have ha : HasStrictFDerivAt (fun q : derOf m × C => NormedSpace.exp (i1 q))
      ((1 : (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V)).comp i1) 0 :=
    (h0 ▸ hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := V →L[ℝ] V)).comp
      (0 : derOf m × C) i1.hasStrictFDerivAt
  have hi2 : HasStrictFDerivAt i2 i2 (0 : derOf m × C) := i2.hasStrictFDerivAt
  have hb : HasStrictFDerivAt (fun q : derOf m × C => (1 : V →L[ℝ] V) + i2 q) i2 0 :=
    HasStrictFDerivAt.const_add (𝕜 := ℝ) (E := derOf m × C) (F := V →L[ℝ] V)
      (1 : V →L[ℝ] V) hi2
  have h := HasStrictFDerivAt.fun_mul' (𝕜 := ℝ) (E := derOf m × C) (𝔸 := V →L[ℝ] V) ha hb
  have hfun : (fun q : derOf m × C => NormedSpace.exp (i1 q) * (1 + i2 q)) = autChart_psi m C :=
    funext fun q => by rw [autChart_i1_apply, autChart_i2_apply]; rfl
  rw [hfun] at h
  have hd : NormedSpace.exp (i1 0) • i2 + MulOpposite.op ((1 : V →L[ℝ] V) + i2 0) •
      (1 : (V →L[ℝ] V) →L[ℝ] (V →L[ℝ] V)).comp i1 =
      ((autChart_sumCLE m hC : (derOf m × C) ≃L[ℝ] (V →L[ℝ] V)) :
        (derOf m × C) →L[ℝ] (V →L[ℝ] V)) := by
    have hz : i2 0 = 0 := map_zero _
    rw [h0, hz, NormedSpace.exp_zero, add_zero]
    refine ContinuousLinearMap.ext fun p => ?_
    rw [ContinuousLinearEquiv.coe_coe, autChart_sumCLE_apply, add_apply,
      smul_apply, smul_apply,
      ContinuousLinearMap.comp_apply, one_apply_eq_self, autChart_i1_apply,
      autChart_i2_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
      one_mul, mul_one, add_comm]
  exact h.congr_fderiv hd

/-- Generic wrapper around `HasStrictFDerivAt.toOpenPartialHomeomorph`. -/
def autChart_oph {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (e : E ≃L[ℝ] F) (a : E)
    (hf : HasStrictFDerivAt f (e : E →L[ℝ] F) a) : OpenPartialHomeomorph E F :=
  hf.toOpenPartialHomeomorph f

/-- **Identity chart of the full automorphism group.** Near the identity, the exponential of the
derivations is a homeomorphism onto all of `autOf m`, with an analytic inverse. -/
theorem exists_expChart_local (m : V →L[ℝ] V →L[ℝ] V) :
    ∃ U : Set (derOf m), ∃ W : Set (V →L[ℝ] V), ∃ inv : (V →L[ℝ] V) → derOf m,
      IsOpen U ∧ (0 : derOf m) ∈ U ∧ IsOpen W ∧ (1 : V →L[ℝ] V) ∈ W ∧
      Set.InjOn (expChart m) U ∧ expChart m '' U = autOf m ∩ W ∧
      (∀ g ∈ autOf m ∩ W, inv g ∈ U ∧ expChart m (inv g) = g) ∧
      (∀ D ∈ U, inv (expChart m D) = D) ∧
      AnalyticOnNhd ℝ inv W := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (derOf m)
  obtain ⟨r, hr, hsmall⟩ := autChart_small_complement m hC
  have hΨ := autChart_psi_hasStrictFDerivAt m hC
  set Φ : OpenPartialHomeomorph (derOf m × C) (V →L[ℝ] V) :=
    autChart_oph (autChart_psi m C) (autChart_sumCLE m hC) 0 hΨ with hΦdef
  have hΦ : ⇑Φ = autChart_psi m C := hΨ.toOpenPartialHomeomorph_coe
  have h0s : (0 : derOf m × C) ∈ Φ.source := hΨ.mem_toOpenPartialHomeomorph_source
  have han : AnalyticAt ℝ Φ.symm 1 := by
    have := analyticAt_toOpenPartialHomeomorph_symm hΨ (autChart_psi_analyticAt m C 0)
    rwa [autChart_psi_zero] at this
  obtain ⟨N, hNan, hNo, h1N⟩ := eventually_nhds_iff.1 han.eventually_analyticAt
  have hD0 : ∀ D : derOf m, Φ (D, 0) = expChart m D := fun D => by
    rw [hΦ, autChart_psi_D0]
  set S : Set (derOf m × C) := Φ.source ∩ {p | ‖(p.2 : V →L[ℝ] V)‖ < r} with hSdef
  have hSo : IsOpen S := Φ.open_source.inter
    (isOpen_lt (continuous_norm.comp (continuous_subtype_val.comp continuous_snd))
      continuous_const)
  have hSs : S ⊆ Φ.source := Set.inter_subset_left
  have hcont : Continuous (expChart m) :=
    continuous_iff_continuousAt.2 fun D => (analyticAt_expChart m D).continuousAt
  have hkey : ∀ g ∈ autOf m ∩ (Φ '' S ∩ N), ∃ D : derOf m,
      ((D, 0) : derOf m × C) ∈ S ∧ expChart m D = g := by
    rintro g ⟨hg, ⟨⟨D, c⟩, hpS, rfl⟩, -⟩
    have h1 : expChart m (-D) * Φ (D, c) = 1 + (c : V →L[ℝ] V) := by
      rw [hΦ]
      simp only [autChart_psi, expChart, Submodule.coe_neg]
      rw [← mul_assoc, exp_neg_mul_exp, one_mul]
    have hc1 : 1 + (c : V →L[ℝ] V) ∈ autOf m := h1 ▸ mul_mem_autOf (expChart_mem_autOf m (-D)) hg
    have hc0 : c = 0 := Subtype.ext (hsmall c hpS.2 hc1)
    subst hc0
    exact ⟨D, hpS, (hD0 D).symm⟩
  refine ⟨{D | ((D, 0) : derOf m × C) ∈ S ∧ expChart m D ∈ N}, Φ '' S ∩ N,
    fun g => (Φ.symm g).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hSo.preimage (continuous_id.prodMk continuous_const)).inter (hNo.preimage hcont)
  · refine ⟨?_, ?_⟩
    · simpa using hSdef ▸ (⟨h0s, by simpa using hr⟩ : (0 : derOf m × C) ∈ S)
    · rw [expChart_zero]; exact h1N
  · exact (Φ.isOpen_image_of_subset_source hSo hSs).inter hNo
  · refine ⟨⟨0, ⟨h0s, by simpa using hr⟩, ?_⟩, h1N⟩
    rw [hΦ, autChart_psi_zero]
  · intro D1 hD1 D2 hD2 heq
    have h12 : Φ (D1, 0) = Φ (D2, 0) := by rw [hD0, hD0]; exact heq
    exact (Prod.ext_iff.1 (Φ.injOn (hSs hD1.1) (hSs hD2.1) h12)).1
  · ext g
    constructor
    · rintro ⟨D, hD, rfl⟩
      exact ⟨expChart_mem_autOf m D, ⟨(D, 0), hD.1, hD0 D⟩, hD.2⟩
    · intro hg
      obtain ⟨D, hDS, rfl⟩ := hkey g hg
      exact ⟨D, ⟨hDS, hg.2.2⟩, rfl⟩
  · intro g hg
    obtain ⟨D, hDS, rfl⟩ := hkey g hg
    have hs : Φ.symm (expChart m D) = (D, 0) := by
      rw [← hD0]; exact Φ.left_inv (hSs hDS)
    simp only [hs]
    exact ⟨⟨hDS, hg.2.2⟩, trivial⟩
  · intro D hD
    have hs : Φ.symm (expChart m D) = (D, 0) := by
      rw [← hD0]; exact Φ.left_inv (hSs hD.1)
    simp only [hs]
  · intro g hg
    exact (ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := derOf m × C) (F := derOf m)
      (ContinuousLinearMap.fst ℝ (derOf m) C) _).comp (hNan g hg.2)

end CKM.NativeGroupSlice

#print axioms CKM.NativeGroupSlice.mem_derOf
#print axioms CKM.NativeGroupSlice.expChart_zero
#print axioms CKM.NativeGroupSlice.expChart_mem_autOf
#print axioms CKM.NativeGroupSlice.analyticAt_expChart
#print axioms CKM.NativeGroupSlice.hasStrictFDerivAt_expChart
#print axioms CKM.NativeGroupSlice.one_mem_autOf
#print axioms CKM.NativeGroupSlice.mul_mem_autOf
#print axioms CKM.NativeGroupSlice.inverse_mem_autOf
#print axioms CKM.NativeGroupSlice.mul_inverse_of_mem_autOf
#print axioms CKM.NativeGroupSlice.exists_expChart_local

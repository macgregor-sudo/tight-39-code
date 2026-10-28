module

public import A4KRep

@[expose] public section

/-!
# Classification of finite-dimensional real `C₃ × C₃` representations by fixed dimensions

A finite-dimensional real `K`-representation whose `K`-fixed space has dimension `m` and whose
`H`-fixed spaces have dimensions `m + 2 n_H` is `K`-equivariantly isomorphic to the standard model
`ℝ^m_triv ⊕ ⨁_H V_H^(n_H)`.

Intended route: the averaging projections `P_K = (1/9) Σ g0^i g1^j` and `P_H = (1/3)(1 + h + h²)`
(`h = gen H`) are commuting equivariant idempotents; `V = V^K ⊕ ⨁_H W_H` with
`W_H = range (P_H - P_K)`. On `W_H` an element `k ∉ H` satisfies `k² + k + 1 = 0`, so
`J = (2k + 1)/√3` is an equivariant complex structure; a complex basis of `(W_H, J)` gives `n_H`
copies of `V_H` (the action of `g0, g1` on `W_H` is `ω^a, ω^b` for `kChar H = (a, b)` in that
complex structure, after choosing `k` and the sign of `J` to match). The `V^K` part is trivial.
-/

noncomputable section

namespace CKM.NativeIntrinsicTriality

namespace KClassify

theorem omega_re' : ω.re = -1 / 2 := by
  simp [ω, UnitaryErrorBases.ThreeCycleFourier.omega]

theorem omega_im' : ω.im = Real.sqrt 3 / 2 := by
  simp [ω, UnitaryErrorBases.ThreeCycleFourier.omega]

/-! ### Complex structures from an element with `k² + k + 1 = 0` -/

section CxStr
variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- The ring hom `ℂ → End W` attached to a complex structure `J`. -/
def cxHom (J : Module.End ℝ W) (hJ : ∀ w, J (J w) = -w) : ℂ →+* Module.End ℝ W where
  toFun z := z.re • 1 + z.im • J
  map_one' := by simp
  map_mul' z z' := by
    ext w
    simp only [Complex.mul_re, Complex.mul_im, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, Module.End.mul_apply, map_add, map_smul, hJ]
    module
  map_zero' := by simp
  map_add' z z' := by
    simp only [Complex.add_re, Complex.add_im, add_smul]
    abel

/-- A finite-dimensional real space with `k² + k + 1 = 0` is `n` copies of `ℂ` with `k ↦ ω`. -/
theorem cx_exists_equiv [FiniteDimensional ℝ W] (k : Module.End ℝ W)
    (hk : ∀ w, k (k w) + k w + w = 0) (n : ℕ) (hn : Module.finrank ℝ W = 2 * n) :
    ∃ e : W ≃ₗ[ℝ] (Fin n → ℂ), ∀ w, e (k w) = ω • e w := by
  set s : ℝ := Real.sqrt 3 with hs
  have hs2 : s * s = 3 := Real.mul_self_sqrt (by norm_num)
  have hs0 : s ≠ 0 := by positivity
  let J : Module.End ℝ W := (s⁻¹ * 2) • k + s⁻¹ • 1
  have hJ : ∀ w, J (J w) = -w := by
    intro w
    have h := hk w
    simp only [J, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add,
      map_smul]
    have hinv : s⁻¹ * s⁻¹ = (1/3 : ℝ) := by
      rw [← mul_inv, hs2]; norm_num
    linear_combination (norm := match_scalars) (4 * s⁻¹ * s⁻¹) • h
    all_goals linarith [hinv]
  let _ : Module ℂ W := Module.compHom W (cxHom J hJ)
  have hsmul : ∀ (z : ℂ) (w : W), z • w = z.re • w + z.im • J w := fun _ _ => rfl
  have : IsScalarTower ℝ ℂ W := ⟨fun r z w => by
    simp only [hsmul, Complex.smul_re, Complex.smul_im, smul_eq_mul, smul_add, mul_smul]⟩
  have : FiniteDimensional ℂ W := Module.Finite.of_restrictScalars_finite ℝ ℂ W
  have hC : Module.finrank ℂ W = n := by
    have := Module.finrank_mul_finrank ℝ ℂ W
    rw [Module.finrank_eq_card_basis Complex.basisOneI, Fintype.card_fin, hn] at this
    omega
  let b := Module.finBasisOfFinrankEq ℂ W hC
  let e : W ≃ₗ[ℝ] (Fin n → ℂ) := b.equivFun.restrictScalars ℝ
  refine ⟨e, fun w => ?_⟩
  have hkw : k w = ω • w := by
    rw [hsmul, omega_re', omega_im', ← hs]
    simp only [J, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, smul_add,
      smul_smul]
    have h1 : s / 2 * (s⁻¹ * 2) = 1 := by field_simp
    have h2 : s / 2 * s⁻¹ = 1 / 2 := by field_simp
    rw [h1, h2]
    module
  show b.equivFun (k w) = ω • b.equivFun w
  rw [hkw, map_smul]

/-- Powers of `k` act by powers of `ω`. -/
theorem cx_equiv_pow {n : ℕ} (k : Module.End ℝ W) (e : W ≃ₗ[ℝ] (Fin n → ℂ))
    (he : ∀ w, e (k w) = ω • e w) (j : ℕ) (w : W) : e ((k ^ j) w) = ω ^ j • e w := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', Module.End.mul_apply, he, ih, smul_smul, pow_succ']

end CxStr

/-! ### Polynomial identities in `ℝ[C₃ × C₃]` -/

section PolyDefs
variable {R : Type*} [Ring R]

/-- Generators of the four subgroups, as ring elements. -/
def genE (a b : R) : Fin 4 → R
  | 0 => a
  | 1 => b
  | 2 => a ^ 2 * b ^ 2
  | 3 => a ^ 2 * b

/-- An element outside each subgroup, with character value `1`. -/
def kE (a b : R) : Fin 4 → R
  | 0 => b ^ 2
  | 1 => a
  | 2 => b
  | 3 => a

/-- Exponents of the first generator. -/
def e0 : Fin 4 → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 1

/-- Exponents of the second generator. -/
def e1 : Fin 4 → ℕ
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 1

/-- Nine times the `K`-average. -/
def avgT (a b : R) : R := (1 + a + a ^ 2) * (1 + b + b ^ 2)

/-- Nine times the projection onto the `H`-isotypic nontrivial part. -/
def avgQ (a b : R) (H : Fin 4) : R := 3 * (1 + genE a b H + genE a b H ^ 2) - avgT a b

theorem e0_eq (H : Fin 4) : (kChar H).1.val = e0 H := by
  fin_cases H <;> rfl

theorem e1_eq (H : Fin 4) : (kChar H).2.val = e1 H := by
  fin_cases H <;> rfl

variable {S : Type*} [Ring S]

theorem map_genE (f : R →+* S) (a b : R) (H : Fin 4) : f (genE a b H) = genE (f a) (f b) H := by
  fin_cases H <;> simp [genE]

theorem map_kE (f : R →+* S) (a b : R) (H : Fin 4) : f (kE a b H) = kE (f a) (f b) H := by
  fin_cases H <;> simp [kE]

theorem map_avgT (f : R →+* S) (a b : R) : f (avgT a b) = avgT (f a) (f b) := by
  simp [avgT]

theorem map_avgQ (f : R →+* S) (a b : R) (H : Fin 4) : f (avgQ a b H) = avgQ (f a) (f b) H := by
  simp [avgQ, map_avgT, map_genE, map_ofNat]

end PolyDefs

section PolyIds
variable {R : Type*} [CommRing R] {a b : R}

/-- The average absorbs `a`. -/
theorem poly_T_mul_a (ha : a ^ 3 = 1) (_hb : b ^ 3 = 1) : avgT a b * a = avgT a b := by
  simp only [avgT]
  linear_combination (b^2 + b + 1) * ha

/-- The average absorbs `b`. -/
theorem poly_T_mul_b (_ha : a ^ 3 = 1) (hb : b ^ 3 = 1) : avgT a b * b = avgT a b := by
  simp only [avgT]
  linear_combination (a^2 + a + 1) * hb

/-- The average kills each isotypic projection. -/
theorem poly_T_mul_Q (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (H : Fin 4) : avgT a b * avgQ a b H = 0 := by
  fin_cases H <;> simp only [avgT, avgQ, genE]
  · linear_combination (-a*b^4 - 2*a*b^3 + a*b + 2*a - 2*b^4 - 4*b^3 + 2*b + 4) * ha + (-3*a^2*b - 6*a^2 - 3*a*b - 6*a - 3*b - 6) * hb
  · linear_combination (-a*b^4 - 2*a*b^3 - 3*a*b^2 - 2*a*b - a - 2*b^4 - 4*b^3 - 6*b^2 - 4*b - 2) * ha
  · linear_combination (3*a^3*b^6 + 3*a^3*b^5 + 3*a^3*b^4 + 3*a^2*b^6 + 3*a^2*b^5 + 3*a^2*b^4 + 3*a*b^6 + 3*a*b^5 + 5*a*b^4 + a*b^3 - 2*a*b - a + 3*b^6 + 3*b^5 + 4*b^4 - b^3 - 3*b^2 - 4*b - 2) * ha + (3*a^2*b^3 + 3*a^2*b^2 + 3*a^2*b + 3*a*b^3 + 3*a*b^2 + 3*a*b + 3*b^3 + 3*b^2 + 3*b) * hb
  · linear_combination (3*a^3*b^4 + 3*a^3*b^3 + 3*a^3*b^2 + 3*a^2*b^4 + 3*a^2*b^3 + 3*a^2*b^2 + 2*a*b^4 + 4*a*b^3 + 3*a*b^2 + a*b - a + b^4 + 2*b^3 - b - 2) * ha

/-- Idempotence (scaled by nine). -/
theorem poly_Q_mul_Q (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (H : Fin 4) : avgQ a b H * avgQ a b H = 9 * avgQ a b H := by
  fin_cases H <;> simp only [avgT, avgQ, genE]
  · linear_combination (a*b^4 + 2*a*b^3 - 3*a*b^2 - 4*a*b + 4*a + 2*b^4 + 4*b^3 - 6*b^2 - 8*b + 8) * ha + (3*a^2*b + 6*a^2 + 3*a*b + 6*a + 3*b + 6) * hb
  · linear_combination (a*b^4 + 2*a*b^3 + 3*a*b^2 + 2*a*b + a + 2*b^4 + 4*b^3 + 6*b^2 + 4*b + 2) * ha + (-3*a^2*b - 6*a^2 - 3*a*b - 6*a + 6*b + 12) * hb
  · linear_combination (9*a^5*b^8 + 12*a^3*b^6 - 6*a^3*b^5 - 6*a^3*b^4 + 9*a^2*b^8 - 6*a^2*b^6 - 6*a^2*b^5 - 6*a^2*b^4 - 6*a*b^6 - 6*a*b^5 - 11*a*b^4 - 4*a*b^3 - 3*a*b^2 + 2*a*b + a + 12*b^6 - 6*b^5 - 10*b^4 - 2*b^3 + 4*b + 2) * ha + (9*a^2*b^5 - 6*a^2*b^3 + 3*a^2*b^2 - 9*a^2*b - 6*a^2 - 6*a*b^3 - 6*a*b^2 - 9*a*b - 6*a + 12*b^3 - 6*b^2 - 9*b + 12) * hb
  · linear_combination (9*a^5*b^4 - 6*a^3*b^4 + 12*a^3*b^3 - 6*a^3*b^2 + 3*a^2*b^4 - 6*a^2*b^3 - 6*a^2*b^2 - 5*a*b^4 - 10*a*b^3 - 9*a*b^2 - 4*a*b + a - 4*b^4 + 10*b^3 - 6*b^2 - 2*b + 2) * ha + (6*a^2*b - 6*a^2 - 3*a*b - 6*a - 3*b + 12) * hb

/-- The subgroup generator fixes the range of `avgQ`. -/
theorem poly_gen_mul_Q (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (H : Fin 4) : genE a b H * avgQ a b H = avgQ a b H := by
  fin_cases H <;> simp only [avgT, avgQ, genE]
  · linear_combination (-b^2 - b + 2) * ha
  · linear_combination (-a^2 - a + 2) * hb
  · linear_combination (3*a^3*b^6 - a*b^4 - a*b^3 - a*b^2 + 3*b^6 - b^4 - b^3 - b^2) * ha + (-a^2*b - a^2 - a*b - a + 3*b^3 - b + 2) * hb
  · linear_combination (3*a^3*b^3 - a*b^3 - a*b^2 - a*b + 2*b^3 - b^2 - b) * ha + (-a^2 - a + 2) * hb

/-- The complementary element has no fixed vectors on the range of `avgQ`. -/
theorem poly_k_Q (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (H : Fin 4) : (kE a b H * kE a b H + kE a b H + 1) * avgQ a b H = 0 := by
  fin_cases H <;> simp only [avgT, avgQ, genE, kE]
  · linear_combination (-a^2*b^3 - a^2*b^2 + a^2*b - 2*a^2 - a*b^3 - a*b^2 + a*b - 2*a - b^3 - b^2 + b - 2) * hb
  · linear_combination (-a*b^2 - a*b - a - 2*b^2 - 2*b - 2) * ha
  · linear_combination (3*a*b^6 + 3*a*b^5 + 3*a*b^4) * ha + (2*a^2*b + a^2 + 3*a*b^3 + 3*a*b^2 + 2*a*b + a - b - 2) * hb
  · linear_combination (3*a^3*b^2 + 3*a^2*b^2 + 2*a*b^2 + 2*a*b - a + b^2 + b - 2) * ha

/-- `a` acts on the range of `avgQ` as a power of `kE`. -/
theorem poly_Q_mul_a (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (H : Fin 4) : avgQ a b H * a = kE a b H ^ e0 H * avgQ a b H := by
  fin_cases H <;> simp only [avgT, avgQ, genE, kE, e0]
  · linear_combination (-b^2 - b + 2) * ha
  · ring
  · linear_combination (3*a^2*b^4 - 3*a*b^6 + 2*b^2 - b - 1) * ha + (a^2*b + a^2 - 3*a*b^3 + a*b - 2*a + b + 1) * hb
  · ring

/-- `b` acts on the range of `avgQ` as a power of `kE`. -/
theorem poly_Q_mul_b (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (H : Fin 4) : avgQ a b H * b = kE a b H ^ e1 H * avgQ a b H := by
  fin_cases H <;> simp only [avgT, avgQ, genE, kE, e1]
  · linear_combination (a^2*b^3 + a^2*b^2 - 2*a^2*b + a*b^3 + a*b^2 - 2*a*b + b^3 + b^2 - 2*b) * hb
  · linear_combination (-a^2 - a + 2) * hb
  · ring
  · linear_combination (-3*a^2*b^2 + 3*a*b^3 + b^2 - 2*b + 1) * ha + (-a^2 + 2*a - 1) * hb

/-- Distinct isotypic projections are orthogonal. -/
theorem poly_Q_mul_Q_ne (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (H H' : Fin 4) (hne : H ≠ H') :
    avgQ a b H * avgQ a b H' = 0 := by
  fin_cases H <;> fin_cases H' <;> simp only [ne_eq, not_true_eq_false] at hne <;>
    simp only [avgT, avgQ, genE]
  · linear_combination (a*b^4 + 2*a*b^3 - a*b - 2*a + 2*b^4 + 4*b^3 - 2*b - 4) * ha
  · linear_combination (-3*a^3*b^6 - 3*a^3*b^5 + 6*a^3*b^4 - 3*a^2*b^6 - 3*a^2*b^5 + 6*a^2*b^4 - 3*a*b^6 - 3*a*b^5 + 4*a*b^4 - a*b^3 + 6*a*b^2 - a*b - 2*a - 3*b^6 - 3*b^5 + 5*b^4 + b^3 + 6*b^2 - 2*b - 4) * ha + (-3*a^2*b^3 - 3*a^2*b^2 + 6*a^2*b - 3*a*b^3 - 3*a*b^2 + 6*a*b - 3*b^3 - 3*b^2 + 6*b) * hb
  · linear_combination (-3*a^3*b^4 - 3*a^3*b^3 + 6*a^3*b^2 - 3*a^2*b^4 - 3*a^2*b^3 + 6*a^2*b^2 - 2*a*b^4 - 4*a*b^3 + 3*a*b^2 + 5*a*b - 2*a - b^4 - 2*b^3 + 3*b^2 + 4*b - 4) * ha
  · linear_combination (a*b^4 + 2*a*b^3 - a*b - 2*a + 2*b^4 + 4*b^3 - 2*b - 4) * ha
  · linear_combination (-3*a^3*b^6 - 3*a^3*b^5 - 3*a^3*b^4 - 3*a^2*b^6 - 3*a^2*b^5 - 3*a^2*b^4 + 6*a*b^6 + 6*a*b^5 + 4*a*b^4 - a*b^3 + 2*a*b + a - 3*b^6 - 3*b^5 - 4*b^4 + b^3 + 3*b^2 + 4*b + 2) * ha + (-3*a^2*b^3 - 3*a^2*b^2 + 3*a^2*b + 3*a^2 + 6*a*b^3 + 6*a*b^2 + 3*a*b + 3*a - 3*b^3 - 3*b^2 - 6*b - 6) * hb
  · linear_combination (-3*a^3*b^4 - 3*a^3*b^3 - 3*a^3*b^2 - 3*a^2*b^4 - 3*a^2*b^3 - 3*a^2*b^2 + 7*a*b^4 + 5*a*b^3 + 6*a*b^2 - a*b + a - b^4 - 2*b^3 + b + 2) * ha + (-3*a^2*b + 3*a^2 + 6*a*b + 3*a - 3*b - 6) * hb
  · linear_combination (-3*a^3*b^6 - 3*a^3*b^5 + 6*a^3*b^4 - 3*a^2*b^6 - 3*a^2*b^5 + 6*a^2*b^4 - 3*a*b^6 - 3*a*b^5 + 4*a*b^4 - a*b^3 + 6*a*b^2 - a*b - 2*a - 3*b^6 - 3*b^5 + 5*b^4 + b^3 + 6*b^2 - 2*b - 4) * ha + (-3*a^2*b^3 - 3*a^2*b^2 + 6*a^2*b - 3*a*b^3 - 3*a*b^2 + 6*a*b - 3*b^3 - 3*b^2 + 6*b) * hb
  · linear_combination (-3*a^3*b^6 - 3*a^3*b^5 - 3*a^3*b^4 - 3*a^2*b^6 - 3*a^2*b^5 - 3*a^2*b^4 + 6*a*b^6 + 6*a*b^5 + 4*a*b^4 - a*b^3 + 2*a*b + a - 3*b^6 - 3*b^5 - 4*b^4 + b^3 + 3*b^2 + 4*b + 2) * ha + (-3*a^2*b^3 - 3*a^2*b^2 + 3*a^2*b + 3*a^2 + 6*a*b^3 + 6*a*b^2 + 3*a*b + 3*a - 3*b^3 - 3*b^2 - 6*b - 6) * hb
  · linear_combination (9*a^5*b^6 - 3*a^3*b^6 + 6*a^3*b^5 + 3*a^3*b^4 - 3*a^3*b^3 - 3*a^3*b^2 + 6*a^2*b^6 - 3*a^2*b^5 - 6*a^2*b^4 - 3*a^2*b^3 - 3*a^2*b^2 - 3*a*b^6 - 3*a*b^5 + a*b^4 + 2*a*b^3 + 3*a*b^2 - a*b + a - 3*b^6 + 6*b^5 + 2*b^4 - 5*b^3 - 3*b^2 + b + 2) * ha + (6*a^2*b^3 - 3*a^2*b^2 - 6*a^2*b + 3*a^2 - 3*a*b^3 - 3*a*b^2 + 3*a*b + 3*a - 3*b^3 + 6*b^2 + 3*b - 6) * hb
  · linear_combination (-3*a^3*b^4 - 3*a^3*b^3 + 6*a^3*b^2 - 3*a^2*b^4 - 3*a^2*b^3 + 6*a^2*b^2 - 2*a*b^4 - 4*a*b^3 + 3*a*b^2 + 5*a*b - 2*a - b^4 - 2*b^3 + 3*b^2 + 4*b - 4) * ha
  · linear_combination (-3*a^3*b^4 - 3*a^3*b^3 - 3*a^3*b^2 - 3*a^2*b^4 - 3*a^2*b^3 - 3*a^2*b^2 + 7*a*b^4 + 5*a*b^3 + 6*a*b^2 - a*b + a - b^4 - 2*b^3 + b + 2) * ha + (-3*a^2*b + 3*a^2 + 6*a*b + 3*a - 3*b - 6) * hb
  · linear_combination (9*a^5*b^6 - 3*a^3*b^6 + 6*a^3*b^5 + 3*a^3*b^4 - 3*a^3*b^3 - 3*a^3*b^2 + 6*a^2*b^6 - 3*a^2*b^5 - 6*a^2*b^4 - 3*a^2*b^3 - 3*a^2*b^2 - 3*a*b^6 - 3*a*b^5 + a*b^4 + 2*a*b^3 + 3*a*b^2 - a*b + a - 3*b^6 + 6*b^5 + 2*b^4 - 5*b^3 - 3*b^2 + b + 2) * ha + (6*a^2*b^3 - 3*a^2*b^2 - 6*a^2*b + 3*a^2 - 3*a*b^3 - 3*a*b^2 + 3*a*b + 3*a - 3*b^3 + 6*b^2 + 3*b - 6) * hb

/-- The resolution of the identity. -/
theorem poly_sum (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) : avgT a b + (avgQ a b 0 + avgQ a b 1 + avgQ a b 2 + avgQ a b 3) = 9 := by
  simp only [avgT, avgQ, genE]
  linear_combination (3*a*b^4 + 3*a*b^2) * ha + (3*a*b) * hb


end PolyIds

/-! ### Operator identities for a `K`-action -/

section Ops
universe u
variable {V : Type u} [AddCommGroup V] [Module ℝ V] (ρ : KAction V)

open scoped IsMulCommutative in
/-- A commutative model of the group algebra image. -/
theorem exists_comm_model : ∃ (R : Type u) (_ : CommRing R) (f : R →+* Module.End ℝ V) (a b : R),
    f a = ρ.g0 ∧ f b = ρ.g1 ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 := by
  let s : Set (Module.End ℝ V) := {ρ.g0, ρ.g1}
  have hcomm : s.Pairwise Commute := by
    intro x hx y hy _
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact ρ.comm
    · exact ρ.comm.symm
    · exact Commute.refl _
  have := Algebra.isMulCommutative_adjoin ℝ hcomm
  let a : Algebra.adjoin ℝ s := ⟨ρ.g0, Algebra.subset_adjoin (by simp [s])⟩
  let b : Algebra.adjoin ℝ s := ⟨ρ.g1, Algebra.subset_adjoin (by simp [s])⟩
  refine ⟨Algebra.adjoin ℝ s, inferInstance, (Algebra.adjoin ℝ s).val.toRingHom, a, b, rfl, rfl,
    ?_, ?_⟩
  · apply Subtype.ext
    simp [a, ρ.g0_cube]
  · apply Subtype.ext
    simp [b, ρ.g1_cube]

theorem gen_eq (H : Fin 4) : ρ.gen H = genE ρ.g0 ρ.g1 H := by
  fin_cases H <;> rfl

theorem op_T_mul_g0 : avgT ρ.g0 ρ.g1 * ρ.g0 = avgT ρ.g0 ρ.g1 := by
  obtain ⟨R, _, f, a, b, hfa, hfb, ha, hb⟩ := exists_comm_model ρ
  rw [← hfa, ← hfb, ← map_avgT, ← map_mul, poly_T_mul_a ha hb]

theorem op_T_mul_g1 : avgT ρ.g0 ρ.g1 * ρ.g1 = avgT ρ.g0 ρ.g1 := by
  obtain ⟨R, _, f, a, b, hfa, hfb, ha, hb⟩ := exists_comm_model ρ
  rw [← hfa, ← hfb, ← map_avgT, ← map_mul, poly_T_mul_b ha hb]

theorem op_g0_mul_T : ρ.g0 * avgT ρ.g0 ρ.g1 = avgT ρ.g0 ρ.g1 := by
  obtain ⟨R, _, f, a, b, hfa, hfb, ha, hb⟩ := exists_comm_model ρ
  rw [← hfa, ← hfb, ← map_avgT, ← map_mul, mul_comm, poly_T_mul_a ha hb]

theorem op_g1_mul_T : ρ.g1 * avgT ρ.g0 ρ.g1 = avgT ρ.g0 ρ.g1 := by
  obtain ⟨R, _, f, a, b, hfa, hfb, ha, hb⟩ := exists_comm_model ρ
  rw [← hfa, ← hfb, ← map_avgT, ← map_mul, mul_comm, poly_T_mul_b ha hb]

theorem op_T_mul_Q (H : Fin 4) : avgT ρ.g0 ρ.g1 * avgQ ρ.g0 ρ.g1 H = 0 := by
  obtain ⟨R, _, f, a, b, hfa, hfb, ha, hb⟩ := exists_comm_model ρ
  rw [← hfa, ← hfb, ← map_avgT, ← map_avgQ, ← map_mul, poly_T_mul_Q ha hb, map_zero]

theorem op_Q_mul_Q (H : Fin 4) :
    avgQ ρ.g0 ρ.g1 H * avgQ ρ.g0 ρ.g1 H = 9 * avgQ ρ.g0 ρ.g1 H := by
  obtain ⟨R, _, f, a, b, hfa, hfb, ha, hb⟩ := exists_comm_model ρ
  rw [← hfa, ← hfb, ← map_avgQ, ← map_mul, poly_Q_mul_Q ha hb, map_mul, map_ofNat]

theorem op_Q_mul_Q_ne (H H' : Fin 4) (hne : H ≠ H') :
    avgQ ρ.g0 ρ.g1 H * avgQ ρ.g0 ρ.g1 H' = 0 := by
  obtain ⟨R, _, f, a, b, hfa, hfb, ha, hb⟩ := exists_comm_model ρ
  rw [← hfa, ← hfb, ← map_avgQ, ← map_avgQ, ← map_mul, poly_Q_mul_Q_ne ha hb H H' hne, map_zero]

theorem op_gen_mul_Q (H : Fin 4) : ρ.gen H * avgQ ρ.g0 ρ.g1 H = avgQ ρ.g0 ρ.g1 H := by
  obtain ⟨R, _, f, a, b, hfa, hfb, ha, hb⟩ := exists_comm_model ρ
  rw [gen_eq, ← hfa, ← hfb, ← map_avgQ, ← map_genE, ← map_mul, poly_gen_mul_Q ha hb]

theorem op_k_Q (H : Fin 4) :
    (kE ρ.g0 ρ.g1 H * kE ρ.g0 ρ.g1 H + kE ρ.g0 ρ.g1 H + 1) * avgQ ρ.g0 ρ.g1 H = 0 := by
  obtain ⟨R, _, f, a, b, hfa, hfb, ha, hb⟩ := exists_comm_model ρ
  rw [← hfa, ← hfb, ← map_avgQ, ← map_kE, ← map_one f, ← map_mul, ← map_add, ← map_add,
    ← map_mul, poly_k_Q ha hb, map_zero]

theorem op_k_comm_Q (H : Fin 4) :
    kE ρ.g0 ρ.g1 H * avgQ ρ.g0 ρ.g1 H = avgQ ρ.g0 ρ.g1 H * kE ρ.g0 ρ.g1 H := by
  obtain ⟨R, _, f, a, b, hfa, hfb, ha, hb⟩ := exists_comm_model ρ
  rw [← hfa, ← hfb, ← map_avgQ, ← map_kE, ← map_mul, ← map_mul, mul_comm]

theorem op_Q_mul_g0 (H : Fin 4) :
    avgQ ρ.g0 ρ.g1 H * ρ.g0 = kE ρ.g0 ρ.g1 H ^ e0 H * avgQ ρ.g0 ρ.g1 H := by
  obtain ⟨R, _, f, a, b, hfa, hfb, ha, hb⟩ := exists_comm_model ρ
  rw [← hfa, ← hfb, ← map_avgQ, ← map_kE, ← map_mul, ← map_pow, ← map_mul, poly_Q_mul_a ha hb]

theorem op_Q_mul_g1 (H : Fin 4) :
    avgQ ρ.g0 ρ.g1 H * ρ.g1 = kE ρ.g0 ρ.g1 H ^ e1 H * avgQ ρ.g0 ρ.g1 H := by
  obtain ⟨R, _, f, a, b, hfa, hfb, ha, hb⟩ := exists_comm_model ρ
  rw [← hfa, ← hfb, ← map_avgQ, ← map_kE, ← map_mul, ← map_pow, ← map_mul, poly_Q_mul_b ha hb]

theorem op_sum : avgT ρ.g0 ρ.g1 + (avgQ ρ.g0 ρ.g1 0 + avgQ ρ.g0 ρ.g1 1 + avgQ ρ.g0 ρ.g1 2 +
    avgQ ρ.g0 ρ.g1 3) = 9 := by
  obtain ⟨R, _, f, a, b, hfa, hfb, ha, hb⟩ := exists_comm_model ρ
  rw [← hfa, ← hfb, ← map_avgT, ← map_avgQ, ← map_avgQ, ← map_avgQ, ← map_avgQ, ← map_add,
    ← map_add, ← map_add, ← map_add, poly_sum ha hb, map_ofNat]

end Ops

/-! ### The isotypic decomposition -/

section Decomp
universe u
variable {V : Type u} [AddCommGroup V] [Module ℝ V] (ρ : KAction V)

open CKM.NativeFirstOrder (fixedSpace mem_fixedSpace)

theorem pow_apply_fixed {f : Module.End ℝ V} {v : V} (h : f v = v) (j : ℕ) : (f ^ j) v = v := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, Module.End.mul_apply, h, ih]

theorem g0_apply_fixK {x : V} (hx : x ∈ ρ.fixK) : ρ.g0 x = x :=
  mem_fixedSpace.1 (Submodule.mem_inf.1 hx).1

theorem g1_apply_fixK {x : V} (hx : x ∈ ρ.fixK) : ρ.g1 x = x :=
  mem_fixedSpace.1 (Submodule.mem_inf.1 hx).2

theorem genE_apply_fixK {x : V} (hx : x ∈ ρ.fixK) (H : Fin 4) : genE ρ.g0 ρ.g1 H x = x := by
  have h0 := g0_apply_fixK ρ hx
  have h1 := g1_apply_fixK ρ hx
  fin_cases H <;> simp [genE, Module.End.mul_apply, pow_apply_fixed h0, pow_apply_fixed h1, h0, h1]

theorem avgT_apply_fixK {x : V} (hx : x ∈ ρ.fixK) : avgT ρ.g0 ρ.g1 x = (9 : ℝ) • x := by
  have h0 := g0_apply_fixK ρ hx
  have h1 := g1_apply_fixK ρ hx
  simp only [avgT, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
    pow_apply_fixed h0, pow_apply_fixed h1, map_add, h0, h1]
  module

theorem avgQ_apply_fixK {x : V} (hx : x ∈ ρ.fixK) (H : Fin 4) : avgQ ρ.g0 ρ.g1 H x = 0 := by
  have hg := genE_apply_fixK ρ hx H
  simp only [avgQ, LinearMap.sub_apply, Module.End.mul_apply, Module.End.ofNat_apply,
    LinearMap.add_apply, Module.End.one_apply, pow_apply_fixed hg, hg, avgT_apply_fixK ρ hx]
  module

/-- The nontrivial `H`-isotypic part. -/
def isoW (H : Fin 4) : Submodule ℝ V := LinearMap.range (avgQ ρ.g0 ρ.g1 H)

theorem isoW_le_fixH (H : Fin 4) : isoW ρ H ≤ ρ.fixH H := by
  rintro _ ⟨u, rfl⟩
  rw [KAction.fixH, mem_fixedSpace, ← Module.End.mul_apply, op_gen_mul_Q]

theorem fixK_le_fixH (H : Fin 4) : ρ.fixK ≤ ρ.fixH H := by
  intro x hx
  rw [KAction.fixH, mem_fixedSpace, gen_eq, genE_apply_fixK ρ hx]

theorem avgT_mem_fixK (v : V) : avgT ρ.g0 ρ.g1 v ∈ ρ.fixK := by
  refine Submodule.mem_inf.2 ⟨mem_fixedSpace.2 ?_, mem_fixedSpace.2 ?_⟩
  · rw [← Module.End.mul_apply, op_g0_mul_T]
  · rw [← Module.End.mul_apply, op_g1_mul_T]

theorem fixH_le_sup (H : Fin 4) : ρ.fixH H ≤ ρ.fixK ⊔ isoW ρ H := by
  intro v hv
  rw [KAction.fixH, mem_fixedSpace, gen_eq] at hv
  have hQ : avgQ ρ.g0 ρ.g1 H v = (9 : ℝ) • v - avgT ρ.g0 ρ.g1 v := by
    simp only [avgQ, LinearMap.sub_apply, Module.End.mul_apply, Module.End.ofNat_apply,
      LinearMap.add_apply, Module.End.one_apply, pow_apply_fixed hv, hv]
    module
  have hv' : v = (1 / 9 : ℝ) • avgT ρ.g0 ρ.g1 v + (1 / 9 : ℝ) • avgQ ρ.g0 ρ.g1 H v := by
    rw [hQ]; module
  rw [hv']
  exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (avgT_mem_fixK ρ v))
    (Submodule.smul_mem _ _ ⟨v, rfl⟩)

theorem fixK_inf_isoW (H : Fin 4) : ρ.fixK ⊓ isoW ρ H = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro x ⟨hx, u, rfl⟩
  have h1 := avgT_apply_fixK ρ hx
  rw [← Module.End.mul_apply, op_T_mul_Q, LinearMap.zero_apply] at h1
  have h9 : (9 : ℝ) ≠ 0 := by norm_num
  exact (smul_eq_zero.1 h1.symm).resolve_left h9

theorem finrank_isoW [FiniteDimensional ℝ V] (m : ℕ) (n : Fin 4 → ℕ)
    (hK : Module.finrank ℝ ρ.fixK = m)
    (hH : ∀ H, Module.finrank ℝ (ρ.fixH H) = m + 2 * n H) (H : Fin 4) :
    Module.finrank ℝ (isoW ρ H) = 2 * n H := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq ρ.fixK (isoW ρ H)
  have hsup : ρ.fixK ⊔ isoW ρ H = ρ.fixH H :=
    le_antisymm (sup_le (fixK_le_fixH ρ H) (isoW_le_fixH ρ H)) (fixH_le_sup ρ H)
  rw [hsup, fixK_inf_isoW, finrank_bot, hH, hK] at h
  omega

theorem kE_mem_isoW (H : Fin 4) : ∀ w ∈ isoW ρ H, kE ρ.g0 ρ.g1 H w ∈ isoW ρ H := by
  rintro _ ⟨u, rfl⟩
  exact ⟨kE ρ.g0 ρ.g1 H u, by rw [← Module.End.mul_apply, ← op_k_comm_Q, Module.End.mul_apply]⟩

/-- The complementary generator on the isotypic part. -/
def kW (H : Fin 4) : Module.End ℝ (isoW ρ H) := (kE ρ.g0 ρ.g1 H).restrict (kE_mem_isoW ρ H)

theorem kW_coe (H : Fin 4) (w : isoW ρ H) : (kW ρ H w : V) = kE ρ.g0 ρ.g1 H w := rfl

theorem kW_pow_coe (H : Fin 4) (j : ℕ) (w : isoW ρ H) :
    ((kW ρ H ^ j) w : V) = (kE ρ.g0 ρ.g1 H ^ j) w := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', Module.End.mul_apply, kW_coe, ih, pow_succ', Module.End.mul_apply]

theorem kW_rel (H : Fin 4) (w : isoW ρ H) : kW ρ H (kW ρ H w) + kW ρ H w + w = 0 := by
  obtain ⟨_, u, rfl⟩ := w
  apply Subtype.ext
  have h := LinearMap.congr_fun (op_k_Q ρ H) u
  simp only [Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply,
    LinearMap.zero_apply] at h
  simpa only [Submodule.coe_add, kW_coe, Submodule.coe_zero] using h

/-- Projection onto the isotypic part. -/
def projW (H : Fin 4) : V →ₗ[ℝ] isoW ρ H :=
  ((1 / 9 : ℝ) • avgQ ρ.g0 ρ.g1 H).codRestrict (isoW ρ H) fun v =>
    ⟨(1 / 9 : ℝ) • v, by simp only [map_smul, LinearMap.smul_apply]⟩

theorem projW_coe (H : Fin 4) (v : V) :
    (projW ρ H v : V) = (1 / 9 : ℝ) • avgQ ρ.g0 ρ.g1 H v := rfl

/-- Projection onto the `K`-fixed part. -/
def projK : V →ₗ[ℝ] ρ.fixK :=
  ((1 / 9 : ℝ) • avgT ρ.g0 ρ.g1).codRestrict ρ.fixK fun v =>
    Submodule.smul_mem _ _ (avgT_mem_fixK ρ v)

theorem projK_coe (v : V) : (projK ρ v : V) = (1 / 9 : ℝ) • avgT ρ.g0 ρ.g1 v := rfl

end Decomp

end KClassify

open KClassify

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- **Classification by fixed dimensions.** -/
theorem kEquiv_std_of_finrank (ρ : KAction V) (m : ℕ) (n : Fin 4 → ℕ)
    (hK : Module.finrank ℝ ρ.fixK = m)
    (hH : ∀ H, Module.finrank ℝ (ρ.fixH H) = m + 2 * n H) :
    Nonempty (KEquiv ρ (stdAction m n)) := by
  classical
  have hex : ∀ H, ∃ e : isoW ρ H ≃ₗ[ℝ] (Fin (n H) → ℂ), ∀ w, e (kW ρ H w) = ω • e w :=
    fun H => cx_exists_equiv (kW ρ H) (kW_rel ρ H) (n H) (finrank_isoW ρ m n hK hH H)
  choose e he using hex
  let eK : ρ.fixK ≃ₗ[ℝ] (Fin m → ℝ) :=
    LinearEquiv.ofFinrankEq ρ.fixK (Fin m → ℝ) (by rw [hK, Module.finrank_fin_fun])
  let Φ : V →ₗ[ℝ] StdSpace m n :=
    LinearMap.prod (eK.toLinearMap ∘ₗ projK ρ)
      (LinearMap.pi fun H => (e H).toLinearMap ∘ₗ projW ρ H)
  let Ψ : StdSpace m n →ₗ[ℝ] V :=
    ρ.fixK.subtype ∘ₗ eK.symm.toLinearMap ∘ₗ LinearMap.fst ℝ _ _ +
      ∑ H : Fin 4, (isoW ρ H).subtype ∘ₗ (e H).symm.toLinearMap ∘ₗ
        LinearMap.proj (φ := fun H => Fin (n H) → ℂ) H ∘ₗ LinearMap.snd ℝ _ _
  have hΦ1 : ∀ v, (Φ v).1 = eK (projK ρ v) := fun _ => rfl
  have hΦ2 : ∀ v H, (Φ v).2 H = e H (projW ρ H v) := fun _ _ => rfl
  have hΨ : ∀ p : StdSpace m n,
      Ψ p = (eK.symm p.1 : V) + ∑ H : Fin 4, ((e H).symm (p.2 H) : V) := by
    intro p
    simp [Ψ, LinearMap.sum_apply]
  have h2 : Ψ ∘ₗ Φ = LinearMap.id := by
    ext v
    rw [LinearMap.comp_apply, hΨ, LinearMap.id_apply, hΦ1]
    simp only [hΦ2, LinearEquiv.symm_apply_apply, projK_coe, projW_coe, Fin.sum_univ_four]
    have h := LinearMap.congr_fun (op_sum ρ) v
    simp only [LinearMap.add_apply, Module.End.ofNat_apply] at h
    linear_combination (norm := module) (1 / 9 : ℝ) • h
  have h1 : Φ ∘ₗ Ψ = LinearMap.id := by
    refine LinearMap.ext fun p => ?_
    have hx : (eK.symm p.1 : V) ∈ ρ.fixK := (eK.symm p.1).2
    have hu : ∀ H, ∃ u, avgQ ρ.g0 ρ.g1 H u = ((e H).symm (p.2 H) : V) :=
      fun H => LinearMap.mem_range.1 ((e H).symm (p.2 H)).2
    choose u hu using hu
    have hΨ' : Ψ p = (eK.symm p.1 : V) + ∑ H : Fin 4, avgQ ρ.g0 ρ.g1 H (u H) := by
      rw [hΨ]; simp only [hu]
    rw [LinearMap.id_apply, LinearMap.comp_apply]
    refine Prod.ext ?_ (funext fun H => ?_)
    · rw [hΦ1]
      have : projK ρ (Ψ p) = eK.symm p.1 := by
        apply Subtype.ext
        rw [projK_coe, hΨ', map_add, map_sum, avgT_apply_fixK ρ hx]
        simp only [← Module.End.mul_apply, op_T_mul_Q, LinearMap.zero_apply,
          Finset.sum_const_zero, add_zero, smul_smul]
        norm_num
      rw [this, LinearEquiv.apply_symm_apply]
    · rw [hΦ2]
      have : projW ρ H (Ψ p) = (e H).symm (p.2 H) := by
        apply Subtype.ext
        rw [projW_coe, hΨ', map_add, map_sum, avgQ_apply_fixK ρ hx, zero_add,
          Finset.sum_eq_single H, ← hu, ← Module.End.mul_apply, op_Q_mul_Q,
          Module.End.mul_apply, Module.End.ofNat_apply]
        · module
        · intro H' _ hne
          rw [← Module.End.mul_apply, op_Q_mul_Q_ne ρ H H' (Ne.symm hne), LinearMap.zero_apply]
        · simp
      rw [this, LinearEquiv.apply_symm_apply]
  refine ⟨{ toLinearEquiv := LinearEquiv.ofLinearMap Φ Ψ h1 h2, map_g0 := ?_, map_g1 := ?_ }⟩
  · intro v
    simp only [LinearEquiv.coe_ofLinearMap]
    refine Prod.ext ?_ (funext fun H => funext fun i => ?_)
    · rw [hΦ1]
      show eK (projK ρ (ρ.g0 v)) = eK (projK ρ v)
      congr 1
      apply Subtype.ext
      rw [projK_coe, projK_coe, ← Module.End.mul_apply, op_T_mul_g0]
    · have hw : projW ρ H (ρ.g0 v) = (kW ρ H ^ e0 H) (projW ρ H v) := by
        apply Subtype.ext
        rw [projW_coe, kW_pow_coe, projW_coe, map_smul, ← Module.End.mul_apply,
          ← Module.End.mul_apply, op_Q_mul_g0]
      show e H (projW ρ H (ρ.g0 v)) i = ω ^ (kChar H).1.val * e H (projW ρ H v) i
      rw [hw, cx_equiv_pow (kW ρ H) (e H) (he H), e0_eq]
      rfl
  · intro v
    simp only [LinearEquiv.coe_ofLinearMap]
    refine Prod.ext ?_ (funext fun H => funext fun i => ?_)
    · rw [hΦ1]
      show eK (projK ρ (ρ.g1 v)) = eK (projK ρ v)
      congr 1
      apply Subtype.ext
      rw [projK_coe, projK_coe, ← Module.End.mul_apply, op_T_mul_g1]
    · have hw : projW ρ H (ρ.g1 v) = (kW ρ H ^ e1 H) (projW ρ H v) := by
        apply Subtype.ext
        rw [projW_coe, kW_pow_coe, projW_coe, map_smul, ← Module.End.mul_apply,
          ← Module.End.mul_apply, op_Q_mul_g1]
      show e H (projW ρ H (ρ.g1 v)) i = ω ^ (kChar H).2.val * e H (projW ρ H v) i
      rw [hw, cx_equiv_pow (kW ρ H) (e H) (he H), e1_eq]
      rfl

end CKM.NativeIntrinsicTriality

#print axioms CKM.NativeIntrinsicTriality.kEquiv_std_of_finrank
#print axioms CKM.NativeIntrinsicTriality.KClassify.cx_exists_equiv
#print axioms CKM.NativeIntrinsicTriality.KClassify.exists_comm_model
#print axioms CKM.NativeIntrinsicTriality.KClassify.finrank_isoW
#print axioms CKM.NativeIntrinsicTriality.KClassify.poly_Q_mul_Q_ne
#print axioms CKM.NativeIntrinsicTriality.KClassify.op_sum

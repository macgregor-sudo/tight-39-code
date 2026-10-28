module

public import A3QuartetSolve

@[expose] public section

/-!
# The orbit map onto the standard quartet first-order space, and relabelling invariance

Helpers for `A3Quartet`. `phiL` reads eight real coordinates of a variation; `Xmat` builds the
traceless anti-Hermitian matrix with those coordinates; the commutator `[Xmat c, q]` lies in the
first-order space, and `core_zero` (generated certificates) shows `phiL` is injective there.
-/

noncomputable section

namespace CKM.NativeFirstOrder.QuartetAux

open CompactAlbert UnitaryErrorBases.ComplexQuartet ConfigurationResidualIndices

set_option linter.unusedSimpArgs false

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega

abbrev Var := Fin 4 → Fin 3 → TitsComplexMatrix

/-! ## Ring identities -/

theorem tan_comm {R : Type*} [Ring R] (q X : R) (h : q * q = q) :
    q * (X * q - q * X) + (X * q - q * X) * q = X * q - q * X := by
  have e : q * (X * q - q * X) + (X * q - q * X) * q =
      q * X * q - (q * q) * X + X * (q * q) - q * X * q := by noncomm_ring
  rw [e, h]; abel

theorem win_comm {R : Type*} [Ring R] (qa qb X : R) (hab : qa * qb = 0) (hba : qb * qa = 0) :
    qa * (X * qb - qb * X) + (X * qb - qb * X) * qa + (X * qa - qa * X) * qb +
      qb * (X * qa - qa * X) = 0 := by
  have e : qa * (X * qb - qb * X) + (X * qb - qb * X) * qa + (X * qa - qa * X) * qb +
      qb * (X * qa - qa * X) = X * (qb * qa) - (qa * qb) * X + X * (qa * qb) - (qb * qa) * X := by
    noncomm_ring
  rw [e, hab, hba]; simp

theorem cmul {R : Type*} [Ring R] (g g' a b : R) (h : g' * g = 1) :
    g * a * g' * (g * b * g') = g * (a * b) * g' := by
  calc g * a * g' * (g * b * g') = g * a * (g' * g) * b * g' := by noncomm_ring
    _ = g * (a * b) * g' := by rw [h, mul_one]; noncomm_ring

theorem herm_trace_im (A B : TitsComplexMatrix) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace.im = 0 := by
  have h1 : star (A * B).trace = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq, Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_im.mp h1

/-! ## Within-frame conditions for every ordered pair -/

theorem pair_ne (s : Fin 3) : (withinPair s).val.1 ≠ (withinPair s).val.2 :=
  ne_of_lt (withinPair s).2

/-- The within-frame equation of the first-order space holds for every pair of distinct outcomes. -/
theorem win_general (q δ : Var) (hδ : δ ∈ quartetFirstOrder q) (k : Fin 4) (a b : Fin 3)
    (hab : a ≠ b) :
    q k a * δ k b + δ k b * q k a + δ k a * q k b + q k b * δ k a = 0 := by
  obtain ⟨-, -, h3, -, -⟩ := hδ
  have h0 := h3 k 0
  have h1 := h3 k 1
  have h2 := h3 k 2
  rw [withinPair_zero] at h0
  rw [withinPair_one] at h1
  rw [withinPair_two] at h2
  have h0' : q k 0 * δ k 1 + δ k 1 * q k 0 + δ k 0 * q k 1 + q k 1 * δ k 0 = 0 := h0
  have h1' : q k 0 * δ k 2 + δ k 2 * q k 0 + δ k 0 * q k 2 + q k 2 * δ k 0 = 0 := h1
  have h2' : q k 1 * δ k 2 + δ k 2 * q k 1 + δ k 1 * q k 2 + q k 2 * δ k 1 = 0 := h2
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
  all_goals obtain rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 := by fin_cases b <;> simp
  all_goals first
    | exact absurd rfl hab
    | exact h0' | exact h1' | exact h2'
    | (rw [← h0']; abel1) | (rw [← h1']; abel1) | (rw [← h2']; abel1)

/-! ## Commutators lie in the first-order space -/

theorem comm_mem (q : Var) (hH : ∀ k t, (q k t).IsHermitian) (hI : ∀ k t, q k t * q k t = q k t)
    (hO : ∀ k (a b : Fin 3), a ≠ b → q k a * q k b = 0) (hS : ∀ k, ∑ t, q k t = 1)
    (X : TitsComplexMatrix) (hX : X.conjTranspose = -X) :
    (fun k t => X * q k t - q k t * X) ∈ quartetFirstOrder q := by
  refine ⟨fun k t => ?_, fun k t => tan_comm _ _ (hI k t), fun k s => ?_, fun k => ?_,
    fun k k' t t' _ => ?_⟩
  · show (X * q k t - q k t * X).conjTranspose = X * q k t - q k t * X
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hX,
      (hH k t).eq]
    simp only [mul_neg, neg_mul, sub_neg_eq_add]
    abel
  · exact win_comm _ _ _ (hO k _ _ (pair_ne s)) (hO k _ _ (pair_ne s).symm)
  · show ∑ t, (X * q k t - q k t * X) = 0
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hS k, mul_one, one_mul,
      sub_self]
  · show (q k t * (X * q k' t' - q k' t' * X) + (X * q k t - q k t * X) * q k' t').trace.re = 0
    have e : q k t * (X * q k' t' - q k' t' * X) + (X * q k t - q k t * X) * q k' t' =
        X * (q k t * q k' t') - (q k t * q k' t') * X := by noncomm_ring
    rw [e, Matrix.trace_sub, Matrix.trace_mul_comm X, sub_self, Complex.zero_re]

/-! ## The standard quartet -/

theorem std_idem (k : Fin 4) (t : Fin 3) :
    (stdQuartet k t).val * (stdQuartet k t).val = (stdQuartet k t).val := by
  fin_cases k <;> fin_cases t
  exacts [qmul_0_0_0, qmul_0_1_1, qmul_0_2_2, qmul_1_0_0, qmul_1_1_1, qmul_1_2_2, qmul_2_0_0,
    qmul_2_1_1, qmul_2_2_2, qmul_3_0_0, qmul_3_1_1, qmul_3_2_2]

theorem std_orth (k : Fin 4) (a b : Fin 3) (h : a ≠ b) :
    (stdQuartet k a).val * (stdQuartet k b).val = 0 := by
  fin_cases k <;> fin_cases a <;> fin_cases b
  exacts [absurd rfl h, qmul_0_0_1, qmul_0_0_2, qmul_0_1_0, absurd rfl h, qmul_0_1_2, qmul_0_2_0,
    qmul_0_2_1, absurd rfl h, absurd rfl h, qmul_1_0_1, qmul_1_0_2, qmul_1_1_0, absurd rfl h,
    qmul_1_1_2, qmul_1_2_0, qmul_1_2_1, absurd rfl h, absurd rfl h, qmul_2_0_1, qmul_2_0_2,
    qmul_2_1_0, absurd rfl h, qmul_2_1_2, qmul_2_2_0, qmul_2_2_1, absurd rfl h, absurd rfl h,
    qmul_3_0_1, qmul_3_0_2, qmul_3_1_0, absurd rfl h, qmul_3_1_2, qmul_3_2_0, qmul_3_2_1,
    absurd rfl h]

theorem std_sum (k : Fin 4) : ∑ t, (stdQuartet k t).val = 1 := by
  fin_cases k
  · exact coordinateProjector_sum
  · exact phaseProjector_sum 0
  · exact phaseProjector_sum 1
  · exact phaseProjector_sum 2

/-! ## Coordinates and the inverse construction -/

/-- Eight real coordinates of a variation. -/
def phiL : Var →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun δ := ![(δ 0 0 0 1).re, (δ 0 0 0 1).im, (δ 0 0 0 2).re, (δ 0 0 0 2).im,
    (δ 0 1 1 2).re, (δ 0 1 1 2).im, (δ 1 0 0 1).im, (δ 1 0 1 2).im]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' c x := by ext i; fin_cases i <;> simp

/-- First diagonal parameter of `Xmat`. -/
def xa (c : Fin 8 → ℝ) : ℝ := c 1 / 3 + c 3 / 3 - 2 * c 5 / 3 + 2 * c 6 + c 7

/-- Second diagonal parameter of `Xmat`. -/
def xb (c : Fin 8 → ℝ) : ℝ := c 1 / 3 - 2 * c 3 / 3 + c 5 / 3 - c 6 + c 7

/-- The traceless anti-Hermitian matrix whose commutator with the quartet has coordinates `c`. -/
def Xmat (c : Fin 8 → ℝ) : TitsComplexMatrix :=
  !![Complex.I * (xa c : ℂ), -((c 0 : ℂ) + (c 1 : ℂ) * Complex.I),
      -((c 2 : ℂ) + (c 3 : ℂ) * Complex.I);
    (c 0 : ℂ) - (c 1 : ℂ) * Complex.I, Complex.I * (xb c : ℂ),
      -((c 4 : ℂ) + (c 5 : ℂ) * Complex.I);
    (c 2 : ℂ) - (c 3 : ℂ) * Complex.I, (c 4 : ℂ) - (c 5 : ℂ) * Complex.I,
      -(Complex.I * ((xa c : ℂ) + (xb c : ℂ)))]

theorem Xmat_skew (c : Fin 8 → ℝ) : (Xmat c).conjTranspose = -Xmat c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;> simp [Xmat, Matrix.conjTranspose_apply]

/-- `Xmat` as a real-linear map. -/
def XL : (Fin 8 → ℝ) →ₗ[ℝ] TitsComplexMatrix where
  toFun := Xmat
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Xmat, xa, xb] <;> ring
  map_smul' r x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Xmat, xa, xb, Complex.real_smul] <;> ring

/-- The orbit map `X ↦ (k,t ↦ X q - q X)` at the standard quartet. -/
def orbitL : TitsComplexMatrix →ₗ[ℝ] Var where
  toFun X := fun k t => X * (stdQuartet k t).val - (stdQuartet k t).val * X
  map_add' X Y := by
    funext k t
    simp only [Pi.add_apply, add_mul, mul_add]
    abel
  map_smul' r X := by
    funext k t
    simp only [Pi.smul_apply, Matrix.smul_mul, Matrix.mul_smul, smul_sub, RingHom.id_apply]

abbrev stdFO : Submodule ℝ Var := quartetFirstOrder fun k t => (stdQuartet k t).val

theorem orbit_mem (X : TitsComplexMatrix) (hX : X.conjTranspose = -X) : orbitL X ∈ stdFO :=
  comm_mem _ (fun k t => (stdQuartet k t).2) std_idem std_orth std_sum X hX

theorem phi_orbit (c : Fin 8 → ℝ) : phiL (orbitL (Xmat c)) = c := by
  funext i
  fin_cases i
  · show (orbitL (Xmat c) 0 0 0 1).re = c 0
    simp only [orbitL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Xmat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, qv_0_0_0_0, qv_0_0_0_1, qv_0_0_0_2, qv_0_0_1_0, qv_0_0_1_1, qv_0_0_1_2, qv_0_0_2_0, qv_0_0_2_1, qv_0_0_2_2, qv_0_1_0_0, qv_0_1_0_1, qv_0_1_0_2, qv_0_1_1_0, qv_0_1_1_1, qv_0_1_1_2, qv_0_1_2_0, qv_0_1_2_1, qv_0_1_2_2, qv_1_0_0_0, qv_1_0_0_1, qv_1_0_0_2, qv_1_0_1_0, qv_1_0_1_1, qv_1_0_1_2, qv_1_0_2_0, qv_1_0_2_1, qv_1_0_2_2]
    simp [xa, xb]
  · show (orbitL (Xmat c) 0 0 0 1).im = c 1
    simp only [orbitL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Xmat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, qv_0_0_0_0, qv_0_0_0_1, qv_0_0_0_2, qv_0_0_1_0, qv_0_0_1_1, qv_0_0_1_2, qv_0_0_2_0, qv_0_0_2_1, qv_0_0_2_2, qv_0_1_0_0, qv_0_1_0_1, qv_0_1_0_2, qv_0_1_1_0, qv_0_1_1_1, qv_0_1_1_2, qv_0_1_2_0, qv_0_1_2_1, qv_0_1_2_2, qv_1_0_0_0, qv_1_0_0_1, qv_1_0_0_2, qv_1_0_1_0, qv_1_0_1_1, qv_1_0_1_2, qv_1_0_2_0, qv_1_0_2_1, qv_1_0_2_2]
    simp [xa, xb]
  · show (orbitL (Xmat c) 0 0 0 2).re = c 2
    simp only [orbitL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Xmat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, qv_0_0_0_0, qv_0_0_0_1, qv_0_0_0_2, qv_0_0_1_0, qv_0_0_1_1, qv_0_0_1_2, qv_0_0_2_0, qv_0_0_2_1, qv_0_0_2_2, qv_0_1_0_0, qv_0_1_0_1, qv_0_1_0_2, qv_0_1_1_0, qv_0_1_1_1, qv_0_1_1_2, qv_0_1_2_0, qv_0_1_2_1, qv_0_1_2_2, qv_1_0_0_0, qv_1_0_0_1, qv_1_0_0_2, qv_1_0_1_0, qv_1_0_1_1, qv_1_0_1_2, qv_1_0_2_0, qv_1_0_2_1, qv_1_0_2_2]
    simp [xa, xb]
  · show (orbitL (Xmat c) 0 0 0 2).im = c 3
    simp only [orbitL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Xmat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, qv_0_0_0_0, qv_0_0_0_1, qv_0_0_0_2, qv_0_0_1_0, qv_0_0_1_1, qv_0_0_1_2, qv_0_0_2_0, qv_0_0_2_1, qv_0_0_2_2, qv_0_1_0_0, qv_0_1_0_1, qv_0_1_0_2, qv_0_1_1_0, qv_0_1_1_1, qv_0_1_1_2, qv_0_1_2_0, qv_0_1_2_1, qv_0_1_2_2, qv_1_0_0_0, qv_1_0_0_1, qv_1_0_0_2, qv_1_0_1_0, qv_1_0_1_1, qv_1_0_1_2, qv_1_0_2_0, qv_1_0_2_1, qv_1_0_2_2]
    simp [xa, xb]
  · show (orbitL (Xmat c) 0 1 1 2).re = c 4
    simp only [orbitL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Xmat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, qv_0_0_0_0, qv_0_0_0_1, qv_0_0_0_2, qv_0_0_1_0, qv_0_0_1_1, qv_0_0_1_2, qv_0_0_2_0, qv_0_0_2_1, qv_0_0_2_2, qv_0_1_0_0, qv_0_1_0_1, qv_0_1_0_2, qv_0_1_1_0, qv_0_1_1_1, qv_0_1_1_2, qv_0_1_2_0, qv_0_1_2_1, qv_0_1_2_2, qv_1_0_0_0, qv_1_0_0_1, qv_1_0_0_2, qv_1_0_1_0, qv_1_0_1_1, qv_1_0_1_2, qv_1_0_2_0, qv_1_0_2_1, qv_1_0_2_2]
    simp [xa, xb]
  · show (orbitL (Xmat c) 0 1 1 2).im = c 5
    simp only [orbitL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Xmat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, qv_0_0_0_0, qv_0_0_0_1, qv_0_0_0_2, qv_0_0_1_0, qv_0_0_1_1, qv_0_0_1_2, qv_0_0_2_0, qv_0_0_2_1, qv_0_0_2_2, qv_0_1_0_0, qv_0_1_0_1, qv_0_1_0_2, qv_0_1_1_0, qv_0_1_1_1, qv_0_1_1_2, qv_0_1_2_0, qv_0_1_2_1, qv_0_1_2_2, qv_1_0_0_0, qv_1_0_0_1, qv_1_0_0_2, qv_1_0_1_0, qv_1_0_1_1, qv_1_0_1_2, qv_1_0_2_0, qv_1_0_2_1, qv_1_0_2_2]
    simp [xa, xb]
  · show (orbitL (Xmat c) 1 0 0 1).im = c 6
    simp only [orbitL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Xmat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, qv_0_0_0_0, qv_0_0_0_1, qv_0_0_0_2, qv_0_0_1_0, qv_0_0_1_1, qv_0_0_1_2, qv_0_0_2_0, qv_0_0_2_1, qv_0_0_2_2, qv_0_1_0_0, qv_0_1_0_1, qv_0_1_0_2, qv_0_1_1_0, qv_0_1_1_1, qv_0_1_1_2, qv_0_1_2_0, qv_0_1_2_1, qv_0_1_2_2, qv_1_0_0_0, qv_1_0_0_1, qv_1_0_0_2, qv_1_0_1_0, qv_1_0_1_1, qv_1_0_1_2, qv_1_0_2_0, qv_1_0_2_1, qv_1_0_2_2]
    simp [xa, xb]; ring
  · show (orbitL (Xmat c) 1 0 1 2).im = c 7
    simp only [orbitL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Xmat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, qv_0_0_0_0, qv_0_0_0_1, qv_0_0_0_2, qv_0_0_1_0, qv_0_0_1_1, qv_0_0_1_2, qv_0_0_2_0, qv_0_0_2_1, qv_0_0_2_2, qv_0_1_0_0, qv_0_1_0_1, qv_0_1_0_2, qv_0_1_1_0, qv_0_1_1_1, qv_0_1_1_2, qv_0_1_2_0, qv_0_1_2_1, qv_0_1_2_2, qv_1_0_0_0, qv_1_0_0_1, qv_1_0_0_2, qv_1_0_1_0, qv_1_0_1_1, qv_1_0_1_2, qv_1_0_2_0, qv_1_0_2_1, qv_1_0_2_2]
    simp [xa, xb]; ring

/-! ## Injectivity of the coordinates -/

theorem coreHyp_of_mem (δ : Var) (hδ : δ ∈ stdFO) (hφ : phiL δ = 0) : CoreHyp δ := by
  have hw := win_general _ δ hδ
  obtain ⟨hH, htan, -, hsum, hcross⟩ := hδ
  have c : ∀ i, phiL δ i = 0 := fun i => by rw [hφ]; rfl
  have c0 := c 0
  have c1 := c 1
  have c2 := c 2
  have c3 := c 3
  have c4 := c 4
  have c5 := c 5
  have c6 := c 6
  have c7 := c 7
  simp only [phiL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.head_cons] at c0 c1 c2 c3 c4 c5 c6 c7
  have e01 : δ 0 0 0 1 = 0 := Complex.ext c0 c1
  have e02 : δ 0 0 0 2 = 0 := Complex.ext c2 c3
  have e12 : δ 0 1 1 2 = 0 := Complex.ext c4 c5
  refine ⟨htan, hw, hsum, fun k k' t t' hk => ?_, ?_⟩
  · have hre := hcross k k' t t' hk
    have him : ((stdQuartet k t).val * δ k' t' + δ k t * (stdQuartet k' t').val).trace.im = 0 := by
      rw [Matrix.trace_add, Complex.add_im, herm_trace_im _ _ (stdQuartet k t).2 (hH k' t'),
        herm_trace_im _ _ (hH k t) (stdQuartet k' t').2, add_zero]
    exact Complex.ext hre him
  · have s1 : star (δ 1 0 0 1) = δ 1 0 0 1 := by
      rw [← starRingEnd_apply]; exact Complex.conj_eq_iff_im.mpr c6
    have s2 : star (δ 1 0 1 2) = δ 1 0 1 2 := by
      rw [← starRingEnd_apply]; exact Complex.conj_eq_iff_im.mpr c7
    refine ⟨e01, ?_, e02, ?_, e12, ?_, ?_, ?_⟩
    · rw [← (hH 0 0).apply 1 0, e01, star_zero]
    · rw [← (hH 0 0).apply 2 0, e02, star_zero]
    · rw [← (hH 0 1).apply 2 1, e12, star_zero]
    · rw [← (hH 1 0).apply 1 0, s1]
    · rw [← (hH 1 0).apply 2 1, s2]

/-- Coordinates restricted to the first-order space. -/
def phiR : stdFO →ₗ[ℝ] (Fin 8 → ℝ) := phiL ∘ₗ stdFO.subtype

theorem phiR_injective : Function.Injective phiR := by
  refine (injective_iff_map_eq_zero phiR).mpr fun x hx => ?_
  exact Subtype.ext (core_zero (coreHyp_of_mem x.1 x.2 hx))

theorem phiR_surjective : Function.Surjective phiR := fun c =>
  ⟨⟨orbitL (Xmat c), orbit_mem _ (Xmat_skew c)⟩, phi_orbit c⟩

theorem finrank_std : Module.finrank ℝ stdFO = 8 :=
  (LinearEquiv.ofBijective phiR ⟨phiR_injective, phiR_surjective⟩).finrank_eq.trans
    (Module.finrank_fin_fun ℝ)

/-! ## Unitary conjugation and relabelling -/

/-- The conjugated, relabelled variation. -/
def conjL (g : TitsComplexMatrix) (fperm : Equiv.Perm (Fin 4)) (τ : Fin 4 → Equiv.Perm (Fin 3)) :
    Var →ₗ[ℝ] Var where
  toFun δ := fun k t => g * δ (fperm k) (τ k t) * g.conjTranspose
  map_add' x y := by
    funext k t
    simp only [Pi.add_apply, mul_add, add_mul]
  map_smul' r x := by
    funext k t
    simp only [Pi.smul_apply, Matrix.smul_mul, Matrix.mul_smul, RingHom.id_apply]

theorem conj_mem (q : Var) (g : TitsComplexMatrix) (hg : g * g.conjTranspose = 1)
    (fperm : Equiv.Perm (Fin 4)) (τ : Fin 4 → Equiv.Perm (Fin 3)) (δ : Var)
    (hδ : δ ∈ quartetFirstOrder q) :
    conjL g fperm τ δ ∈ quartetFirstOrder fun k t => g * q (fperm k) (τ k t) * g.conjTranspose := by
  have hg' : g.conjTranspose * g = 1 := mul_eq_one_comm.mp hg
  have hw := win_general q δ hδ
  obtain ⟨hH, htan, -, hsum, hcross⟩ := hδ
  refine ⟨fun k t => ?_, fun k t => ?_, fun k s => ?_, fun k => ?_, fun k k' t t' hk => ?_⟩
  · exact Matrix.isHermitian_mul_mul_conjTranspose g (hH _ _)
  · show g * q (fperm k) (τ k t) * g.conjTranspose * (g * δ (fperm k) (τ k t) * g.conjTranspose) +
        g * δ (fperm k) (τ k t) * g.conjTranspose * (g * q (fperm k) (τ k t) * g.conjTranspose) =
      g * δ (fperm k) (τ k t) * g.conjTranspose
    rw [cmul _ _ _ _ hg', cmul _ _ _ _ hg', ← add_mul, ← mul_add, htan]
  · show g * q (fperm k) (τ k _) * g.conjTranspose * (g * δ (fperm k) (τ k _) * g.conjTranspose) +
        g * δ (fperm k) (τ k _) * g.conjTranspose * (g * q (fperm k) (τ k _) * g.conjTranspose) +
        g * δ (fperm k) (τ k _) * g.conjTranspose * (g * q (fperm k) (τ k _) * g.conjTranspose) +
        g * q (fperm k) (τ k _) * g.conjTranspose * (g * δ (fperm k) (τ k _) * g.conjTranspose) = 0
    rw [cmul _ _ _ _ hg', cmul _ _ _ _ hg', cmul _ _ _ _ hg', cmul _ _ _ _ hg', ← add_mul,
      ← add_mul, ← add_mul, ← mul_add, ← mul_add, ← mul_add,
      hw (fperm k) _ _ ((τ k).injective.ne (pair_ne s)), mul_zero, zero_mul]
  · show ∑ t, g * δ (fperm k) (τ k t) * g.conjTranspose = 0
    rw [← Finset.sum_mul, ← Finset.mul_sum, Equiv.sum_comp (τ k) (fun t => δ (fperm k) t),
      hsum, mul_zero, zero_mul]
  · show (g * q (fperm k) (τ k t) * g.conjTranspose * (g * δ (fperm k') (τ k' t') * g.conjTranspose) +
        g * δ (fperm k) (τ k t) * g.conjTranspose *
          (g * q (fperm k') (τ k' t') * g.conjTranspose)).trace.re = 0
    rw [cmul _ _ _ _ hg', cmul _ _ _ _ hg', ← add_mul, ← mul_add, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, hg', Matrix.one_mul]
    exact hcross _ _ _ _ (fperm.injective.ne hk)

theorem conj_injective (g : TitsComplexMatrix) (hg : g * g.conjTranspose = 1)
    (fperm : Equiv.Perm (Fin 4)) (τ : Fin 4 → Equiv.Perm (Fin 3)) :
    Function.Injective (conjL g fperm τ) := by
  have hg' : g.conjTranspose * g = 1 := mul_eq_one_comm.mp hg
  refine (injective_iff_map_eq_zero _).mpr fun δ hδ => ?_
  funext k' t'
  have e := congrFun (congrFun hδ (fperm.symm k')) ((τ (fperm.symm k')).symm t')
  simp only [conjL, LinearMap.coe_mk, AddHom.coe_mk, Equiv.apply_symm_apply, Pi.zero_apply] at e
  have : δ k' t' = g.conjTranspose * (g * δ k' t' * g.conjTranspose) * g := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg', Matrix.one_mul, Matrix.mul_assoc, hg',
      Matrix.mul_one]
  rw [this, e, Matrix.mul_zero, Matrix.zero_mul]
  rfl

theorem conj_le (q : Var) (g : TitsComplexMatrix) (hg : g * g.conjTranspose = 1)
    (fperm : Equiv.Perm (Fin 4)) (τ : Fin 4 → Equiv.Perm (Fin 3)) :
    Module.finrank ℝ (quartetFirstOrder q) ≤
      Module.finrank ℝ (quartetFirstOrder fun k t => g * q (fperm k) (τ k t) * g.conjTranspose) := by
  let f : quartetFirstOrder q →ₗ[ℝ]
      quartetFirstOrder fun k t => g * q (fperm k) (τ k t) * g.conjTranspose :=
    ((conjL g fperm τ).comp (quartetFirstOrder q).subtype).codRestrict _
      (fun δ => conj_mem q g hg fperm τ δ.1 δ.2)
  refine LinearMap.finrank_le_finrank_of_injective (f := f) fun x y hxy => ?_
  have h := congrArg Subtype.val hxy
  exact Subtype.ext (conj_injective g hg fperm τ h)

theorem finrank_conj (q : Var) (g : TitsComplexMatrix) (hg : g * g.conjTranspose = 1)
    (fperm : Equiv.Perm (Fin 4)) (τ : Fin 4 → Equiv.Perm (Fin 3)) :
    Module.finrank ℝ (quartetFirstOrder fun k t => g * q (fperm k) (τ k t) * g.conjTranspose) =
      Module.finrank ℝ (quartetFirstOrder q) := by
  have hg' : g.conjTranspose * g = 1 := mul_eq_one_comm.mp hg
  refine le_antisymm ?_ (conj_le q g hg fperm τ)
  have h2 := conj_le (fun k t => g * q (fperm k) (τ k t) * g.conjTranspose) g.conjTranspose
    (by rw [Matrix.conjTranspose_conjTranspose]; exact hg') fperm.symm
    (fun k => (τ (fperm.symm k)).symm)
  have e : (fun k t => g.conjTranspose * (g * q (fperm (fperm.symm k))
      (τ (fperm.symm k) ((τ (fperm.symm k)).symm t)) * g.conjTranspose) *
        g.conjTranspose.conjTranspose) = q := by
    funext k t
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hg', Matrix.one_mul, Matrix.mul_assoc, hg',
      Matrix.mul_one]
  rw [e] at h2
  exact h2

end CKM.NativeFirstOrder.QuartetAux

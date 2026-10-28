module

public import A4Slots
public import A4KClassify

@[expose] public section

/-!
# The common Cartan `t = Der(J)^K` and the actual roots of `s`

`commonCartan` is the actual Lie algebra of native Jordan derivations commuting with both `K`
generators. It lies in the ordered diagonal fixer `s` (a `K`-invariant derivation preserves
`J^K = ℝ e₀ ⊕ ℝ e₁ ⊕ ℝ e₂`, and a derivation of three real fields vanishes), is abelian of dimension
four, and is self-centralizing in `s`. Under `psi` (second projection, slot `o12`) it is the span of
the four plane rotations, the skew-adjoint commutant of the `K`-action on `o12`, whose plane characters
`(0,1),(2,1),(2,2),(1,0)` are pairwise distinct up to sign.

The weights `ε_r(h) = ⟨e_{2r+1}, (h (slot12 e_{2r})).o12⟩` are the coordinates of `psi h` in the
plane rotations. The root vectors `sRootX α, sRootY α` (preimages of the bivector root vectors) satisfy
`[h, X_α] = α(h) Y_α`, `[h, Y_α] = −α(h) X_α` in the actual Lie algebra, with `α(h) = ε_r(h) ± ε_s(h)`.
Together with `t` they span `s`. The quotient `s/t` is a real vector-space quotient (`t` is not an
ideal) and is `K`-isomorphic to `⨁_H V_H^3`.
-/

noncomputable section

namespace CKM.NativeIntrinsicTriality

open Glennie CKM.NativeDerivationTriality CKM.NativeFirstOrder

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Helpers: the cube root of unity -/

theorem cart_omega_re : ω.re = -1 / 2 := by
  simp [ω, UnitaryErrorBases.ThreeCycleFourier.omega]

theorem cart_omega_im : ω.im = Real.sqrt 3 / 2 := by
  simp [ω, UnitaryErrorBases.ThreeCycleFourier.omega]

theorem cart_omega_sq : ω ^ 2 = -1 - ω := UnitaryErrorBases.ThreeCycleFourier.omega_sq

theorem cart_omega_cube : ω ^ 3 = 1 := UnitaryErrorBases.ThreeCycleFourier.omega_cube

theorem cart_star_omega : star ω = ω ^ 2 := by
  rw [cart_omega_sq]
  apply Complex.ext
  · simp [cart_omega_re]; norm_num
  · simp [cart_omega_im]

theorem cart_omega_ne_one : ω ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  rw [cart_omega_im, Complex.one_im] at this
  have : Real.sqrt 3 = 0 := by linarith
  simp at this

theorem cart_omega_sq_ne_one : ω ^ 2 ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  rw [cart_omega_sq, Complex.sub_im, Complex.neg_im, Complex.one_im, cart_omega_im] at this
  have : Real.sqrt 3 = 0 := by linarith
  simp at this

theorem cart_omega_pow_mod (n : ℕ) : ω ^ n = ω ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3]
  rw [pow_add, pow_mul, cart_omega_cube, one_pow, mul_one]

theorem cart_omega_pow_eq_one_iff (n : ℕ) : ω ^ n = 1 ↔ n % 3 = 0 := by
  rw [cart_omega_pow_mod]
  have hlt : n % 3 < 3 := Nat.mod_lt n (by norm_num)
  generalize n % 3 = m at hlt ⊢
  interval_cases m
  · simp
  · rw [pow_one]; exact iff_of_false cart_omega_ne_one (by norm_num)
  · exact iff_of_false cart_omega_sq_ne_one (by norm_num)

theorem cart_omegaPow_ne_one_iff (e : Fin 4 → ℕ) (r : Fin 4) : omegaPow e r ≠ 1 ↔ e r % 3 ≠ 0 := by
  rw [omegaPow, Ne, cart_omega_pow_eq_one_iff]

/-- The integer exponent of a root value of `omegaPow e`. -/
def cartRootExp (e : Fin 4 → ℕ) (α : PosRoot) : ℕ :=
  e α.r + if α.plus then e α.s else 2 * e α.s

theorem cart_rootValue_omegaPow (e : Fin 4 → ℕ) (α : PosRoot) :
    rootValue (omegaPow e) α = ω ^ cartRootExp e α := by
  unfold rootValue cartRootExp omegaPow
  split_ifs
  · rw [pow_add]
  · rw [star_pow, cart_star_omega, ← pow_mul, pow_add]

/-! ## Helpers: fixed vectors of plane rotations -/

theorem cart_plane_zero {u v a b : ℝ} (h : (u - 1) ^ 2 + v ^ 2 ≠ 0) (h1 : u * a - v * b = a)
    (h2 : v * a + u * b = b) : a = 0 ∧ b = 0 := by
  constructor
  · have : ((u - 1) ^ 2 + v ^ 2) * a = 0 := by linear_combination (u - 1) * h1 + v * h2
    exact (mul_eq_zero.mp this).resolve_left h
  · have : ((u - 1) ^ 2 + v ^ 2) * b = 0 := by linear_combination (-v) * h1 + (u - 1) * h2
    exact (mul_eq_zero.mp this).resolve_left h

theorem cart_cond_of_ne_one {z : ℂ} (hz : z ≠ 1) : (z.re - 1) ^ 2 + z.im ^ 2 ≠ 0 := by
  intro h
  apply hz
  have : Complex.normSq (z - 1) = 0 := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    linear_combination h
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp this)

theorem cart_planeRot_fixed (z : Fin 4 → ℂ) (x : Octonion) (h : planeRot z x = x) :
    (z 0 ≠ 1 → x.1.re = 0 ∧ x.1.imI = 0) ∧ (z 1 ≠ 1 → x.1.imJ = 0 ∧ x.1.imK = 0) ∧
      (z 2 ≠ 1 → x.2.re = 0 ∧ x.2.imI = 0) ∧ (z 3 ≠ 1 → x.2.imJ = 0 ∧ x.2.imK = 0) := by
  have e : ((⟨(z 0).re * x.1.re - (z 0).im * x.1.imI, (z 0).im * x.1.re + (z 0).re * x.1.imI,
      (z 1).re * x.1.imJ - (z 1).im * x.1.imK, (z 1).im * x.1.imJ + (z 1).re * x.1.imK⟩,
     ⟨(z 2).re * x.2.re - (z 2).im * x.2.imI, (z 2).im * x.2.re + (z 2).re * x.2.imI,
      (z 3).re * x.2.imJ - (z 3).im * x.2.imK, (z 3).im * x.2.imJ + (z 3).re * x.2.imK⟩) :
      Octonion) = x := h
  simp only [Prod.ext_iff, Quaternion.ext_iff] at e
  obtain ⟨⟨e1, e2, e3, e4⟩, ⟨e5, e6, e7, e8⟩⟩ := e
  exact ⟨fun hz => cart_plane_zero (cart_cond_of_ne_one hz) e1 e2,
    fun hz => cart_plane_zero (cart_cond_of_ne_one hz) e3 e4,
    fun hz => cart_plane_zero (cart_cond_of_ne_one hz) e5 e6,
    fun hz => cart_plane_zero (cart_cond_of_ne_one hz) e7 e8⟩

theorem cart_oct_eq_zero_of_fixed (z w : Fin 4 → ℂ) (x : Octonion) (hz : planeRot z x = x)
    (hw : planeRot w x = x) (h : ∀ r, z r ≠ 1 ∨ w r ≠ 1) : x = 0 := by
  obtain ⟨a0, a1, a2, a3⟩ := cart_planeRot_fixed z x hz
  obtain ⟨b0, b1, b2, b3⟩ := cart_planeRot_fixed w x hw
  have c0 := (h 0).elim a0 b0
  have c1 := (h 1).elim a1 b1
  have c2 := (h 2).elim a2 b2
  have c3 := (h 3).elim a3 b3
  apply Prod.ext <;> apply Quaternion.ext <;> simp [c0, c1, c2, c3]

theorem cart_oct_eq_zero_of_fixed_pow (e e' : Fin 4 → ℕ) (x : Octonion)
    (hz : planeRot (omegaPow e) x = x) (hw : planeRot (omegaPow e') x = x)
    (h : ∀ r, e r % 3 ≠ 0 ∨ e' r % 3 ≠ 0) : x = 0 :=
  cart_oct_eq_zero_of_fixed _ _ x hz hw fun r => by
    rw [cart_omegaPow_ne_one_iff, cart_omegaPow_ne_one_iff]; exact h r

/-- The `K`-fixed vectors of the Albert algebra are diagonal. -/
theorem cart_fixed_offdiag (y : Albert) (h0 : R0 y = y) (h1 : R1 y = y) :
    y.o01 = 0 ∧ y.o02 = 0 ∧ y.o12 = 0 := by
  rw [R0_eq_slotwise, slotwise_apply] at h0
  rw [R1_eq_slotwise, slotwise_apply] at h1
  have p0 := congrArg Albert.o01 h0
  have p1 := congrArg Albert.o02 h0
  have p2 := congrArg Albert.o12 h0
  have q0 := congrArg Albert.o01 h1
  have q1 := congrArg Albert.o02 h1
  have q2 := congrArg Albert.o12 h1
  refine ⟨cart_oct_eq_zero_of_fixed_pow _ _ _ p0 q0 (by decide),
    cart_oct_eq_zero_of_fixed_pow _ _ _ p1 q1 (by decide),
    cart_oct_eq_zero_of_fixed_pow _ _ _ p2 q2 (by decide)⟩

/-- A `K`-commuting derivation kills a `K`-fixed idempotent of the diagonal. -/
theorem cart_der_idem_zero {D : Module.End ℝ Albert} (hD : D ∈ jordanDerivations)
    (h0 : R0 * D = D * R0) (h1 : R1 * D = D * R1) :
    D idem0 = 0 ∧ D idem1 = 0 ∧ D idem2 = 0 := by
  have fix : ∀ e : Albert, R0 e = e → R1 e = e →
      R0 (D e) = D e ∧ R1 (D e) = D e := by
    intro e he0 he1
    refine ⟨?_, ?_⟩
    · have := congrArg (fun T : Module.End ℝ Albert => T e) h0
      simp only [Module.End.mul_apply, he0] at this
      exact this
    · have := congrArg (fun T : Module.End ℝ Albert => T e) h1
      simp only [Module.End.mul_apply, he1] at this
      exact this
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨f0, f1⟩ := fix idem0 R0_idem.1 R1_idem.1
    obtain ⟨o1, o2, o3⟩ := cart_fixed_offdiag _ f0 f1
    have e := hD idem0 idem0
    rw [jordan_idem0_idem0, jordan_comm (D idem0) idem0, jordan_idem0_left] at e
    have d0 := congrArg Albert.d0 e
    have d1 := congrArg Albert.d1 e
    have d2 := congrArg Albert.d2 e
    simp only [Albert.add_d0, Albert.add_d1, Albert.add_d2] at d0 d1 d2
    apply Albert.extExplicit <;> simp [o1, o2, o3] <;> linarith
  · obtain ⟨f0, f1⟩ := fix idem1 R0_idem.2.1 R1_idem.2.1
    obtain ⟨o1, o2, o3⟩ := cart_fixed_offdiag _ f0 f1
    have e := hD idem1 idem1
    rw [jordan_idem1_idem1, jordan_comm (D idem1) idem1, jordan_idem1_left] at e
    have d0 := congrArg Albert.d0 e
    have d1 := congrArg Albert.d1 e
    have d2 := congrArg Albert.d2 e
    simp only [Albert.add_d0, Albert.add_d1, Albert.add_d2] at d0 d1 d2
    apply Albert.extExplicit <;> simp [o1, o2, o3] <;> linarith
  · obtain ⟨f0, f1⟩ := fix idem2 R0_idem.2.2 R1_idem.2.2
    obtain ⟨o1, o2, o3⟩ := cart_fixed_offdiag _ f0 f1
    have e := hD idem2 idem2
    rw [jordan_idem2_idem2, jordan_comm (D idem2) idem2, jordan_idem2_left] at e
    have d0 := congrArg Albert.d0 e
    have d1 := congrArg Albert.d1 e
    have d2 := congrArg Albert.d2 e
    simp only [Albert.add_d0, Albert.add_d1, Albert.add_d2] at d0 d1 d2
    apply Albert.extExplicit <;> simp [o1, o2, o3] <;> linarith

/-- `Der(J)^K` as a submodule of endomorphisms. -/
def commonCartanSubmodule : Submodule ℝ (Module.End ℝ Albert) where
  carrier := {D | D ∈ jordanDerivations ∧ R0 * D = D * R0 ∧ R1 * D = D * R1}
  zero_mem' := ⟨jordanDerivations.zero_mem, by rw [mul_zero, zero_mul], by rw [mul_zero, zero_mul]⟩
  add_mem' := by
    rintro D E ⟨hD, a, b⟩ ⟨hE, c, d⟩
    exact ⟨jordanDerivations.add_mem hD hE, by rw [mul_add, add_mul, a, c],
      by rw [mul_add, add_mul, b, d]⟩
  smul_mem' := by
    rintro t D ⟨hD, a, b⟩
    exact ⟨jordanDerivations.smul_mem t hD, by rw [mul_smul_comm, smul_mul_assoc, a],
      by rw [mul_smul_comm, smul_mul_assoc, b]⟩

theorem commutator_mem_commonCartanSubmodule {D E : Module.End ℝ Albert}
    (hD : D ∈ commonCartanSubmodule) (hE : E ∈ commonCartanSubmodule) :
    D * E - E * D ∈ commonCartanSubmodule := by
  obtain ⟨hD, a, b⟩ := hD
  obtain ⟨hE, c, d⟩ := hE
  have a' : Commute R0 D := a
  have b' : Commute R1 D := b
  have c' : Commute R0 E := c
  have d' : Commute R1 E := d
  exact ⟨commutator_mem_derivationSubmodule hD hE, ((a'.mul_right c').sub_right (c'.mul_right a') :),
    ((b'.mul_right d').sub_right (d'.mul_right b') :)⟩

/-- The common Cartan `t = Der(J)^K`, an actual Lie subalgebra (commutator bracket). -/
def commonCartan : LieSubalgebra ℝ (Module.End ℝ Albert) :=
  { commonCartanSubmodule with lie_mem' := fun hD hE => commutator_mem_commonCartanSubmodule hD hE }

theorem mem_commonCartan {D : Module.End ℝ Albert} :
    D ∈ commonCartan ↔ D ∈ jordanDerivations ∧ R0 * D = D * R0 ∧ R1 * D = D * R1 := Iff.rfl

theorem commonCartan_le_diagonalFixer : commonCartan ≤ diagonalFixer := by
  intro D hD
  obtain ⟨hDer, h0, h1⟩ := hD
  exact ⟨hDer, cart_der_idem_zero hDer h0 h1⟩

/-! ## Helpers: the common Cartan through `psi` -/

/-- The two `K` generators on the slot `o12`, as plane-rotation parameters. -/
def cartZ : Fin 2 → Fin 4 → ℂ := ![omegaPow r0Exp, omegaPow (r1Exp 2)]

theorem cartZ_unit : ∀ i r, Complex.normSq (cartZ i r) = 1 := by
  intro i r
  fin_cases i
  · exact omegaPow_unit _ r
  · exact omegaPow_unit _ r

/-- The common fixed space of the two conjugations inside `skewEnd`. -/
def cartFix : Submodule ℝ (Module.End ℝ Octonion) :=
  (⨅ i, fixedSpace (adRot (cartZ i))) ⊓ skewEnd.toSubmodule

theorem cart_comm_iff_conj {g D : Module.End ℝ Albert} (h3 : g ^ 3 = 1) :
    g * D = D * g ↔ g * D * g ^ 2 = D := by
  constructor
  · intro h
    rw [h, mul_assoc, ← pow_succ', h3, mul_one]
  · intro h
    calc g * D = g * D * g ^ 3 := by rw [h3, mul_one]
      _ = (g * D * g ^ 2) * g := by rw [pow_succ, mul_assoc (g * D)]
      _ = D * g := by rw [h]

theorem cart_sAction_g0_eq_iff (D : diagonalFixer) :
    sAction.g0 D = D ↔ R0 * (D : Module.End ℝ Albert) = D * R0 := by
  rw [Subtype.ext_iff, sAction_g0_apply, cart_comm_iff_conj R0_cube]

theorem cart_sAction_g1_eq_iff (D : diagonalFixer) :
    sAction.g1 D = D ↔ R1 * (D : Module.End ℝ Albert) = D * R1 := by
  rw [Subtype.ext_iff, sAction_g1_apply, cart_comm_iff_conj R1_cube]

theorem cart_mem_commonCartan_iff_fixK (D : diagonalFixer) :
    (D : Module.End ℝ Albert) ∈ commonCartan ↔ D ∈ sAction.fixK := by
  rw [mem_commonCartan, KAction.fixK, Submodule.mem_inf, mem_fixedSpace, mem_fixedSpace,
    cart_sAction_g0_eq_iff, cart_sAction_g1_eq_iff]
  exact ⟨fun h => h.2, fun h => ⟨diagonalFixer_le D.2, h⟩⟩

theorem cart_psi_eq_iff {D E : diagonalFixer} :
    D = E ↔ ((psi D : skewEnd) : Module.End ℝ Octonion) = psi E := by
  rw [← Subtype.ext_iff]
  exact psi.injective.eq_iff.symm

theorem cart_fixK_iff_psi (D : diagonalFixer) :
    D ∈ sAction.fixK ↔ ((psi D : skewEnd) : Module.End ℝ Octonion) ∈ cartFix := by
  rw [KAction.fixK, Submodule.mem_inf, mem_fixedSpace, mem_fixedSpace, cartFix, Submodule.mem_inf,
    Submodule.mem_iInf, Fin.forall_fin_two, mem_fixedSpace, mem_fixedSpace, cart_psi_eq_iff,
    cart_psi_eq_iff, psi_sAction_g0, psi_sAction_g1]
  simp only [cartZ, Matrix.cons_val_zero, Matrix.cons_val_one, SetLike.coe_mem, and_true]

theorem cart_no_common_root_exp :
    ∀ α : PosRoot, ¬ (cartRootExp r0Exp α % 3 = 0 ∧ cartRootExp (r1Exp 2) α % 3 = 0) := by
  decide

theorem cart_no_common_root (α : PosRoot) (h : ∀ i, rootValue (cartZ i) α = 1) : False := by
  have h0 := h 0
  have h1 := h 1
  simp only [cartZ, Matrix.cons_val_zero, Matrix.cons_val_one, cart_rootValue_omegaPow,
    cart_omega_pow_eq_one_iff] at h0 h1
  exact cart_no_common_root_exp α ⟨h0, h1⟩

theorem cartFix_eq : cartFix = Submodule.span ℝ (Set.range cartanGen) := by
  rw [cartFix, fixed_adRot_eq cartZ cartZ_unit]
  have hE : {B | ∃ α : PosRoot, (∀ i, rootValue (cartZ i) α = 1) ∧ (B = rootX α ∨ B = rootY α)} =
      (∅ : Set (Module.End ℝ Octonion)) := by
    ext B
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro α hα
    exact (cart_no_common_root α hα).elim
  rw [hE, Set.union_empty]

theorem finrank_cartFix : Module.finrank ℝ cartFix = 4 := by
  have h := finrank_fixed_adRot cartZ cartZ_unit
  have : IsEmpty {α : PosRoot // ∀ i, rootValue (cartZ i) α = 1} :=
    ⟨fun a => cart_no_common_root a.1 a.2⟩
  rw [Nat.card_of_isEmpty, mul_zero, add_zero] at h
  exact h

/-- `psi` followed by the inclusion of `skewEnd`. -/
def cartPsiLin : diagonalFixer →ₗ[ℝ] Module.End ℝ Octonion :=
  skewEnd.incl.toLinearMap ∘ₗ psi.toLinearEquiv.toLinearMap

theorem cartPsiLin_apply (D : diagonalFixer) :
    cartPsiLin D = ((psi D : skewEnd) : Module.End ℝ Octonion) := rfl

theorem cartPsiLin_injective : Function.Injective cartPsiLin := by
  intro D E h
  exact cart_psi_eq_iff.mpr h

/-- Transport of a finrank through `psi`. -/
theorem cart_finrank_eq_of_psi (P : Submodule ℝ diagonalFixer) (Q : Submodule ℝ (Module.End ℝ Octonion))
    (hQ : Q ≤ skewEnd.toSubmodule)
    (h : ∀ D : diagonalFixer, D ∈ P ↔ ((psi D : skewEnd) : Module.End ℝ Octonion) ∈ Q) :
    Module.finrank ℝ P = Module.finrank ℝ Q := by
  have hmap : P.map cartPsiLin = Q := by
    ext B
    constructor
    · rintro ⟨D, hD, rfl⟩
      exact (h D).mp hD
    · intro hB
      have hBs : B ∈ skewEnd := hQ hB
      refine ⟨psi.symm ⟨B, hBs⟩, (h _).mpr ?_, ?_⟩
      · rw [LieEquiv.apply_symm_apply]
        exact hB
      · rw [cartPsiLin_apply, LieEquiv.apply_symm_apply]
  rw [← hmap]
  exact (Submodule.equivMapOfInjective _ cartPsiLin_injective P).finrank_eq

/-- `t` inside `s` (helper copy of `cartanInS`, available before that definition). -/
def cartInS : Submodule ℝ diagonalFixer :=
  Submodule.comap (diagonalFixer.incl : diagonalFixer →ₗ⁅ℝ⁆ Module.End ℝ Albert).toLinearMap
    commonCartan.toSubmodule

theorem cartInS_eq_fixK : cartInS = sAction.fixK := by
  ext D
  exact cart_mem_commonCartan_iff_fixK D

theorem finrank_cartInS : Module.finrank ℝ cartInS = 4 := by
  rw [← finrank_cartFix]
  refine cart_finrank_eq_of_psi _ _ inf_le_right fun D => ?_
  rw [cartInS_eq_fixK, cart_fixK_iff_psi]

/-- `cartInS ≃ commonCartan`. -/
def cartInSEquiv : cartInS ≃ₗ[ℝ] commonCartan where
  toFun D := ⟨D.1.1, D.2⟩
  invFun E := ⟨⟨E.1, commonCartan_le_diagonalFixer E.2⟩, E.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem cart_psi_mem_span_iff (D : diagonalFixer) :
    (D : Module.End ℝ Albert) ∈ commonCartan ↔
      ((psi D : skewEnd) : Module.End ℝ Octonion) ∈ Submodule.span ℝ (Set.range cartanGen) := by
  rw [cart_mem_commonCartan_iff_fixK, cart_fixK_iff_psi, cartFix_eq]

theorem cart_span_cartan_commute {B B' : Module.End ℝ Octonion}
    (hB : B ∈ Submodule.span ℝ (Set.range cartanGen))
    (hB' : B' ∈ Submodule.span ℝ (Set.range cartanGen)) : Commute B B' := by
  have hq : ∀ q, Commute (cartanGen q) B' := by
    intro q
    induction hB' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q', rfl⟩ := hx
      exact cartanGen_comm q q'
    | zero => exact Commute.zero_right _
    | add x y _ _ hx hy => exact hx.add_right hy
    | smul a x _ hx => exact hx.smul_right a
  induction hB using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, rfl⟩ := hx
    exact hq q
  | zero => exact Commute.zero_left _
  | add x y _ _ hx hy => exact hx.add_left hy
  | smul a x _ hx => exact hx.smul_left a

/-- The commutator of `psi D`, `psi E` is the image of the commutator of `D`, `E`. -/
theorem cart_psi_commutator (D E : diagonalFixer) :
    ((psi ⁅D, E⁆ : skewEnd) : Module.End ℝ Octonion) =
      (psi D : Module.End ℝ Octonion) * (psi E : Module.End ℝ Octonion) -
        (psi E : Module.End ℝ Octonion) * (psi D : Module.End ℝ Octonion) := by
  rw [LieEquiv.map_lie, LieSubalgebra.coe_bracket, Ring.lie_def]

theorem cart_coe_commutator (D E : diagonalFixer) :
    ((⁅D, E⁆ : diagonalFixer) : Module.End ℝ Albert) =
      (D : Module.End ℝ Albert) * (E : Module.End ℝ Albert) - (E : Module.End ℝ Albert) * D := by
  rw [LieSubalgebra.coe_bracket, Ring.lie_def]

theorem cart_weight_r (α : PosRoot) : α.weight α.r = 1 := by
  simp [PosRoot.weight, α.2.ne]

theorem cart_comm_sum_smul {ι : Type*} [Fintype ι] (c : ι → ℝ) (v : ι → Module.End ℝ Octonion)
    (T : Module.End ℝ Octonion) :
    T * (∑ i, c i • v i) - (∑ i, c i • v i) * T = ∑ i, c i • (T * v i - v i * T) := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, smul_sub]

/-- Coefficients of `[J_q, ·]` in the root basis. -/
def cartAdCoeff (c : RootIndex → ℝ) (q : Fin 4) : RootIndex → ℝ
  | .inl _ => 0
  | .inr (β, false) => -(((β.weight q : ℤ) : ℝ) * c (.inr (β, true)))
  | .inr (β, true) => ((β.weight q : ℤ) : ℝ) * c (.inr (β, false))

theorem cart_ad_sum (c : RootIndex → ℝ) (q : Fin 4) :
    ∑ i, c i • (cartanGen q * rootFamily i - rootFamily i * cartanGen q) =
      ∑ i, cartAdCoeff c q i • rootFamily i := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, rootFamily,
    cartanGen_comm, sub_self, smul_zero, Finset.sum_const_zero, zero_add, cartan_rootX,
    cartan_rootY, cartAdCoeff, zero_smul]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [smul_neg, smul_smul]
  rw [add_comm, mul_comm (c (.inr (β, false))), mul_comm (c (.inr (β, true)))]
  exact congrArg _ (neg_smul _ _).symm

/-- An element of `skewEnd` commuting with the four plane rotations is in their span. -/
theorem cart_mem_span_cartan_of_comm {B : Module.End ℝ Octonion} (hB : B ∈ skewEnd)
    (hc : ∀ q, cartanGen q * B = B * cartanGen q) : B ∈ Submodule.span ℝ (Set.range cartanGen) := by
  have hB' : B ∈ Submodule.span ℝ (Set.range rootFamily) := by rw [span_rootFamily]; exact hB
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hB'
  have key : ∀ α : PosRoot, c (.inr (α, false)) = 0 ∧ c (.inr (α, true)) = 0 := by
    intro α
    have h0 : cartanGen α.r * (∑ i, c i • rootFamily i) - (∑ i, c i • rootFamily i) * cartanGen α.r
        = 0 := by rw [hc, sub_self]
    rw [cart_comm_sum_smul, cart_ad_sum] at h0
    have hz := Fintype.linearIndependent_iff.mp rootFamily_linearIndependent _ h0
    have h1 := hz (.inr (α, true))
    have h2 := hz (.inr (α, false))
    simp only [cartAdCoeff, cart_weight_r, Int.cast_one, one_mul, neg_eq_zero] at h1 h2
    exact ⟨h1, h2⟩
  refine Submodule.sum_mem _ fun i _ => ?_
  rcases i with q | ⟨α, b⟩
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
  · cases b
    · rw [(key α).1, zero_smul]; exact zero_mem _
    · rw [(key α).2, zero_smul]; exact zero_mem _

theorem commonCartan_abelian {D E : Module.End ℝ Albert} (hD : D ∈ commonCartan) (hE : E ∈ commonCartan) :
    D * E = E * D := by
  have hD' := commonCartan_le_diagonalFixer hD
  have hE' := commonCartan_le_diagonalFixer hE
  have h1 := (cart_psi_mem_span_iff ⟨D, hD'⟩).mp hD
  have h2 := (cart_psi_mem_span_iff ⟨E, hE'⟩).mp hE
  have hc := cart_span_cartan_commute h1 h2
  have h0 : (⁅(⟨D, hD'⟩ : diagonalFixer), ⟨E, hE'⟩⁆ : diagonalFixer) = 0 := by
    apply cart_psi_eq_iff.mpr
    rw [cart_psi_commutator, hc.eq, sub_self, map_zero]
    rfl
  have h3 := congrArg Subtype.val h0
  rw [cart_coe_commutator] at h3
  exact sub_eq_zero.mp h3

theorem commonCartan_selfCentralizing {D : Module.End ℝ Albert} (hD : D ∈ diagonalFixer)
    (hc : ∀ E ∈ commonCartan, D * E = E * D) : D ∈ commonCartan := by
  refine (cart_psi_mem_span_iff ⟨D, hD⟩).mpr ?_
  refine cart_mem_span_cartan_of_comm (psi ⟨D, hD⟩).2 fun q => ?_
  have hE0 : ((psi.symm ⟨cartanGen q, cartanGen_mem q⟩ : diagonalFixer) : Module.End ℝ Albert) ∈
      commonCartan := by
    rw [cart_psi_mem_span_iff, LieEquiv.apply_symm_apply]
    exact Submodule.subset_span ⟨q, rfl⟩
  have h := hc _ hE0
  have h0 : (⁅(⟨D, hD⟩ : diagonalFixer), psi.symm ⟨cartanGen q, cartanGen_mem q⟩⁆ : diagonalFixer)
      = 0 := by
    apply Subtype.ext
    rw [cart_coe_commutator]
    exact sub_eq_zero.mpr h
  have h2 := congrArg (fun X : diagonalFixer => ((psi X : skewEnd) : Module.End ℝ Octonion)) h0
  rw [cart_psi_commutator, LieEquiv.apply_symm_apply, map_zero] at h2
  exact (sub_eq_zero.mp h2).symm

theorem finrank_commonCartan : Module.finrank ℝ commonCartan = 4 := by
  rw [← cartInSEquiv.finrank_eq]
  exact finrank_cartInS

theorem psi_mem_commonCartan_iff (D : diagonalFixer) :
    (D : Module.End ℝ Albert) ∈ commonCartan ↔
      ((psi D : skewEnd) : Module.End ℝ Octonion) ∈ Submodule.span ℝ (Set.range cartanGen) := by
  exact cart_psi_mem_span_iff D

/-- `t` inside `s`. -/
def cartanInS : Submodule ℝ diagonalFixer :=
  Submodule.comap (diagonalFixer.incl : diagonalFixer →ₗ⁅ℝ⁆ Module.End ℝ Albert).toLinearMap
    commonCartan.toSubmodule

theorem mem_cartanInS {D : diagonalFixer} : D ∈ cartanInS ↔ (D : Module.End ℝ Albert) ∈ commonCartan :=
  Iff.rfl

theorem cartanInS_eq_fixK : cartanInS = sAction.fixK := by
  exact cartInS_eq_fixK

/-! ## Weights and root vectors -/

theorem cart_octDot_add_right (a x y : Octonion) : octDot a (x + y) = octDot a x + octDot a y :=
  map_add (octDotForm a) x y

theorem cart_octDot_smul_right (a : Octonion) (t : ℝ) (x : Octonion) :
    octDot a (t • x) = t * octDot a x :=
  map_smul (octDotForm a) t x

theorem cart_octDot_sub_right (a x y : Octonion) : octDot a (x - y) = octDot a x - octDot a y :=
  map_sub (octDotForm a) x y

/-- The weight `ε_r(D) = ⟨e_{2r+1}, (D (slot12 e_{2r})).o12⟩`. -/
def cartanWeight (r : Fin 4) : Module.End ℝ Albert →ₗ[ℝ] ℝ where
  toFun D := octDot (octBasis (planeSnd r)) (D (slot12 (octBasis (planeFst r)))).o12
  map_add' D E := by
    simp only [LinearMap.add_apply, Albert.add_o12]
    exact cart_octDot_add_right _ _ _
  map_smul' t D := by
    simp only [LinearMap.smul_apply, Albert.smul_o12, RingHom.id_apply, smul_eq_mul]
    exact cart_octDot_smul_right _ _ _

/-- The root `α(h) = Σ_q α_q ε_q(h)`. -/
def rootEval (α : PosRoot) (D : Module.End ℝ Albert) : ℝ := ∑ q, ((α.weight q : ℤ) : ℝ) * cartanWeight q D

/-- The plane-`r` coordinate `⟨e_{2r+1}, B e_{2r}⟩` of an octonion endomorphism. -/
def cartWeightLin (r : Fin 4) : Module.End ℝ Octonion →ₗ[ℝ] ℝ where
  toFun B := octDot (octBasis (planeSnd r)) (B (octBasis (planeFst r)))
  map_add' _ _ := cart_octDot_add_right _ _ _
  map_smul' _ _ := cart_octDot_smul_right _ _ _

theorem cart_cartanGen_weight (q r : Fin 4) :
    cartWeightLin r (cartanGen q) = if q = r then 1 else 0 := by
  show octDot _ (cartanGen q _) = _
  rw [cartanGen, wedge_apply, cart_octDot_sub_right, cart_octDot_smul_right, cart_octDot_smul_right,
    octDot_octBasis, octDot_octBasis, octDot_octBasis, octDot_octBasis]
  fin_cases q <;> fin_cases r <;> simp [planeFst, planeSnd]

theorem cart_weightLin_sum (c : Fin 4 → ℝ) (r : Fin 4) :
    cartWeightLin r (∑ q, c q • cartanGen q) = c r := by
  rw [map_sum]
  simp only [map_smul, cart_cartanGen_weight, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq']

theorem cart_cartanWeight_eq (D : diagonalFixer) (r : Fin 4) :
    cartanWeight r (D : Module.End ℝ Albert) = cartWeightLin r ((psi D : skewEnd) : Module.End ℝ Octonion) := by
  show octDot _ _ = octDot _ _
  rw [psi_apply]

theorem psi_commonCartan (D : diagonalFixer) (hD : (D : Module.End ℝ Albert) ∈ commonCartan) :
    ((psi D : skewEnd) : Module.End ℝ Octonion) = ∑ q, cartanWeight q D • cartanGen q := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp ((psi_mem_commonCartan_iff D).mp hD)
  have hw : ∀ r, cartanWeight r (D : Module.End ℝ Albert) = c r := fun r => by
    rw [cart_cartanWeight_eq, ← hc, cart_weightLin_sum]
  rw [← hc]
  exact Finset.sum_congr rfl fun q _ => by rw [hw]

/-- Actual root vectors in `s`. -/
def sRootX (α : PosRoot) : diagonalFixer := psi.symm ⟨rootX α, rootX_mem α⟩
def sRootY (α : PosRoot) : diagonalFixer := psi.symm ⟨rootY α, rootY_mem α⟩

theorem cart_comm_cartan_sum (w : Fin 4 → ℝ) (T : Module.End ℝ Octonion) :
    (∑ q, w q • cartanGen q) * T - T * (∑ q, w q • cartanGen q) =
      ∑ q, w q • (cartanGen q * T - T * cartanGen q) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, smul_sub]

/-- **Actual roots, first vector**: `[h, X_α] = α(h) Y_α` for every `h ∈ t`. -/
theorem commonCartan_bracket_sRootX (α : PosRoot) {h : Module.End ℝ Albert} (hh : h ∈ commonCartan) :
    h * (sRootX α : Module.End ℝ Albert) - (sRootX α : Module.End ℝ Albert) * h =
      rootEval α h • (sRootY α : Module.End ℝ Albert) := by
  have hS := commonCartan_le_diagonalFixer hh
  have key : (⁅(⟨h, hS⟩ : diagonalFixer), sRootX α⁆ : diagonalFixer) = rootEval α h • sRootY α := by
    apply cart_psi_eq_iff.mpr
    rw [cart_psi_commutator, psi_commonCartan ⟨h, hS⟩ hh, map_smul, sRootX,
      sRootY, LieEquiv.apply_symm_apply, LieEquiv.apply_symm_apply]
    show (∑ q, cartanWeight q h • cartanGen q) * rootX α - rootX α * (∑ q, cartanWeight q h • cartanGen q)
      = rootEval α h • rootY α
    rw [cart_comm_cartan_sum, Finset.sum_congr rfl (fun q _ => by rw [cartan_rootX, smul_smul]),
      ← Finset.sum_smul, rootEval]
    congr 1
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _
  have h3 := congrArg Subtype.val key
  rw [cart_coe_commutator] at h3
  exact h3

/-- **Actual roots, second vector**: `[h, Y_α] = −α(h) X_α` for every `h ∈ t`. -/
theorem commonCartan_bracket_sRootY (α : PosRoot) {h : Module.End ℝ Albert} (hh : h ∈ commonCartan) :
    h * (sRootY α : Module.End ℝ Albert) - (sRootY α : Module.End ℝ Albert) * h =
      -(rootEval α h • (sRootX α : Module.End ℝ Albert)) := by
  have hS := commonCartan_le_diagonalFixer hh
  have key : (⁅(⟨h, hS⟩ : diagonalFixer), sRootY α⁆ : diagonalFixer) = -(rootEval α h • sRootX α) := by
    apply cart_psi_eq_iff.mpr
    rw [cart_psi_commutator, psi_commonCartan ⟨h, hS⟩ hh, map_neg, map_smul, sRootX, sRootY, LieEquiv.apply_symm_apply, LieEquiv.apply_symm_apply]
    show (∑ q, cartanWeight q h • cartanGen q) * rootY α - rootY α * (∑ q, cartanWeight q h • cartanGen q)
      = -(rootEval α h • rootX α)
    rw [cart_comm_cartan_sum, Finset.sum_congr rfl (fun q _ => by rw [cartan_rootY, smul_neg, smul_smul]),
      Finset.sum_neg_distrib, ← Finset.sum_smul, rootEval]
    congr 2
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _
  have h3 := congrArg Subtype.val key
  rw [cart_coe_commutator] at h3
  exact h3

/-- Every root is a nonzero functional on `t`. -/
theorem exists_rootEval_ne_zero (α : PosRoot) : ∃ h ∈ commonCartan, rootEval α h ≠ 0 := by
  have hpsi : ((psi (psi.symm ⟨cartanGen α.r, cartanGen_mem α.r⟩) : skewEnd) : Module.End ℝ Octonion)
      = cartanGen α.r := by
    rw [LieEquiv.apply_symm_apply]
  refine ⟨(psi.symm ⟨cartanGen α.r, cartanGen_mem α.r⟩ : diagonalFixer), ?_, ?_⟩
  · rw [psi_mem_commonCartan_iff, hpsi]
    exact Submodule.subset_span ⟨α.r, rfl⟩
  · have hw : ∀ q, cartanWeight q
        ((psi.symm ⟨cartanGen α.r, cartanGen_mem α.r⟩ : diagonalFixer) : Module.End ℝ Albert) =
        if α.r = q then 1 else 0 := fun q => by
      rw [cart_cartanWeight_eq, hpsi, cart_cartanGen_weight]
    rw [rootEval]
    simp only [hw, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      cart_weight_r]
    norm_num

/-- `t` and the 24 root vectors span `s`. -/
theorem cartanInS_sup_roots :
    cartanInS ⊔ Submodule.span ℝ (Set.range sRootX ∪ Set.range sRootY) = ⊤ := by
  set S := cartanInS ⊔ Submodule.span ℝ (Set.range sRootX ∪ Set.range sRootY) with hSdef
  have hskew : ∀ {B : Module.End ℝ Octonion}, B ∈ Submodule.span ℝ (Set.range rootFamily) →
      B ∈ skewEnd := fun hB => by rw [span_rootFamily] at hB; exact hB
  have key : ∀ B (hB : B ∈ Submodule.span ℝ (Set.range rootFamily)), psi.symm ⟨B, hskew hB⟩ ∈ S := by
    intro B hB
    induction hB using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rcases i with q | ⟨β, _ | _⟩
      · apply Submodule.mem_sup_left
        rw [mem_cartanInS, psi_mem_commonCartan_iff, LieEquiv.apply_symm_apply]
        exact Submodule.subset_span ⟨q, rfl⟩
      · apply Submodule.mem_sup_right
        exact Submodule.subset_span (Or.inl ⟨β, rfl⟩)
      · apply Submodule.mem_sup_right
        exact Submodule.subset_span (Or.inr ⟨β, rfl⟩)
    | zero =>
      have e : ∀ h', (⟨0, h'⟩ : skewEnd) = 0 := fun _ => rfl
      rw [e, map_zero]
      exact S.zero_mem
    | add x y hx hy px py =>
      have e : ∀ h', (⟨x + y, h'⟩ : skewEnd) = ⟨x, hskew hx⟩ + ⟨y, hskew hy⟩ := fun _ => rfl
      rw [e, map_add]
      exact S.add_mem px py
    | smul a x hx px =>
      have e : ∀ h', (⟨a • x, h'⟩ : skewEnd) = a • ⟨x, hskew hx⟩ := fun _ => rfl
      rw [e, map_smul]
      exact S.smul_mem a px
  rw [eq_top_iff]
  intro D _
  have hD : ((psi D : skewEnd) : Module.End ℝ Octonion) ∈ Submodule.span ℝ (Set.range rootFamily) := by
    rw [span_rootFamily]; exact (psi D).2
  have h := key _ hD
  rwa [show (⟨((psi D : skewEnd) : Module.End ℝ Octonion), hskew hD⟩ : skewEnd) = psi D from rfl,
    LieEquiv.symm_apply_apply] at h

/-! ## Fixed dimensions in `s` and the quotient `s/t` -/

theorem finrank_sAction_fixK : Module.finrank ℝ sAction.fixK = 4 := by
  rw [← cartanInS_eq_fixK]
  exact finrank_cartInS

/-- Plane exponents of the four subgroup generators on `o12`. -/
def cartEH : Fin 4 → Fin 4 → ℕ :=
  ![r0Exp, r1Exp 2, fun r => 2 * r0Exp r + 2 * r1Exp 2 r, fun r => 2 * r0Exp r + r1Exp 2 r]

theorem cart_omegaPow_mul (a b : Fin 4 → ℕ) : omegaPow a * omegaPow b = omegaPow (a + b) := by
  funext r
  simp only [Pi.mul_apply, omegaPow, Pi.add_apply, pow_add]

theorem cart_adRot_adRot (z w : Fin 4 → ℂ) (B : Module.End ℝ Octonion) :
    adRot z (adRot w B) = adRot (z * w) B := by
  rw [adRot_apply, adRot_apply, adRot_apply, star_mul, ← planeRot_mul, ← planeRot_mul]
  simp only [mul_assoc]

theorem cart_psi_gen (H : Fin 4) (D : diagonalFixer) :
    ((psi (sAction.gen H D) : skewEnd) : Module.End ℝ Octonion) =
      adRot (omegaPow (cartEH H)) (psi D) := by
  fin_cases H
  · exact psi_sAction_g0 D
  · exact psi_sAction_g1 D
  · show ((psi ((sAction.g0 ^ 2 * sAction.g1 ^ 2) D) : skewEnd) : Module.End ℝ Octonion) =
      adRot (omegaPow (cartEH 2)) (psi D)
    rw [pow_two, pow_two, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply,
      psi_sAction_g0, psi_sAction_g0, psi_sAction_g1, psi_sAction_g1]
    simp only [cart_adRot_adRot, cart_omegaPow_mul]
    congr 3
    funext r
    simp [cartEH]
    ring
  · show ((psi ((sAction.g0 ^ 2 * sAction.g1) D) : skewEnd) : Module.End ℝ Octonion) =
      adRot (omegaPow (cartEH 3)) (psi D)
    rw [pow_two, Module.End.mul_apply, Module.End.mul_apply, psi_sAction_g0, psi_sAction_g0,
      psi_sAction_g1]
    simp only [cart_adRot_adRot, cart_omegaPow_mul]
    congr 3
    funext r
    simp [cartEH]
    ring

theorem cart_card_exp :
    ∀ H : Fin 4, Fintype.card {α : PosRoot // cartRootExp (cartEH H) α % 3 = 0} = 3 := by
  decide

theorem cart_card (H : Fin 4) :
    Nat.card {α : PosRoot // ∀ _ : Unit, rootValue (omegaPow (cartEH H)) α = 1} = 3 := by
  have e : {α : PosRoot // ∀ _ : Unit, rootValue (omegaPow (cartEH H)) α = 1} ≃
      {α : PosRoot // cartRootExp (cartEH H) α % 3 = 0} :=
    Equiv.subtypeEquivRight fun α => by
      simp only [forall_const, cart_rootValue_omegaPow, cart_omega_pow_eq_one_iff]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, cart_card_exp]

theorem finrank_sAction_fixH (H : Fin 4) : Module.finrank ℝ (sAction.fixH H) = 10 := by
  have h := finrank_fixed_adRot (fun _ : Unit => omegaPow (cartEH H)) (fun _ r => omegaPow_unit _ r)
  have hP : Module.finrank ℝ (sAction.fixH H) = Module.finrank ℝ
      ↥((⨅ _ : Unit, fixedSpace (adRot (omegaPow (cartEH H)))) ⊓ skewEnd.toSubmodule) :=
    cart_finrank_eq_of_psi _ _ inf_le_right fun D => by
      rw [KAction.fixH, mem_fixedSpace, Submodule.mem_inf, Submodule.mem_iInf, cart_psi_eq_iff,
        cart_psi_gen]
      simp only [mem_fixedSpace, forall_const, SetLike.coe_mem, and_true]
  rw [hP, h, cart_card]

theorem cart_fixK_le_fixH {V : Type*} [AddCommGroup V] [Module ℝ V] (ρ : KAction V) (H : Fin 4) :
    ρ.fixK ≤ ρ.fixH H := by
  intro v hv
  rw [KAction.fixK, Submodule.mem_inf, mem_fixedSpace, mem_fixedSpace] at hv
  rw [KAction.fixH, mem_fixedSpace]
  fin_cases H
  · exact hv.1
  · exact hv.2
  · show (ρ.g0 ^ 2 * ρ.g1 ^ 2) v = v
    simp only [pow_two, Module.End.mul_apply, hv.1, hv.2]
  · show (ρ.g0 ^ 2 * ρ.g1) v = v
    simp only [pow_two, Module.End.mul_apply, hv.1, hv.2]

theorem cartanInS_invariant : sAction.IsInvariant cartanInS := by
  rw [cartanInS_eq_fixK]
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · have h0 := hv
    rw [KAction.fixK, Submodule.mem_inf, mem_fixedSpace] at h0
    rw [h0.1]; exact hv
  · have h1 := hv
    rw [KAction.fixK, Submodule.mem_inf, mem_fixedSpace, mem_fixedSpace] at h1
    rw [h1.2]; exact hv

/-- `K` acting on the vector-space quotient `s/t`. -/
def sQuotAction : KAction (diagonalFixer ⧸ cartanInS) := sAction.quot cartanInS cartanInS_invariant

/-- **`s/t ≃_K ⨁_H V_H^3`.** -/
theorem sQuot_kEquiv : Nonempty (KEquiv sQuotAction (stdAction 0 fun _ => 3)) := by
  have h4 : Module.finrank ℝ cartanInS = 4 := finrank_cartInS
  refine kEquiv_std_of_finrank sQuotAction 0 (fun _ => 3) ?_ ?_
  · have h := finrank_fixK_quot sAction cartanInS cartanInS_invariant
    rw [finrank_fixK_restrict, ← cartanInS_eq_fixK, inf_idem, h4] at h
    show Module.finrank ℝ (sAction.quot cartanInS cartanInS_invariant).fixK = 0
    omega
  · intro H
    have hle : cartanInS ≤ sAction.fixH H := by
      rw [cartanInS_eq_fixK]; exact cart_fixK_le_fixH sAction H
    have h := finrank_fixH_quot sAction cartanInS cartanInS_invariant H
    rw [finrank_fixH_restrict, inf_eq_right.mpr hle, h4, finrank_sAction_fixH] at h
    show Module.finrank ℝ ((sAction.quot cartanInS cartanInS_invariant).fixH H) = 0 + 2 * 3
    omega

end CKM.NativeIntrinsicTriality

#print axioms CKM.NativeIntrinsicTriality.commutator_mem_commonCartanSubmodule
#print axioms CKM.NativeIntrinsicTriality.commonCartan_le_diagonalFixer
#print axioms CKM.NativeIntrinsicTriality.commonCartan_abelian
#print axioms CKM.NativeIntrinsicTriality.commonCartan_selfCentralizing
#print axioms CKM.NativeIntrinsicTriality.finrank_commonCartan
#print axioms CKM.NativeIntrinsicTriality.psi_mem_commonCartan_iff
#print axioms CKM.NativeIntrinsicTriality.cartanInS_eq_fixK
#print axioms CKM.NativeIntrinsicTriality.psi_commonCartan
#print axioms CKM.NativeIntrinsicTriality.commonCartan_bracket_sRootX
#print axioms CKM.NativeIntrinsicTriality.commonCartan_bracket_sRootY
#print axioms CKM.NativeIntrinsicTriality.exists_rootEval_ne_zero
#print axioms CKM.NativeIntrinsicTriality.cartanInS_sup_roots
#print axioms CKM.NativeIntrinsicTriality.finrank_sAction_fixK
#print axioms CKM.NativeIntrinsicTriality.finrank_sAction_fixH
#print axioms CKM.NativeIntrinsicTriality.cartanInS_invariant
#print axioms CKM.NativeIntrinsicTriality.sQuot_kEquiv

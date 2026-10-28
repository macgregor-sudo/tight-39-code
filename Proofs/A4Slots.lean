module

public import A4PlaneRot
public import A3Automorphisms
public import NativeTrialityMain

@[expose] public section

/-!
# The actual `K` generators act slotwise; conjugation actions on derivations

* `R0`, `R1` (A3's native automorphisms, `R1 = T₁ R0 T₁⁻¹`) fix the diagonal and rotate the four
  coordinate planes of each octonion slot: `R0` by `ω^(0,2,2,1)` on every slot, `R1` by
  `ω^(1,0,1,1)`, `ω^(2,2,0,2)`, `ω^(1,1,2,0)` on `o01`, `o02`, `o12`. On the first cyclic Peirce
  slot `o12` the joint exponents are the Peirce weight characters `(0,1),(2,1),(2,2),(1,0)`.
* `K` acts on endomorphisms by conjugation `D ↦ g D g²` (`g³ = 1`); this preserves the native
  Jordan derivations and the ordered diagonal fixer (`derAction`, `sAction`).
* `psi : s ≃ₗ⁅ℝ⁆ skewEnd` is the restriction/extension Lie equivalence followed by the **second**
  projection (the first cyclic slot `E₂₃ = o12`); it intertwines `sAction` with `adRot` of the `o12`
  plane rotations.
* The diagonal splitting `Der ≃ O³ × s` is `K`-equivariant for the slotwise action on `O³`.
-/

noncomputable section

namespace CKM.NativeIntrinsicTriality

open Glennie CKM.NativeDerivationTriality CKM.NativeFirstOrder

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Plane-rotation parameters `ω ^ e r`. -/
def omegaPow (e : Fin 4 → ℕ) : Fin 4 → ℂ := fun r => ω ^ e r

/-- Plane exponents of `R0` (every slot). -/
def r0Exp : Fin 4 → ℕ := ![0, 2, 2, 1]

/-- Plane exponents of `R1` on the slots `o01`, `o02`, `o12`. -/
def r1Exp : Fin 3 → Fin 4 → ℕ := ![![1, 0, 1, 1], ![2, 2, 0, 2], ![1, 1, 2, 0]]

/-- Peirce weight characters of `ε₁, …, ε₄` on the first cyclic slot `o12`. -/
def peirceChar : Fin 4 → ZMod 3 × ZMod 3 := ![(0, 1), (2, 1), (2, 2), (1, 0)]

theorem peirceChar_exponents (r : Fin 4) :
    (peirceChar r).1.val = r0Exp r ∧ (peirceChar r).2.val = r1Exp 2 r := by
  fin_cases r <;> exact ⟨rfl, rfl⟩

theorem ω_re : ω.re = -1 / 2 := omega_re
theorem ω_im : ω.im = Real.sqrt 3 / 2 := omega_im
theorem ω_cube : ω ^ 3 = 1 := UnitaryErrorBases.ThreeCycleFourier.omega_cube

theorem sqrt3_mul_self : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

theorem ω_sq_re : (ω ^ 2).re = -1 / 2 := by
  rw [pow_two, Complex.mul_re, ω_re, ω_im]
  linear_combination (-1 / 4 : ℝ) * sqrt3_mul_self

theorem ω_sq_im : (ω ^ 2).im = -(Real.sqrt 3 / 2) := by
  rw [pow_two, Complex.mul_im, ω_re, ω_im]
  ring

theorem normSq_ω : Complex.normSq ω = 1 := by
  rw [Complex.normSq_apply, ω_re, ω_im]
  linear_combination (1 / 4 : ℝ) * sqrt3_mul_self

theorem star_ω : star ω = ω ^ 2 := by
  apply Complex.ext
  · rw [ω_sq_re, Complex.star_def, Complex.conj_re, ω_re]
  · rw [ω_sq_im, Complex.star_def, Complex.conj_im, ω_im]

theorem omegaPow_unit (e : Fin 4 → ℕ) (r : Fin 4) : Complex.normSq (omegaPow e r) = 1 := by
  rw [omegaPow, map_pow, normSq_ω, one_pow]

/-- A slotwise map: identity on the diagonal, `a, b, c` on `o01, o02, o12`. -/
def slotwise (a b c : Module.End ℝ Octonion) : Module.End ℝ Albert where
  toFun x := ⟨x.d0, x.d1, x.d2, a x.o01, b x.o02, c x.o12⟩
  map_add' x y := by
    apply Albert.extExplicit <;> simp only [Albert.add_d0, Albert.add_d1, Albert.add_d2,
      Albert.add_o01, Albert.add_o02, Albert.add_o12, map_add]
  map_smul' r x := by
    apply Albert.extExplicit <;> simp only [Albert.smul_d0, Albert.smul_d1, Albert.smul_d2,
      Albert.smul_o01, Albert.smul_o02, Albert.smul_o12, map_smul, RingHom.id_apply]

theorem slotwise_apply (a b c : Module.End ℝ Octonion) (x : Albert) :
    slotwise a b c x = ⟨x.d0, x.d1, x.d2, a x.o01, b x.o02, c x.o12⟩ := rfl

theorem omegaPow_zero (e : Fin 4 → ℕ) (r : Fin 4) (h : e r = 0) : omegaPow e r = 1 := by
  rw [omegaPow, h, pow_zero]
theorem omegaPow_one (e : Fin 4 → ℕ) (r : Fin 4) (h : e r = 1) : omegaPow e r = ω := by
  rw [omegaPow, h, pow_one]
theorem omegaPow_two (e : Fin 4 → ℕ) (r : Fin 4) (h : e r = 2) : omegaPow e r = ω ^ 2 := by
  rw [omegaPow, h]

-- (integration) `planeRot_apply` is taken from `A4PlaneRot`.

theorem R0_eq_slotwise :
    R0 = slotwise (planeRot (omegaPow r0Exp)) (planeRot (omegaPow r0Exp)) (planeRot (omegaPow r0Exp)) := by
  have z0 : omegaPow r0Exp 0 = 1 := omegaPow_zero _ _ rfl
  have z1 : omegaPow r0Exp 1 = ω ^ 2 := omegaPow_two _ _ rfl
  have z2 : omegaPow r0Exp 2 = ω ^ 2 := omegaPow_two _ _ rfl
  have z3 : omegaPow r0Exp 3 = ω := omegaPow_one _ _ rfl
  refine LinearMap.ext fun x => ?_
  apply NativePolynomial.upperCoordinateEquiv.injective
  change NativePolynomial.upperCoordinates _ = NativePolynomial.upperCoordinates _
  rw [upper_R0]
  refine fun27_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    simp only [rotc, NativePolynomial.upperCoordinates, slotwise_apply, planeRot_apply, z0, z1, z2, z3,
      ω_re, ω_im, ω_sq_re, ω_sq_im, Complex.one_re, Complex.one_im, Matrix.cons_val, Fin.isValue]
    try ring

-- The shared table list leaves most entries unused in each coordinate goal.
set_option linter.unusedSimpArgs false in
theorem R1_eq_slotwise :
    R1 = slotwise (planeRot (omegaPow (r1Exp 0))) (planeRot (omegaPow (r1Exp 1)))
      (planeRot (omegaPow (r1Exp 2))) := by
  have a0 : omegaPow (r1Exp 0) 0 = ω := omegaPow_one _ _ rfl
  have a1 : omegaPow (r1Exp 0) 1 = 1 := omegaPow_zero _ _ rfl
  have a2 : omegaPow (r1Exp 0) 2 = ω := omegaPow_one _ _ rfl
  have a3 : omegaPow (r1Exp 0) 3 = ω := omegaPow_one _ _ rfl
  have b0 : omegaPow (r1Exp 1) 0 = ω ^ 2 := omegaPow_two _ _ rfl
  have b1 : omegaPow (r1Exp 1) 1 = ω ^ 2 := omegaPow_two _ _ rfl
  have b2 : omegaPow (r1Exp 1) 2 = 1 := omegaPow_zero _ _ rfl
  have b3 : omegaPow (r1Exp 1) 3 = ω ^ 2 := omegaPow_two _ _ rfl
  have c0 : omegaPow (r1Exp 2) 0 = ω := omegaPow_one _ _ rfl
  have c1 : omegaPow (r1Exp 2) 1 = ω := omegaPow_one _ _ rfl
  have c2 : omegaPow (r1Exp 2) 2 = ω ^ 2 := omegaPow_two _ _ rfl
  have c3 : omegaPow (r1Exp 2) 3 = 1 := omegaPow_zero _ _ rfl
  refine LinearMap.ext fun x => ?_
  apply NativePolynomial.upperCoordinateEquiv.injective
  change NativePolynomial.upperCoordinates _ = NativePolynomial.upperCoordinates _
  simp only [R1, LinearMap.comp_apply]
  rw [upper_T0, upper_R0, upper_Ti0]
  refine fun27_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    simp only [TitsS.sgnPerm, T1p_at_0, T1p_at_1, T1p_at_2, T1p_at_3, T1p_at_4, T1p_at_5, T1p_at_6, T1p_at_7, T1p_at_8, T1p_at_9, T1p_at_10, T1p_at_11, T1p_at_12, T1p_at_13, T1p_at_14, T1p_at_15, T1p_at_16, T1p_at_17, T1p_at_18, T1p_at_19, T1p_at_20, T1p_at_21, T1p_at_22, T1p_at_23, T1p_at_24, T1p_at_25, T1p_at_26, T1s_at_0, T1s_at_1, T1s_at_2, T1s_at_3, T1s_at_4, T1s_at_5, T1s_at_6, T1s_at_7, T1s_at_8, T1s_at_9, T1s_at_10, T1s_at_11, T1s_at_12, T1s_at_13, T1s_at_14, T1s_at_15, T1s_at_16, T1s_at_17, T1s_at_18, T1s_at_19, T1s_at_20, T1s_at_21, T1s_at_22, T1s_at_23, T1s_at_24, T1s_at_25, T1s_at_26, T1pinv_at_0, T1pinv_at_1, T1pinv_at_2, T1pinv_at_3, T1pinv_at_4, T1pinv_at_5, T1pinv_at_6, T1pinv_at_7, T1pinv_at_8, T1pinv_at_9, T1pinv_at_10, T1pinv_at_11, T1pinv_at_12, T1pinv_at_13, T1pinv_at_14, T1pinv_at_15, T1pinv_at_16, T1pinv_at_17, T1pinv_at_18, T1pinv_at_19, T1pinv_at_20, T1pinv_at_21, T1pinv_at_22, T1pinv_at_23, T1pinv_at_24, T1pinv_at_25, T1pinv_at_26, T1si_at_0, T1si_at_1, T1si_at_2, T1si_at_3, T1si_at_4, T1si_at_5, T1si_at_6, T1si_at_7, T1si_at_8, T1si_at_9, T1si_at_10, T1si_at_11, T1si_at_12, T1si_at_13, T1si_at_14, T1si_at_15, T1si_at_16, T1si_at_17, T1si_at_18, T1si_at_19, T1si_at_20, T1si_at_21, T1si_at_22, T1si_at_23, T1si_at_24, T1si_at_25, T1si_at_26, rotc_apply_0, rotc_apply_1, rotc_apply_2, rotc_apply_3, rotc_apply_4, rotc_apply_5, rotc_apply_6, rotc_apply_7, rotc_apply_8, rotc_apply_9, rotc_apply_10, rotc_apply_11, rotc_apply_12, rotc_apply_13, rotc_apply_14, rotc_apply_15, rotc_apply_16, rotc_apply_17, rotc_apply_18, rotc_apply_19, rotc_apply_20, rotc_apply_21, rotc_apply_22, rotc_apply_23, rotc_apply_24, rotc_apply_25, rotc_apply_26]
    simp only [NativePolynomial.upperCoordinates, slotwise_apply, planeRot_apply,
      a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3,
      ω_re, ω_im, ω_sq_re, ω_sq_im, Complex.one_re, Complex.one_im, Matrix.cons_val, Fin.isValue]
    try push_cast
    try ring

/-! ## Conjugation actions -/

/-- Conjugation `D ↦ g D g²` (for `g³ = 1` this is `g D g⁻¹`). -/
def conjAct (g : Module.End ℝ Albert) : Module.End ℝ (Module.End ℝ Albert) :=
  LinearMap.mulLeft ℝ g ∘ₗ LinearMap.mulRight ℝ (g ^ 2)

theorem conjAct_apply (g D : Module.End ℝ Albert) : conjAct g D = g * D * g ^ 2 := by
  rw [conjAct, LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, mul_assoc]

theorem end_sq_apply {V : Type*} [AddCommGroup V] [Module ℝ V] (g : Module.End ℝ V) (x : V) :
    (g ^ 2) x = g (g x) := by
  rw [pow_two, Module.End.mul_apply]

theorem end_cube_apply {V : Type*} [AddCommGroup V] [Module ℝ V] {g : Module.End ℝ V}
    (hg3 : g ^ 3 = 1) (x : V) : g (g (g x)) = x := by
  have h := LinearMap.congr_fun hg3 x
  rwa [pow_three, Module.End.mul_apply, Module.End.mul_apply, Module.End.one_apply] at h

theorem conjAct_mem_jordanDerivations {g : Module.End ℝ Albert} (hg : IsNativeAut g) (hg3 : g ^ 3 = 1)
    {D : Module.End ℝ Albert} (hD : D ∈ jordanDerivations) : conjAct g D ∈ jordanDerivations := by
  rw [mem_jordanDerivations] at hD ⊢
  rw [conjAct_apply]
  intro x y
  simp only [Module.End.mul_apply, end_sq_apply, hg.jordan, hD _ _, map_add, end_cube_apply hg3]

theorem slotwise_diag (a b c : Module.End ℝ Octonion) :
    slotwise a b c idem0 = idem0 ∧ slotwise a b c idem1 = idem1 ∧ slotwise a b c idem2 = idem2 := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Albert.extExplicit <;>
    simp only [slotwise_apply, idem0, idem1, idem2, map_zero]

theorem R0_idem : R0 idem0 = idem0 ∧ R0 idem1 = idem1 ∧ R0 idem2 = idem2 := by
  rw [R0_eq_slotwise]; exact slotwise_diag _ _ _

theorem R1_idem : R1 idem0 = idem0 ∧ R1 idem1 = idem1 ∧ R1 idem2 = idem2 := by
  rw [R1_eq_slotwise]; exact slotwise_diag _ _ _

theorem conjAct_mem_diagonalFixer {g : Module.End ℝ Albert} (hg : IsNativeAut g) (hg3 : g ^ 3 = 1)
    (hfix : g idem0 = idem0 ∧ g idem1 = idem1 ∧ g idem2 = idem2)
    {D : Module.End ℝ Albert} (hD : D ∈ diagonalFixer) : conjAct g D ∈ diagonalFixer := by
  obtain ⟨hJ, h0, h1, h2⟩ := mem_diagonalFixer.mp hD
  refine mem_diagonalFixer.mpr ⟨conjAct_mem_jordanDerivations hg hg3 hJ, ?_, ?_, ?_⟩ <;>
    rw [conjAct_apply] <;>
    simp only [Module.End.mul_apply, end_sq_apply, hfix.1, hfix.2.1, hfix.2.2, h0, h1, h2, map_zero]

theorem conjAct_cube {g : Module.End ℝ Albert} (hg3 : g ^ 3 = 1) (D : Module.End ℝ Albert) :
    conjAct g (conjAct g (conjAct g D)) = D := by
  simp only [conjAct_apply]
  have e : g * (g * (g * D * g ^ 2) * g ^ 2) * g ^ 2 = g ^ 3 * D * (g ^ 3 * g ^ 3) := by
    simp only [pow_two, pow_three, mul_assoc]
  rw [e, hg3, one_mul, mul_one, mul_one]

theorem conjAct_comm {g h : Module.End ℝ Albert} (hgh : g * h = h * g) (D : Module.End ℝ Albert) :
    conjAct g (conjAct h D) = conjAct h (conjAct g D) := by
  simp only [conjAct_apply]
  have h2 : h ^ 2 * g ^ 2 = g ^ 2 * h ^ 2 := (Commute.pow_pow (a := g) (b := h) hgh 2 2).eq.symm
  calc g * (h * D * h ^ 2) * g ^ 2 = (g * h) * D * (h ^ 2 * g ^ 2) := by simp only [mul_assoc]
    _ = (h * g) * D * (g ^ 2 * h ^ 2) := by rw [hgh, h2]
    _ = h * (g * D * g ^ 2) * h ^ 2 := by simp only [mul_assoc]

/-- `K` acting on all native Jordan derivations by conjugation with `R0`, `R1`. -/
def derAction : KAction jordanDerivations where
  g0 :=
    { toFun := fun D => ⟨conjAct R0 D, conjAct_mem_jordanDerivations R0_isNativeAut R0_cube D.2⟩
      map_add' := fun D E => Subtype.ext (map_add (conjAct R0) (D : Module.End ℝ Albert) E)
      map_smul' := fun r D => Subtype.ext (map_smul (conjAct R0) r (D : Module.End ℝ Albert)) }
  g1 :=
    { toFun := fun D => ⟨conjAct R1 D, conjAct_mem_jordanDerivations R1_isNativeAut R1_cube D.2⟩
      map_add' := fun D E => Subtype.ext (map_add (conjAct R1) (D : Module.End ℝ Albert) E)
      map_smul' := fun r D => Subtype.ext (map_smul (conjAct R1) r (D : Module.End ℝ Albert)) }
  g0_cube := by
    refine LinearMap.ext fun D => Subtype.ext ?_
    rw [pow_three, Module.End.mul_apply, Module.End.mul_apply, Module.End.one_apply]
    exact conjAct_cube R0_cube D
  g1_cube := by
    refine LinearMap.ext fun D => Subtype.ext ?_
    rw [pow_three, Module.End.mul_apply, Module.End.mul_apply, Module.End.one_apply]
    exact conjAct_cube R1_cube D
  comm := by
    refine LinearMap.ext fun D => Subtype.ext ?_
    rw [Module.End.mul_apply, Module.End.mul_apply]
    exact conjAct_comm R0_mul_R1_comm D

/-- `K` acting on the ordered diagonal fixer `s` by conjugation with `R0`, `R1`. -/
def sAction : KAction diagonalFixer where
  g0 :=
    { toFun := fun D => ⟨conjAct R0 D, conjAct_mem_diagonalFixer R0_isNativeAut R0_cube R0_idem D.2⟩
      map_add' := fun D E => Subtype.ext (map_add (conjAct R0) (D : Module.End ℝ Albert) E)
      map_smul' := fun r D => Subtype.ext (map_smul (conjAct R0) r (D : Module.End ℝ Albert)) }
  g1 :=
    { toFun := fun D => ⟨conjAct R1 D, conjAct_mem_diagonalFixer R1_isNativeAut R1_cube R1_idem D.2⟩
      map_add' := fun D E => Subtype.ext (map_add (conjAct R1) (D : Module.End ℝ Albert) E)
      map_smul' := fun r D => Subtype.ext (map_smul (conjAct R1) r (D : Module.End ℝ Albert)) }
  g0_cube := by
    refine LinearMap.ext fun D => Subtype.ext ?_
    rw [pow_three, Module.End.mul_apply, Module.End.mul_apply, Module.End.one_apply]
    exact conjAct_cube R0_cube D
  g1_cube := by
    refine LinearMap.ext fun D => Subtype.ext ?_
    rw [pow_three, Module.End.mul_apply, Module.End.mul_apply, Module.End.one_apply]
    exact conjAct_cube R1_cube D
  comm := by
    refine LinearMap.ext fun D => Subtype.ext ?_
    rw [Module.End.mul_apply, Module.End.mul_apply]
    exact conjAct_comm R0_mul_R1_comm D

theorem derAction_g0_apply (D : jordanDerivations) :
    ((derAction.g0 D : jordanDerivations) : Module.End ℝ Albert) = R0 * D * R0 ^ 2 := by
  exact conjAct_apply _ _
theorem derAction_g1_apply (D : jordanDerivations) :
    ((derAction.g1 D : jordanDerivations) : Module.End ℝ Albert) = R1 * D * R1 ^ 2 := by
  exact conjAct_apply _ _
theorem sAction_g0_apply (D : diagonalFixer) :
    ((sAction.g0 D : diagonalFixer) : Module.End ℝ Albert) = R0 * D * R0 ^ 2 := by
  exact conjAct_apply _ _
theorem sAction_g1_apply (D : diagonalFixer) :
    ((sAction.g1 D : diagonalFixer) : Module.End ℝ Albert) = R1 * D * R1 ^ 2 := by
  exact conjAct_apply _ _

/-! ## The second-projection triality equivalence on `s` -/

/-- Restriction to the Peirce slots followed by the second projection: `D ↦ (a ↦ (D (slot12 a)).o12)`. -/
def psi : diagonalFixer ≃ₗ⁅ℝ⁆ skewEnd := peirceRestrictionEquiv.trans secondProjEquiv

theorem psi_apply (D : diagonalFixer) (a : Octonion) :
    ((psi D : skewEnd) : Module.End ℝ Octonion) a = ((D : Module.End ℝ Albert) (slot12 a)).o12 := by
  rw [psi, LieEquiv.trans_apply, secondProjEquiv_apply, secondProj_apply, peirceRestrictionEquiv_apply,
    restrictTriple_apply_snd]

theorem slotwise_slot12 (a b c : Module.End ℝ Octonion) (x : Octonion) :
    slotwise a b c (slot12 x) = slot12 (c x) := by
  apply Albert.extExplicit <;> simp only [slotwise_apply, slot12, map_zero]

theorem star_omegaPow (e : Fin 4 → ℕ) (r : Fin 4) :
    star (omegaPow e r) = omegaPow e r * omegaPow e r := by
  rw [omegaPow, star_pow, star_ω, ← pow_mul, ← pow_add, two_mul]

theorem planeRot_star_omegaPow (e : Fin 4 → ℕ) :
    planeRot (star (omegaPow e)) = planeRot (omegaPow e) * planeRot (omegaPow e) := by
  rw [planeRot_mul]
  congr 1
  funext r
  exact star_omegaPow e r

/-- Conjugation by a slotwise automorphism acts on the second projection by `adRot` of the `o12`
rotation. -/
theorem psi_conj_slotwise (a b : Module.End ℝ Octonion) (e : Fin 4 → ℕ) {g : Module.End ℝ Albert}
    (hg : g = slotwise a b (planeRot (omegaPow e))) (D E : diagonalFixer)
    (hE : (E : Module.End ℝ Albert) = g * D * g ^ 2) :
    ((psi E : skewEnd) : Module.End ℝ Octonion) = adRot (omegaPow e) (psi D) := by
  subst hg
  refine LinearMap.ext fun x => ?_
  rw [psi_apply, hE, adRot_apply, planeRot_star_omegaPow]
  simp only [Module.End.mul_apply, end_sq_apply, slotwise_slot12, psi_apply]
  rfl

theorem psi_sAction_g0 (D : diagonalFixer) :
    ((psi (sAction.g0 D) : skewEnd) : Module.End ℝ Octonion) = adRot (omegaPow r0Exp) (psi D) := by
  exact psi_conj_slotwise _ _ _ R0_eq_slotwise D _ (sAction_g0_apply D)

theorem psi_sAction_g1 (D : diagonalFixer) :
    ((psi (sAction.g1 D) : skewEnd) : Module.End ℝ Octonion) = adRot (omegaPow (r1Exp 2)) (psi D) := by
  exact psi_conj_slotwise _ _ _ R1_eq_slotwise D _ (sAction_g1_apply D)

/-! ## Slotwise action on the three diagonal-variation directions -/

theorem omegaPow_cube (e : Fin 4 → ℕ) : omegaPow e * (omegaPow e * omegaPow e) = 1 := by
  funext r
  simp only [Pi.mul_apply, Pi.one_apply, omegaPow]
  calc ω ^ e r * (ω ^ e r * ω ^ e r) = (ω ^ 3) ^ e r := by ring
    _ = 1 := by rw [ω_cube, one_pow]

theorem planeRot_omegaPow_cube_apply (e : Fin 4 → ℕ) (x : Octonion) :
    planeRot (omegaPow e) (planeRot (omegaPow e) (planeRot (omegaPow e) x)) = x := by
  have h : planeRot (omegaPow e) * (planeRot (omegaPow e) * planeRot (omegaPow e)) = 1 := by
    rw [planeRot_mul, planeRot_mul, omegaPow_cube, planeRot_one]
  have := LinearMap.congr_fun h x
  rwa [Module.End.mul_apply, Module.End.mul_apply, Module.End.one_apply] at this

theorem planeRot_comm_apply (z w : Fin 4 → ℂ) (x : Octonion) :
    planeRot z (planeRot w x) = planeRot w (planeRot z x) := by
  rw [← Module.End.mul_apply, planeRot_mul, mul_comm, ← planeRot_mul, Module.End.mul_apply]

/-- `K` acting slotwise on `O³ = (o01, o02, o12)` directions of the diagonal variation. -/
def slotAction : KAction (Octonion × Octonion × Octonion) where
  g0 := LinearMap.prodMap (planeRot (omegaPow r0Exp))
    (LinearMap.prodMap (planeRot (omegaPow r0Exp)) (planeRot (omegaPow r0Exp)))
  g1 := LinearMap.prodMap (planeRot (omegaPow (r1Exp 0)))
    (LinearMap.prodMap (planeRot (omegaPow (r1Exp 1))) (planeRot (omegaPow (r1Exp 2))))
  g0_cube := by
    refine LinearMap.ext fun v => ?_
    simp only [pow_three, Module.End.mul_apply, LinearMap.prodMap_apply, Module.End.one_apply,
      planeRot_omegaPow_cube_apply]
  g1_cube := by
    refine LinearMap.ext fun v => ?_
    simp only [pow_three, Module.End.mul_apply, LinearMap.prodMap_apply, Module.End.one_apply,
      planeRot_omegaPow_cube_apply]
  comm := by
    refine LinearMap.ext fun v => ?_
    simp only [Module.End.mul_apply, LinearMap.prodMap_apply]
    exact Prod.ext (planeRot_comm_apply _ _ _)
      (Prod.ext (planeRot_comm_apply _ _ _) (planeRot_comm_apply _ _ _))

theorem conj_peirceInner {g : Module.End ℝ Albert} (hg : IsNativeAut g) (hg3 : g ^ 3 = 1)
    (v e : Albert) : g * peirceInner v e * g ^ 2 = peirceInner (g v) (g e) := by
  refine LinearMap.ext fun z => ?_
  simp only [Module.End.mul_apply, end_sq_apply, peirceInner_apply, map_smul, map_sub, hg.jordan,
    end_cube_apply hg3]

theorem slotwise_slot01 (a b c : Module.End ℝ Octonion) (x : Octonion) :
    slotwise a b c (slot01 x) = slot01 (a x) := by
  apply Albert.extExplicit <;> simp only [slotwise_apply, slot01, map_zero]

theorem slotwise_slot02 (a b c : Module.End ℝ Octonion) (x : Octonion) :
    slotwise a b c (slot02 x) = slot02 (b x) := by
  apply Albert.extExplicit <;> simp only [slotwise_apply, slot02, map_zero]

/-- Conjugating the inner section by a slotwise automorphism rotates its three arguments. -/
theorem conj_innerSection (a b c : Module.End ℝ Octonion) {g : Module.End ℝ Albert}
    (hg : g = slotwise a b c) (hga : IsNativeAut g) (hg3 : g ^ 3 = 1)
    (v : Octonion × Octonion × Octonion) :
    g * innerSection v * g ^ 2 = innerSection (LinearMap.prodMap a (LinearMap.prodMap b c) v) := by
  rw [innerSection_apply, innerSection_apply, mul_add, mul_add, add_mul, add_mul,
    conj_peirceInner hga hg3, conj_peirceInner hga hg3, conj_peirceInner hga hg3]
  subst hg
  rw [slotwise_slot01, slotwise_slot02, slotwise_slot12, (slotwise_diag a b c).1,
    (slotwise_diag a b c).2.1, LinearMap.prodMap_apply, LinearMap.prodMap_apply]

/-- The diagonal variation of a slotwise conjugate. -/
theorem diagonalVariation_conj (a b c : Module.End ℝ Octonion) {g : Module.End ℝ Albert}
    (hg : g = slotwise a b c) (D : Module.End ℝ Albert) :
    diagonalVariation (g * D * g ^ 2) = LinearMap.prodMap a (LinearMap.prodMap b c) (diagonalVariation D) := by
  subst hg
  rw [diagonalVariation_apply, diagonalVariation_apply, LinearMap.prodMap_apply, LinearMap.prodMap_apply]
  simp only [Module.End.mul_apply, end_sq_apply, (slotwise_diag a b c).1, (slotwise_diag a b c).2.1,
    slotwise_apply]

theorem decomp_conj (a b c : Module.End ℝ Octonion) {g : Module.End ℝ Albert}
    (hg : g = slotwise a b c) (hga : IsNativeAut g) (hg3 : g ^ 3 = 1)
    (D E : jordanDerivations) (hE : (E : Module.End ℝ Albert) = g * D * g ^ 2)
    (F : diagonalFixer) (hF : (F : Module.End ℝ Albert) = g * (derivationDecomposition D).2 * g ^ 2) :
    derivationDecomposition E =
      (LinearMap.prodMap a (LinearMap.prodMap b c) (derivationDecomposition D).1, F) := by
  apply Prod.ext
  · rw [derivationDecomposition_apply_fst, derivationDecomposition_apply_fst, hE,
      diagonalVariation_conj a b c hg]
  · apply Subtype.ext
    rw [derivationDecomposition_apply_snd, hF, derivationDecomposition_apply_snd, hE,
      diagonalVariation_conj a b c hg, ← conj_innerSection a b c hg hga hg3, mul_sub, sub_mul]

/-- The diagonal splitting `Der ≃ O³ × s` is `K`-equivariant. -/
def derDecompKEquiv : KEquiv derAction (slotAction.prod sAction) where
  toLinearEquiv := derivationDecomposition
  map_g0 D := decomp_conj _ _ _ R0_eq_slotwise R0_isNativeAut R0_cube D (derAction.g0 D)
    (derAction_g0_apply D) _ (sAction_g0_apply _)
  map_g1 D := decomp_conj _ _ _ R1_eq_slotwise R1_isNativeAut R1_cube D (derAction.g1 D)
    (derAction_g1_apply D) _ (sAction_g1_apply _)

theorem derDecompKEquiv_toLinearEquiv : derDecompKEquiv.toLinearEquiv = derivationDecomposition := rfl

/-! ## Fixed spaces of the slotwise action -/

/-- The complex coordinate of plane `r` of a native octonion. -/
def planeCoord (r : Fin 4) (x : Octonion) : ℂ :=
  ![⟨x.1.re, x.1.imI⟩, ⟨x.1.imJ, x.1.imK⟩, ⟨x.2.re, x.2.imI⟩, ⟨x.2.imJ, x.2.imK⟩] r

theorem planeCoord_planeRot (z : Fin 4 → ℂ) (r : Fin 4) (x : Octonion) :
    planeCoord r (planeRot z x) = z r * planeCoord r x := by
  fin_cases r <;> apply Complex.ext <;>
    simp [planeCoord, planeRot_apply, Complex.mul_re, Complex.mul_im] <;> ring

theorem planeCoord_zero (r : Fin 4) : planeCoord r 0 = 0 := by
  fin_cases r <;> apply Complex.ext <;> simp [planeCoord]

theorem oct_ext_planeCoord {x y : Octonion} (h : ∀ r, planeCoord r x = planeCoord r y) : x = y := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [planeCoord] at h0 h1 h2 h3
  simp at h0 h1 h2 h3
  exact Prod.ext (Quaternion.ext _ _ h0.1 h0.2 h1.1 h1.2) (Quaternion.ext _ _ h2.1 h2.2 h3.1 h3.2)

/-- The embedding of `ℂ` as plane `q` of the native octonions. -/
def planeEmb (q : Fin 4) : ℂ →ₗ[ℝ] Octonion where
  toFun a := ![(⟨a.re, a.im, 0, 0⟩, 0), (⟨0, 0, a.re, a.im⟩, 0), (0, ⟨a.re, a.im, 0, 0⟩),
    (0, ⟨0, 0, a.re, a.im⟩)] q
  map_add' a b := by
    fin_cases q <;> (apply Prod.ext <;> apply Quaternion.ext) <;> simp
  map_smul' r a := by
    fin_cases q <;> (apply Prod.ext <;> apply Quaternion.ext) <;> simp

theorem planeCoord_planeEmb (r q : Fin 4) (a : ℂ) :
    planeCoord r (planeEmb q a) = if r = q then a else 0 := by
  fin_cases r <;> fin_cases q <;> apply Complex.ext <;> simp [planeCoord, planeEmb]

theorem fixed_planeRot_iff (z : Fin 4 → ℂ) (x : Octonion) :
    planeRot z x = x ↔ ∀ r, z r = 1 ∨ planeCoord r x = 0 := by
  constructor
  · intro h r
    have hr := planeCoord_planeRot z r x
    rw [h] at hr
    have hm : (z r - 1) * planeCoord r x = 0 := by rw [sub_mul, one_mul, ← hr, sub_self]
    rcases mul_eq_zero.mp hm with h' | h'
    · exact Or.inl (sub_eq_zero.mp h')
    · exact Or.inr h'
  · intro h
    apply oct_ext_planeCoord
    intro r
    rw [planeCoord_planeRot]
    rcases h r with h' | h'
    · rw [h', one_mul]
    · rw [h', mul_zero]

theorem fixed_planeRot_single (z : Fin 4 → ℂ) (q : Fin 4) (hz : ∀ r, z r = 1 ↔ r = q) (x : Octonion) :
    planeRot z x = x ↔ x = planeEmb q (planeCoord q x) := by
  constructor
  · intro h
    apply oct_ext_planeCoord
    intro r
    rw [planeCoord_planeEmb]
    split_ifs with hr
    · rw [hr]
    · rcases (fixed_planeRot_iff z x).mp h r with h' | h'
      · exact absurd ((hz r).mp h') hr
      · exact h'
  · intro h
    rw [fixed_planeRot_iff]
    intro r
    by_cases hr : r = q
    · exact Or.inl ((hz r).mpr hr)
    · right
      rw [h, planeCoord_planeEmb, ite_eq_right_iff.mpr (fun h' => absurd h' hr)]

theorem ω_pow_eq_one_iff (n : ℕ) : ω ^ n = 1 ↔ n % 3 = 0 := by
  have key : ω ^ n = ω ^ (n % 3) := by
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, ω_cube, one_pow, one_mul]
  rw [key]
  have hlt : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize n % 3 = m at hlt ⊢
  interval_cases m
  · simp
  · constructor
    · intro h
      have h' := congrArg Complex.re h
      rw [pow_one, ω_re, Complex.one_re] at h'
      norm_num at h'
    · intro h
      exact absurd h (by norm_num)
  · constructor
    · intro h
      have h' := congrArg Complex.re h
      rw [ω_sq_re, Complex.one_re] at h'
      norm_num at h'
    · intro h
      exact absurd h (by norm_num)

theorem omegaPow_eq_one_iff (e : Fin 4 → ℕ) (r : Fin 4) : omegaPow e r = 1 ↔ e r % 3 = 0 :=
  ω_pow_eq_one_iff (e r)

/-- Slotwise products of three plane rotations. -/
def emb3 (qa qb qc : Fin 4) : (ℂ × ℂ × ℂ) →ₗ[ℝ] (Octonion × Octonion × Octonion) :=
  LinearMap.prodMap (planeEmb qa) (LinearMap.prodMap (planeEmb qb) (planeEmb qc))

theorem planeCoord_planeEmb_self (q : Fin 4) (a : ℂ) : planeCoord q (planeEmb q a) = a := by
  rw [planeCoord_planeEmb, ite_eq_left_iff.mpr (fun h' => absurd rfl h')]

theorem emb3_injective (qa qb qc : Fin 4) : Function.Injective (emb3 qa qb qc) := by
  intro w w' h
  simp only [emb3, LinearMap.prodMap_apply, Prod.mk.injEq] at h
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [← planeCoord_planeEmb_self qa w.1, h.1, planeCoord_planeEmb_self]
  · rw [← planeCoord_planeEmb_self qb w.2.1, h.2.1, planeCoord_planeEmb_self]
  · rw [← planeCoord_planeEmb_self qc w.2.2, h.2.2, planeCoord_planeEmb_self]

theorem fixedSpace_prod3 (za zb zc : Fin 4 → ℂ) (qa qb qc : Fin 4) (ha : ∀ r, za r = 1 ↔ r = qa)
    (hb : ∀ r, zb r = 1 ↔ r = qb) (hc : ∀ r, zc r = 1 ↔ r = qc) :
    fixedSpace (LinearMap.prodMap (planeRot za) (LinearMap.prodMap (planeRot zb) (planeRot zc))) =
      LinearMap.range (emb3 qa qb qc) := by
  ext v
  rw [mem_fixedSpace, LinearMap.mem_range]
  constructor
  · intro h
    have h1 : planeRot za v.1 = v.1 := congrArg Prod.fst h
    have h2 : planeRot zb v.2.1 = v.2.1 := congrArg (fun p => p.2.1) h
    have h3 : planeRot zc v.2.2 = v.2.2 := congrArg (fun p => p.2.2) h
    refine ⟨(planeCoord qa v.1, planeCoord qb v.2.1, planeCoord qc v.2.2), ?_⟩
    simp only [emb3, LinearMap.prodMap_apply]
    exact Prod.ext ((fixed_planeRot_single za qa ha _).mp h1).symm
      (Prod.ext ((fixed_planeRot_single zb qb hb _).mp h2).symm
        ((fixed_planeRot_single zc qc hc _).mp h3).symm)
  · rintro ⟨w, rfl⟩
    simp only [emb3, LinearMap.prodMap_apply]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact (fixed_planeRot_single za qa ha _).mpr (by rw [planeCoord_planeEmb_self])
    · exact (fixed_planeRot_single zb qb hb _).mpr (by rw [planeCoord_planeEmb_self])
    · exact (fixed_planeRot_single zc qc hc _).mpr (by rw [planeCoord_planeEmb_self])

theorem finrank_fixed_prod3 (ea eb ec : Fin 4 → ℕ) (qa qb qc : Fin 4)
    (ha : ∀ r, ea r % 3 = 0 ↔ r = qa) (hb : ∀ r, eb r % 3 = 0 ↔ r = qb)
    (hc : ∀ r, ec r % 3 = 0 ↔ r = qc) :
    Module.finrank ℝ (fixedSpace (LinearMap.prodMap (planeRot (omegaPow ea))
      (LinearMap.prodMap (planeRot (omegaPow eb)) (planeRot (omegaPow ec))))) = 6 := by
  rw [fixedSpace_prod3 _ _ _ qa qb qc (fun r => (omegaPow_eq_one_iff ea r).trans (ha r))
    (fun r => (omegaPow_eq_one_iff eb r).trans (hb r)) (fun r => (omegaPow_eq_one_iff ec r).trans (hc r)),
    LinearMap.finrank_range_of_inj (emb3_injective qa qb qc), Module.finrank_prod, Module.finrank_prod,
    Complex.finrank_real_complex]

theorem prodMap3_mul (a b c a' b' c' : Module.End ℝ Octonion) :
    LinearMap.prodMap a (LinearMap.prodMap b c) * LinearMap.prodMap a' (LinearMap.prodMap b' c') =
      LinearMap.prodMap (a * a') (LinearMap.prodMap (b * b') (c * c')) :=
  LinearMap.ext fun _ => rfl

theorem planeRot_omegaPow_mul (e f : Fin 4 → ℕ) :
    planeRot (omegaPow e) * planeRot (omegaPow f) = planeRot (omegaPow (e + f)) := by
  rw [planeRot_mul]
  congr 1
  funext r
  simp only [Pi.mul_apply, omegaPow, Pi.add_apply, pow_add]

theorem slotAction_g0 : slotAction.g0 = LinearMap.prodMap (planeRot (omegaPow r0Exp))
    (LinearMap.prodMap (planeRot (omegaPow r0Exp)) (planeRot (omegaPow r0Exp))) := rfl

theorem slotAction_g1 : slotAction.g1 = LinearMap.prodMap (planeRot (omegaPow (r1Exp 0)))
    (LinearMap.prodMap (planeRot (omegaPow (r1Exp 1))) (planeRot (omegaPow (r1Exp 2)))) := rfl

theorem finrank_slotAction_fixH (H : Fin 4) : Module.finrank ℝ (slotAction.fixH H) = 6 := by
  match H with
  | 0 =>
    change Module.finrank ℝ (fixedSpace slotAction.g0) = 6
    rw [slotAction_g0]
    exact finrank_fixed_prod3 _ _ _ 0 0 0 (by decide) (by decide) (by decide)
  | 1 =>
    change Module.finrank ℝ (fixedSpace slotAction.g1) = 6
    rw [slotAction_g1]
    exact finrank_fixed_prod3 _ _ _ 1 2 3 (by decide) (by decide) (by decide)
  | 2 =>
    change Module.finrank ℝ (fixedSpace (slotAction.g0 ^ 2 * slotAction.g1 ^ 2)) = 6
    rw [slotAction_g0, slotAction_g1, pow_two, pow_two, prodMap3_mul, prodMap3_mul, prodMap3_mul]
    repeat rw [planeRot_omegaPow_mul]
    exact finrank_fixed_prod3 _ _ _ 2 3 1 (by decide) (by decide) (by decide)
  | 3 =>
    change Module.finrank ℝ (fixedSpace (slotAction.g0 ^ 2 * slotAction.g1)) = 6
    rw [slotAction_g0, slotAction_g1, pow_two, prodMap3_mul, prodMap3_mul]
    repeat rw [planeRot_omegaPow_mul]
    exact finrank_fixed_prod3 _ _ _ 3 1 2 (by decide) (by decide) (by decide)

theorem slot_fixed_both_eq_zero (e f : Fin 4 → ℕ) (h : ∀ r, ¬ (e r % 3 = 0 ∧ f r % 3 = 0))
    {x : Octonion} (hx : planeRot (omegaPow e) x = x) (hy : planeRot (omegaPow f) x = x) : x = 0 := by
  apply oct_ext_planeCoord
  intro r
  rw [planeCoord_zero]
  rcases (fixed_planeRot_iff _ _).mp hx r with h1 | h1
  · rcases (fixed_planeRot_iff _ _).mp hy r with h2 | h2
    · exact absurd ⟨(omegaPow_eq_one_iff e r).mp h1, (omegaPow_eq_one_iff f r).mp h2⟩ (h r)
    · exact h2
  · exact h1

theorem slotAction_fixK_eq_bot : slotAction.fixK = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  obtain ⟨h0, h1⟩ := Submodule.mem_inf.mp hv
  rw [mem_fixedSpace, slotAction_g0] at h0
  rw [mem_fixedSpace, slotAction_g1] at h1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact slot_fixed_both_eq_zero r0Exp (r1Exp 0) (by decide) (congrArg Prod.fst h0)
      (congrArg Prod.fst h1)
  · exact slot_fixed_both_eq_zero r0Exp (r1Exp 1) (by decide) (congrArg (fun p => p.2.1) h0)
      (congrArg (fun p => p.2.1) h1)
  · exact slot_fixed_both_eq_zero r0Exp (r1Exp 2) (by decide) (congrArg (fun p => p.2.2) h0)
      (congrArg (fun p => p.2.2) h1)

theorem finrank_slotAction_fixK : Module.finrank ℝ slotAction.fixK = 0 := by
  rw [slotAction_fixK_eq_bot, finrank_bot]

end CKM.NativeIntrinsicTriality

#print axioms CKM.NativeIntrinsicTriality.peirceChar_exponents
#print axioms CKM.NativeIntrinsicTriality.omegaPow_unit
#print axioms CKM.NativeIntrinsicTriality.slotwise
#print axioms CKM.NativeIntrinsicTriality.slotwise_apply
#print axioms CKM.NativeIntrinsicTriality.R0_eq_slotwise
#print axioms CKM.NativeIntrinsicTriality.R1_eq_slotwise
#print axioms CKM.NativeIntrinsicTriality.conjAct_apply
#print axioms CKM.NativeIntrinsicTriality.conjAct_mem_jordanDerivations
#print axioms CKM.NativeIntrinsicTriality.R0_idem
#print axioms CKM.NativeIntrinsicTriality.R1_idem
#print axioms CKM.NativeIntrinsicTriality.conjAct_mem_diagonalFixer
#print axioms CKM.NativeIntrinsicTriality.derAction
#print axioms CKM.NativeIntrinsicTriality.sAction
#print axioms CKM.NativeIntrinsicTriality.derAction_g0_apply
#print axioms CKM.NativeIntrinsicTriality.derAction_g1_apply
#print axioms CKM.NativeIntrinsicTriality.sAction_g0_apply
#print axioms CKM.NativeIntrinsicTriality.sAction_g1_apply
#print axioms CKM.NativeIntrinsicTriality.psi_apply
#print axioms CKM.NativeIntrinsicTriality.psi_sAction_g0
#print axioms CKM.NativeIntrinsicTriality.psi_sAction_g1
#print axioms CKM.NativeIntrinsicTriality.slotAction
#print axioms CKM.NativeIntrinsicTriality.derDecompKEquiv
#print axioms CKM.NativeIntrinsicTriality.derDecompKEquiv_toLinearEquiv
#print axioms CKM.NativeIntrinsicTriality.finrank_slotAction_fixH
#print axioms CKM.NativeIntrinsicTriality.finrank_slotAction_fixK

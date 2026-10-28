module

public import NativeTrialityRelated
public import NativeTrialityPeirce

/-!
# Peirce restriction and extension: diagonal fixer ≃ related triples

A related triple `t = (A, B, C)` extends to an endomorphism of the native Albert algebra that kills
the diagonal and acts on the upper entries `(o01, o02, o12)` by `(A, C, B)`:
`extendTriple t ⟨d0, d1, d2, o01, o02, o12⟩ = ⟨0, 0, 0, A o01, C o02, B o12⟩`.
Skewness and (6.9) give the two other mixed-product identities
`A (z ȳ) = (C z) ȳ + z (B y)‾` and `B (x̄ z) = (A x)‾ z + x̄ (C z)`, so by the native coordinate product
formulas the extension is a Jordan derivation fixing the diagonal. Conversely a diagonal-fixing
derivation preserves the three Peirce slots and restricts to a related triple
`restrictTriple D = (o01 ∘ D ∘ slot01, o12 ∘ D ∘ slot12, o02 ∘ D ∘ slot02)`.
Restriction and extension are inverse, and extension is multiplicative, so this is a Lie equivalence.
-/

@[expose] public section

noncomputable section

namespace CKM.NativeDerivationTriality

open Glennie Reuse

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Pairing helpers (new in this file) -/

theorem restr_octDot_sub_left (x y z : Octonion) : octDot (x - y) z = octDot x z - octDot y z := by
  have h := LinearMap.map_sub₂ octDotForm x y z
  rwa [octDotForm_apply, octDotForm_apply, octDotForm_apply] at h

theorem restr_octDot_sub_right (x y z : Octonion) : octDot x (y - z) = octDot x y - octDot x z := by
  rw [octDot_comm, restr_octDot_sub_left, octDot_comm y, octDot_comm z]

theorem restr_octDot_add_right (x y z : Octonion) : octDot x (y + z) = octDot x y + octDot x z := by
  rw [octDot_comm, octDot_add_left, octDot_comm y, octDot_comm z]

/-- Nondegeneracy of the native positive pairing. -/
theorem restr_octDot_ext {u v : Octonion} (h : ∀ w, octDot u w = octDot v w) : u = v := by
  by_contra hne
  have hpos := octDot_self_pos (sub_ne_zero.mpr hne)
  rw [restr_octDot_sub_left, h, sub_self] at hpos
  exact lt_irrefl _ hpos

/-- Skewness of a member of `skewEnd`, in terms of the native pairing. -/
theorem restr_skew_apply {T : Module.End ℝ Octonion} (hT : T ∈ skewEnd) (x y : Octonion) :
    octDot (T x) y = -octDot x (T y) := by
  change T ∈ octDotForm.skewAdjointSubmodule at hT
  rw [LinearMap.mem_skewAdjointSubmodule] at hT
  have h := hT x y
  rw [Pi.neg_apply, map_neg, octDotForm_apply, octDotForm_apply] at h
  exact h

theorem restr_mem_skewEnd_of {T : Module.End ℝ Octonion}
    (h : ∀ x y, octDot (T x) y = -octDot x (T y)) : T ∈ skewEnd := by
  change T ∈ octDotForm.skewAdjointSubmodule
  rw [LinearMap.mem_skewAdjointSubmodule]
  intro x y
  rw [Pi.neg_apply, map_neg, octDotForm_apply, octDotForm_apply, h]

/-! ## The other two mixed-product identities -/

theorem IsRelatedTriple.mixed_left {t : EndTriple} (ht : IsRelatedTriple t) (z y : Octonion) :
    t.1 (octMul z (octConj y)) = octMul (t.2.2 z) (octConj y) + octMul z (octConj (t.2.1 y)) := by
  obtain ⟨hA, -, hC, hrel⟩ := ht
  apply restr_octDot_ext
  intro w
  have e1 : octDot (t.1 (octMul z (octConj y))) w = -octDot (octMul z (octConj y)) (t.1 w) :=
    restr_skew_apply hA _ _
  have e2 : octDot (octMul z (octConj y)) (t.1 w) = octDot z (octMul (t.1 w) y) := by
    rw [octDot_mul_right_adjoint, octConj_conj]
  have e3 : octMul (t.1 w) y = t.2.2 (octMul w y) - octMul w (t.2.1 y) := by
    rw [hrel, add_sub_cancel_right]
  have e4 : octDot z (t.2.2 (octMul w y)) = -octDot (t.2.2 z) (octMul w y) := by
    rw [octDot_comm, restr_skew_apply hC, octDot_comm]
  have e5 : octDot (octMul (t.2.2 z) (octConj y)) w = octDot (t.2.2 z) (octMul w y) := by
    rw [octDot_mul_right_adjoint, octConj_conj]
  have e6 : octDot (octMul z (octConj (t.2.1 y))) w = octDot z (octMul w (t.2.1 y)) := by
    rw [octDot_mul_right_adjoint, octConj_conj]
  rw [octDot_add_left, e1, e2, e3, restr_octDot_sub_right, e4, e5, e6]
  ring

theorem IsRelatedTriple.mixed_right {t : EndTriple} (ht : IsRelatedTriple t) (x z : Octonion) :
    t.2.1 (octMul (octConj x) z) = octMul (octConj (t.1 x)) z + octMul (octConj x) (t.2.2 z) := by
  obtain ⟨-, hB, hC, hrel⟩ := ht
  apply restr_octDot_ext
  intro w
  have e1 : octDot (t.2.1 (octMul (octConj x) z)) w = -octDot (octMul (octConj x) z) (t.2.1 w) :=
    restr_skew_apply hB _ _
  have e2 : octDot (octMul (octConj x) z) (t.2.1 w) = octDot z (octMul x (t.2.1 w)) := by
    rw [octDot_mul_left_adjoint, octConj_conj]
  have e3 : octMul x (t.2.1 w) = t.2.2 (octMul x w) - octMul (t.1 x) w := by
    rw [hrel, add_sub_cancel_left]
  have e4 : octDot z (t.2.2 (octMul x w)) = -octDot (t.2.2 z) (octMul x w) := by
    rw [octDot_comm, restr_skew_apply hC, octDot_comm]
  have e5 : octDot (octMul (octConj (t.1 x)) z) w = octDot z (octMul (t.1 x) w) := by
    rw [octDot_mul_left_adjoint, octConj_conj]
  have e6 : octDot (octMul (octConj x) (t.2.2 z)) w = octDot (t.2.2 z) (octMul x w) := by
    rw [octDot_mul_left_adjoint, octConj_conj]
  rw [octDot_add_left, e1, e2, e3, restr_octDot_sub_right, e4, e5, e6]
  ring

/-! ## Extension -/

/-- The endomorphism of the native Albert algebra induced by a triple, acting on `(o01, o02, o12)`
by `(A, C, B)` and killing the diagonal. -/
def extendFun (t : EndTriple) (x : Albert) : Albert := ⟨0, 0, 0, t.1 x.o01, t.2.2 x.o02, t.2.1 x.o12⟩

theorem extendFun_add (t : EndTriple) (x y : Albert) : extendFun t (x + y) = extendFun t x + extendFun t y := by
  apply Albert.extExplicit <;> simp [extendFun]

theorem extendFun_smul (t : EndTriple) (r : ℝ) (x : Albert) : extendFun t (r • x) = r • extendFun t x := by
  apply Albert.extExplicit <;> simp [extendFun]

theorem extendFun_add_triple (s t : EndTriple) (x : Albert) :
    extendFun (s + t) x = extendFun s x + extendFun t x := by
  apply Albert.extExplicit <;> simp [extendFun]

theorem extendFun_smul_triple (r : ℝ) (t : EndTriple) (x : Albert) :
    extendFun (r • t) x = r • extendFun t x := by
  apply Albert.extExplicit <;> simp [extendFun]

/-- Extension of triples, as a real-linear map into the endomorphisms of the native Albert algebra. -/
def extendTriple : EndTriple →ₗ[ℝ] Module.End ℝ Albert where
  toFun t :=
    { toFun := extendFun t
      map_add' := extendFun_add t
      map_smul' := extendFun_smul t }
  map_add' s t := LinearMap.ext fun x => extendFun_add_triple s t x
  map_smul' r t := LinearMap.ext fun x => extendFun_smul_triple r t x

/-- The upper-slot order of the extension: `(o01, o02, o12) ↦ (A o01, C o02, B o12)`. -/
theorem extendTriple_apply (t : EndTriple) (x : Albert) :
    extendTriple t x = ⟨0, 0, 0, t.1 x.o01, t.2.2 x.o02, t.2.1 x.o12⟩ := rfl

/-- Extension is multiplicative, hence preserves commutators. -/
theorem extendTriple_mul (s t : EndTriple) : extendTriple (s * t) = extendTriple s * extendTriple t := by
  apply LinearMap.ext
  intro x
  apply Albert.extExplicit <;> simp [extendTriple_apply]

theorem extendTriple_lie (s t : EndTriple) : extendTriple ⁅s, t⁆ = ⁅extendTriple s, extendTriple t⁆ := by
  rw [Ring.lie_def, Ring.lie_def, map_sub, extendTriple_mul, extendTriple_mul]

/-- The extension of a related triple satisfies the native Leibniz rule. -/
theorem extendTriple_isJordanDerivation {t : EndTriple} (ht : IsRelatedTriple t) :
    IsJordanDerivation (extendTriple t) := by
  have hl := ht.mixed_left
  have hr := ht.mixed_right
  obtain ⟨hA, hB, hC, hrel⟩ := ht
  intro x y
  apply Albert.extExplicit
  · simp only [extendTriple_apply, Albert.add_d0, jordan_d0, zero_mul, mul_zero, zero_add]
    rw [restr_skew_apply hA, restr_skew_apply hC]
    ring
  · simp only [extendTriple_apply, Albert.add_d1, jordan_d1, zero_mul, mul_zero, zero_add]
    rw [restr_skew_apply hA, restr_skew_apply hB]
    ring
  · simp only [extendTriple_apply, Albert.add_d2, jordan_d2, zero_mul, mul_zero, zero_add]
    rw [restr_skew_apply hC, restr_skew_apply hB]
    ring
  · simp only [extendTriple_apply, Albert.add_o01, jordan_o01, map_smul, map_add, hl, add_zero,
      zero_add, zero_smul]
    module
  · simp only [extendTriple_apply, Albert.add_o02, jordan_o02, map_smul, map_add, hrel, add_zero,
      zero_add, zero_smul]
    module
  · simp only [extendTriple_apply, Albert.add_o12, jordan_o12, map_smul, map_add, hr, add_zero,
      zero_add, zero_smul]
    module

theorem extendTriple_mem {t : EndTriple} (ht : t ∈ relatedTriples) : extendTriple t ∈ diagonalFixer := by
  rw [mem_diagonalFixer]
  refine ⟨extendTriple_isJordanDerivation ht, ?_, ?_, ?_⟩ <;>
    apply Albert.extExplicit <;> simp [extendTriple_apply, idem0, idem1, idem2]

/-! ## Restriction -/

theorem restr_slot01_add (a b : Octonion) : slot01 (a + b) = slot01 a + slot01 b := by
  apply Albert.extExplicit <;> simp [slot01]
theorem restr_slot02_add (a b : Octonion) : slot02 (a + b) = slot02 a + slot02 b := by
  apply Albert.extExplicit <;> simp [slot02]
theorem restr_slot12_add (a b : Octonion) : slot12 (a + b) = slot12 a + slot12 b := by
  apply Albert.extExplicit <;> simp [slot12]
theorem restr_slot01_smul (r : ℝ) (a : Octonion) : slot01 (r • a) = r • slot01 a := by
  apply Albert.extExplicit <;> simp [slot01]
theorem restr_slot02_smul (r : ℝ) (a : Octonion) : slot02 (r • a) = r • slot02 a := by
  apply Albert.extExplicit <;> simp [slot02]
theorem restr_slot12_smul (r : ℝ) (a : Octonion) : slot12 (r • a) = r • slot12 a := by
  apply Albert.extExplicit <;> simp [slot12]

/-- Restriction of an endomorphism to the three Peirce slots, in the triple order `(A, B, C)` =
`(slot01, slot12, slot02)`. -/
def restrictFun (D : Module.End ℝ Albert) : EndTriple :=
  ({ toFun := fun a => (D (slot01 a)).o01, map_add' := by intro a b; simp only [restr_slot01_add, map_add, Albert.add_o01], map_smul' := by intro r a; simp only [restr_slot01_smul, map_smul, Albert.smul_o01, RingHom.id_apply] },
   { toFun := fun a => (D (slot12 a)).o12, map_add' := by intro a b; simp only [restr_slot12_add, map_add, Albert.add_o12], map_smul' := by intro r a; simp only [restr_slot12_smul, map_smul, Albert.smul_o12, RingHom.id_apply] },
   { toFun := fun a => (D (slot02 a)).o02, map_add' := by intro a b; simp only [restr_slot02_add, map_add, Albert.add_o02], map_smul' := by intro r a; simp only [restr_slot02_smul, map_smul, Albert.smul_o02, RingHom.id_apply] })

/-- Restriction as a real-linear map. -/
def restrictTriple : Module.End ℝ Albert →ₗ[ℝ] EndTriple where
  toFun := restrictFun
  map_add' := by
    intro D E
    refine Prod.ext (LinearMap.ext fun a => rfl) (Prod.ext (LinearMap.ext fun a => rfl)
      (LinearMap.ext fun a => rfl))
  map_smul' := by
    intro r D
    refine Prod.ext (LinearMap.ext fun a => rfl) (Prod.ext (LinearMap.ext fun a => rfl)
      (LinearMap.ext fun a => rfl))

theorem restrictTriple_apply_fst (D : Module.End ℝ Albert) (a : Octonion) :
    (restrictTriple D).1 a = (D (slot01 a)).o01 := rfl
theorem restrictTriple_apply_snd (D : Module.End ℝ Albert) (a : Octonion) :
    (restrictTriple D).2.1 a = (D (slot12 a)).o12 := rfl
theorem restrictTriple_apply_thd (D : Module.End ℝ Albert) (a : Octonion) :
    (restrictTriple D).2.2 a = (D (slot02 a)).o02 := rfl

/-- Half-eigenvector equation for a diagonal-fixing derivation. -/
theorem restr_fixer_half {D : Module.End ℝ Albert} (hD : D ∈ diagonalFixer) {e s : Albert}
    (he : D e = 0) (hs : jordan e s = (1/2 : ℝ) • s) : (1/2 : ℝ) • D s = jordan e (D s) := by
  have h := (mem_diagonalFixer.mp hD).1 e s
  rw [hs, map_smul, he, jordan_zero_left, zero_add] at h
  exact h

theorem restr_idem0_slot01 (a : Octonion) : jordan idem0 (slot01 a) = (1/2 : ℝ) • slot01 a := by
  rw [jordan_idem0_left]; apply Albert.extExplicit <;> simp [slot01]
theorem restr_idem1_slot01 (a : Octonion) : jordan idem1 (slot01 a) = (1/2 : ℝ) • slot01 a := by
  rw [jordan_idem1_left]; apply Albert.extExplicit <;> simp [slot01]
theorem restr_idem0_slot02 (a : Octonion) : jordan idem0 (slot02 a) = (1/2 : ℝ) • slot02 a := by
  rw [jordan_idem0_left]; apply Albert.extExplicit <;> simp [slot02]
theorem restr_idem2_slot02 (a : Octonion) : jordan idem2 (slot02 a) = (1/2 : ℝ) • slot02 a := by
  rw [jordan_idem2_left]; apply Albert.extExplicit <;> simp [slot02]
theorem restr_idem1_slot12 (a : Octonion) : jordan idem1 (slot12 a) = (1/2 : ℝ) • slot12 a := by
  rw [jordan_idem1_left]; apply Albert.extExplicit <;> simp [slot12]
theorem restr_idem2_slot12 (a : Octonion) : jordan idem2 (slot12 a) = (1/2 : ℝ) • slot12 a := by
  rw [jordan_idem2_left]; apply Albert.extExplicit <;> simp [slot12]

theorem restr_half_smul_eq_zero {a : Octonion} (h : (1/2 : ℝ) • a = 0) : a = 0 :=
  (smul_eq_zero.mp h).resolve_left (by norm_num)

/-- A diagonal-fixing derivation maps each Peirce slot into itself. -/
theorem diagonalFixer_map_slot01 {D : Module.End ℝ Albert} (hD : D ∈ diagonalFixer) (a : Octonion) :
    D (slot01 a) = slot01 ((D (slot01 a)).o01) := by
  obtain ⟨-, h0, h1, -⟩ := mem_diagonalFixer.mp hD
  have e0 := restr_fixer_half hD h0 (restr_idem0_slot01 a)
  have e1 := restr_fixer_half hD h1 (restr_idem1_slot01 a)
  rw [jordan_idem0_left] at e0
  rw [jordan_idem1_left] at e1
  generalize D (slot01 a) = y at e0 e1 ⊢
  have hd0 := congrArg Albert.d0 e0
  have hd1 := congrArg Albert.d1 e0
  have hd2 := congrArg Albert.d2 e0
  have ho12 := congrArg Albert.o12 e0
  have ho02 := congrArg Albert.o02 e1
  simp only [Albert.smul_d0, Albert.smul_d1, Albert.smul_d2, Albert.smul_o12, Albert.smul_o02]
    at hd0 hd1 hd2 ho12 ho02
  apply Albert.extExplicit <;> simp only [slot01]
  · linarith
  · linarith
  · linarith
  · exact restr_half_smul_eq_zero ho02
  · exact restr_half_smul_eq_zero ho12

theorem diagonalFixer_map_slot02 {D : Module.End ℝ Albert} (hD : D ∈ diagonalFixer) (a : Octonion) :
    D (slot02 a) = slot02 ((D (slot02 a)).o02) := by
  obtain ⟨-, h0, -, h2⟩ := mem_diagonalFixer.mp hD
  have e0 := restr_fixer_half hD h0 (restr_idem0_slot02 a)
  have e2 := restr_fixer_half hD h2 (restr_idem2_slot02 a)
  rw [jordan_idem0_left] at e0
  rw [jordan_idem2_left] at e2
  generalize D (slot02 a) = y at e0 e2 ⊢
  have hd0 := congrArg Albert.d0 e0
  have hd1 := congrArg Albert.d1 e0
  have hd2 := congrArg Albert.d2 e0
  have ho12 := congrArg Albert.o12 e0
  have ho01 := congrArg Albert.o01 e2
  simp only [Albert.smul_d0, Albert.smul_d1, Albert.smul_d2, Albert.smul_o12, Albert.smul_o01]
    at hd0 hd1 hd2 ho12 ho01
  apply Albert.extExplicit <;> simp only [slot02]
  · linarith
  · linarith
  · linarith
  · exact restr_half_smul_eq_zero ho01
  · exact restr_half_smul_eq_zero ho12

theorem diagonalFixer_map_slot12 {D : Module.End ℝ Albert} (hD : D ∈ diagonalFixer) (a : Octonion) :
    D (slot12 a) = slot12 ((D (slot12 a)).o12) := by
  obtain ⟨-, -, h1, h2⟩ := mem_diagonalFixer.mp hD
  have e1 := restr_fixer_half hD h1 (restr_idem1_slot12 a)
  have e2 := restr_fixer_half hD h2 (restr_idem2_slot12 a)
  rw [jordan_idem1_left] at e1
  rw [jordan_idem2_left] at e2
  generalize D (slot12 a) = y at e1 e2 ⊢
  have hd0 := congrArg Albert.d0 e1
  have hd1 := congrArg Albert.d1 e1
  have hd2 := congrArg Albert.d2 e1
  have ho02 := congrArg Albert.o02 e1
  have ho01 := congrArg Albert.o01 e2
  simp only [Albert.smul_d0, Albert.smul_d1, Albert.smul_d2, Albert.smul_o02, Albert.smul_o01]
    at hd0 hd1 hd2 ho02 ho01
  apply Albert.extExplicit <;> simp only [slot12]
  · linarith
  · linarith
  · linarith
  · exact restr_half_smul_eq_zero ho01
  · exact restr_half_smul_eq_zero ho02

/-- A diagonal-fixing map kills every diagonal element. -/
theorem restr_fixer_diagonal {D : Module.End ℝ Albert} (hD : D ∈ diagonalFixer) (c₀ c₁ c₂ : ℝ) :
    D (diagonal c₀ c₁ c₂) = 0 := by
  obtain ⟨-, h0, h1, h2⟩ := mem_diagonalFixer.mp hD
  have e : diagonal c₀ c₁ c₂ = c₀ • idem0 + c₁ • idem1 + c₂ • idem2 := by
    apply Albert.extExplicit <;> simp [diagonal, idem0, idem1, idem2]
  rw [e, map_add, map_add, map_smul, map_smul, map_smul, h0, h1, h2]
  simp

theorem restrictTriple_mem {D : Module.End ℝ Albert} (hD : D ∈ diagonalFixer) :
    restrictTriple D ∈ relatedTriples := by
  have hJ := (mem_diagonalFixer.mp hD).1
  rw [mem_relatedTriples]
  refine ⟨restr_mem_skewEnd_of ?_, restr_mem_skewEnd_of ?_, restr_mem_skewEnd_of ?_, ?_⟩
  · intro a b
    show octDot (D (slot01 a)).o01 b = -octDot a (D (slot01 b)).o01
    have h := hJ (slot01 a) (slot01 b)
    rw [jordan_slot01_slot01, restr_fixer_diagonal hD, diagonalFixer_map_slot01 hD a,
      diagonalFixer_map_slot01 hD b, jordan_slot01_slot01, jordan_slot01_slot01] at h
    have h' := congrArg Albert.d0 h
    simp only [Albert.add_d0, diagonal, Albert.zero_d0] at h'
    linarith
  · intro a b
    show octDot (D (slot12 a)).o12 b = -octDot a (D (slot12 b)).o12
    have h := hJ (slot12 a) (slot12 b)
    rw [jordan_slot12_slot12, restr_fixer_diagonal hD, diagonalFixer_map_slot12 hD a,
      diagonalFixer_map_slot12 hD b, jordan_slot12_slot12, jordan_slot12_slot12] at h
    have h' := congrArg Albert.d1 h
    simp only [Albert.add_d1, diagonal, Albert.zero_d1] at h'
    linarith
  · intro a b
    show octDot (D (slot02 a)).o02 b = -octDot a (D (slot02 b)).o02
    have h := hJ (slot02 a) (slot02 b)
    rw [jordan_slot02_slot02, restr_fixer_diagonal hD, diagonalFixer_map_slot02 hD a,
      diagonalFixer_map_slot02 hD b, jordan_slot02_slot02, jordan_slot02_slot02] at h
    have h' := congrArg Albert.d0 h
    simp only [Albert.add_d0, diagonal, Albert.zero_d0] at h'
    linarith
  · intro x y
    show (D (slot02 (octMul x y))).o02 =
      octMul (D (slot01 x)).o01 y + octMul x (D (slot12 y)).o12
    have h := hJ (slot01 x) (slot12 y)
    rw [jordan_slot01_slot12, diagonalFixer_map_slot01 hD x, diagonalFixer_map_slot12 hD y,
      jordan_slot01_slot12, jordan_slot01_slot12, restr_slot02_smul, map_smul] at h
    have h' := congrArg Albert.o02 h
    simp only [Albert.smul_o02, Albert.add_o02, slot02] at h'
    rw [← smul_add] at h'
    exact smul_right_injective Octonion (by norm_num : (1/2 : ℝ) ≠ 0) h'

/-! ## The two inverse laws and the Lie equivalence -/

theorem restrictTriple_extendTriple {t : EndTriple} (ht : t ∈ relatedTriples) :
    restrictTriple (extendTriple t) = t := by
  -- The inverse law holds componentwise by definition; membership is not needed.
  exact (fun _ => Prod.ext (LinearMap.ext fun _ => rfl) (Prod.ext (LinearMap.ext fun _ => rfl)
    (LinearMap.ext fun _ => rfl))) ht

theorem extendTriple_restrictTriple {D : Module.End ℝ Albert} (hD : D ∈ diagonalFixer) :
    extendTriple (restrictTriple D) = D := by
  obtain ⟨-, h0, h1, h2⟩ := mem_diagonalFixer.mp hD
  apply LinearMap.ext
  intro x
  conv_rhs => rw [albert_decomposition x]
  simp only [map_add, map_smul, h0, h1, h2, smul_zero, zero_add]
  rw [diagonalFixer_map_slot01 hD, diagonalFixer_map_slot02 hD, diagonalFixer_map_slot12 hD]
  apply Albert.extExplicit <;>
    simp [extendTriple_apply, slot01, slot02, slot12, restrictTriple_apply_fst,
      restrictTriple_apply_snd, restrictTriple_apply_thd]

/-- Extension as a Lie homomorphism from related triples to the diagonal fixer. -/
def extendLieHom : relatedTriples →ₗ⁅ℝ⁆ diagonalFixer where
  toFun t := ⟨extendTriple t, extendTriple_mem t.2⟩
  map_add' _ _ := Subtype.ext (map_add extendTriple _ _)
  map_smul' r _ := Subtype.ext (map_smul extendTriple r _)
  map_lie' {s t} := Subtype.ext (extendTriple_lie s t)

theorem extendLieHom_bijective : Function.Bijective extendLieHom := by
  constructor
  · intro s t hst
    have h : extendTriple (s : EndTriple) = extendTriple (t : EndTriple) := congrArg Subtype.val hst
    apply Subtype.ext
    have h' := congrArg restrictTriple h
    rwa [restrictTriple_extendTriple s.2, restrictTriple_extendTriple t.2] at h'
  · intro D
    exact ⟨⟨restrictTriple D, restrictTriple_mem D.2⟩, Subtype.ext (extendTriple_restrictTriple D.2)⟩

/-- Peirce restriction is a Lie equivalence from the ordered diagonal fixer onto the related
infinitesimal triples; its inverse is extension. -/
def peirceRestrictionEquiv : diagonalFixer ≃ₗ⁅ℝ⁆ relatedTriples :=
  (LieEquiv.ofBijective extendLieHom extendLieHom_bijective).symm

theorem peirceRestrictionEquiv_apply (D : diagonalFixer) :
    (peirceRestrictionEquiv D : EndTriple) = restrictTriple D := by
  have h : extendTriple (peirceRestrictionEquiv D : EndTriple) = (D : Module.End ℝ Albert) :=
    congrArg Subtype.val ((LieEquiv.ofBijective extendLieHom extendLieHom_bijective).apply_symm_apply D)
  rw [← h, restrictTriple_extendTriple (peirceRestrictionEquiv D).2]

theorem peirceRestrictionEquiv_symm_apply (t : relatedTriples) :
    (peirceRestrictionEquiv.symm t : Module.End ℝ Albert) = extendTriple t := by
  rfl

end CKM.NativeDerivationTriality

#print axioms CKM.NativeDerivationTriality.IsRelatedTriple.mixed_left
#print axioms CKM.NativeDerivationTriality.IsRelatedTriple.mixed_right
#print axioms CKM.NativeDerivationTriality.extendTriple_mul
#print axioms CKM.NativeDerivationTriality.extendTriple_lie
#print axioms CKM.NativeDerivationTriality.extendTriple_mem
#print axioms CKM.NativeDerivationTriality.diagonalFixer_map_slot01
#print axioms CKM.NativeDerivationTriality.diagonalFixer_map_slot02
#print axioms CKM.NativeDerivationTriality.diagonalFixer_map_slot12
#print axioms CKM.NativeDerivationTriality.restrictTriple_mem
#print axioms CKM.NativeDerivationTriality.restrictTriple_extendTriple
#print axioms CKM.NativeDerivationTriality.extendTriple_restrictTriple
#print axioms CKM.NativeDerivationTriality.extendLieHom_bijective
#print axioms CKM.NativeDerivationTriality.peirceRestrictionEquiv
#print axioms CKM.NativeDerivationTriality.peirceRestrictionEquiv_apply
#print axioms CKM.NativeDerivationTriality.peirceRestrictionEquiv_symm_apply

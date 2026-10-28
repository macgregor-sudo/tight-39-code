module

public import NativeTrialitySkewDim

/-!
# Seven anticommuting skew square roots of `-1` span the skew endomorphisms

Let `Γ₁, …, Γ₇` be skew endomorphisms of the native eight-dimensional octonion space with
`Γᵢ² = -1` and `ΓᵢΓⱼ = -ΓⱼΓᵢ` for `i ≠ j` (for instance left, or right, multiplication by the seven
imaginary units). The 28 maps `Γᵢ` and `ΓᵢΓⱼ` (`i < j`) form a basis of the skew endomorphisms, and a
skew endomorphism commuting with every `Γᵢ` is zero.

Proof route (MASTER §6.6): words of one to four distinct generators have trace zero, because
conjugation by a suitable generator negates them; hence the 28 maps are orthogonal for the trace
pairing `(S, T) ↦ -tr(S T)` with squared norm eight, so they are linearly independent, and the skew
endomorphisms have dimension `8·7/2 = 28` (strict upper-triangular entries in the orthonormal basis
`octBasis`). A skew `T` commuting with all `Γᵢ` is trace-orthogonal to every basis map.
-/

@[expose] public section

noncomputable section

namespace CKM.NativeDerivationTriality

open Glennie

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Seven skew, pairwise anticommuting square roots of `-1` on the native octonion space. -/
structure CliffordSeven (Γ : Fin 7 → Module.End ℝ Octonion) : Prop where
  sq : ∀ i, Γ i * Γ i = -1
  anticomm : ∀ i j, i ≠ j → Γ i * Γ j = -(Γ j * Γ i)
  skew : ∀ i, Γ i ∈ skewEnd

/-- Index set of the 28 Clifford words: single generators and ordered pairs `i < j`. -/
abbrev CliffordIndex := Fin 7 ⊕ {p : Fin 7 × Fin 7 // p.1 < p.2}

/-- The Clifford words `Γᵢ` and `ΓᵢΓⱼ` (`i < j`). -/
def cliffordWord (Γ : Fin 7 → Module.End ℝ Octonion) : CliffordIndex → Module.End ℝ Octonion
  | Sum.inl i => Γ i
  | Sum.inr p => Γ p.1.1 * Γ p.1.2


/-! ## Helper lemmas -/

section Signs

variable {R : Type*} [Ring R]

/-- Sign bookkeeping: `g` anticommutes with `x`, commutes with `y`, hence anticommutes with `x y`. -/
theorem anti_mul_comm {g x y : R} (hx : g * x = -(x * g)) (hy : g * y = y * g) :
    g * (x * y) = -((x * y) * g) := by
  rw [← mul_assoc, hx, neg_mul, mul_assoc, hy, ← mul_assoc]

/-- Sign bookkeeping: `g` commutes with `x`, anticommutes with `y`, hence anticommutes with `x y`. -/
theorem comm_mul_anti {g x y : R} (hx : g * x = x * g) (hy : g * y = -(y * g)) :
    g * (x * y) = -((x * y) * g) := by
  rw [← mul_assoc, hx, mul_assoc, hy, mul_neg, ← mul_assoc]

/-- Sign bookkeeping: `g` anticommutes with `x` and `y`, hence commutes with `x y`. -/
theorem anti_mul_anti {g x y : R} (hx : g * x = -(x * g)) (hy : g * y = -(y * g)) :
    g * (x * y) = (x * y) * g := by
  rw [← mul_assoc, hx, neg_mul, mul_assoc, hy, mul_neg, neg_neg, ← mul_assoc]

/-- `A W A = W` when `A² = -1` and `A` anticommutes with `W`. -/
theorem anti_conj_eq {A W : R} (hA : A * A = -1) (hAW : A * W = -(W * A)) : A * W * A = W := by
  rw [hAW, neg_mul, mul_assoc, hA, mul_neg, mul_one, neg_neg]

/-- `A (A W) = -W` when `A² = -1`. -/
theorem sq_mul_eq {A W : R} (hA : A * A = -1) : A * (A * W) = -W := by
  rw [← mul_assoc, hA, neg_mul, one_mul]

/-- The product of two anticommuting square roots of `-1` squares to `-1`. -/
theorem mul_mul_self_eq {a b : R} (ha : a * a = -1) (hb : b * b = -1) (hab : b * a = -(a * b)) :
    a * b * (a * b) = -1 := by
  calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
    _ = a * (-(a * b)) * b := by rw [hab]
    _ = -((a * a) * (b * b)) := by simp only [mul_neg, neg_mul, mul_assoc]
    _ = -1 := by rw [ha, hb, neg_one_mul, neg_neg]

/-- From the polarized relation `x x + x x = -2 • 1` deduce `x x = -1` (here `x x` is `y`). -/
theorem eq_neg_one_of_add_self [Module ℝ R] {y : R} (h : y + y = (-2 : ℝ) • (1 : R)) : y = -1 := by
  calc y = ((2 : ℝ)⁻¹ * 2) • y := by norm_num
    _ = (2 : ℝ)⁻¹ • (y + y) := by rw [mul_smul, two_smul]
    _ = (2 : ℝ)⁻¹ • ((-2 : ℝ) • (1 : R)) := by rw [h]
    _ = -1 := by rw [smul_smul]; norm_num

end Signs

/-- An endomorphism anticommuting with a square root of `-1` is trace free. -/
theorem trace_eq_zero_of_anticomm {A W : Module.End ℝ Octonion} (hA : A * A = -1)
    (hAW : A * W = -(W * A)) : LinearMap.trace ℝ Octonion W = 0 := by
  have h1 : (A * W) * A = W := anti_conj_eq hA hAW
  have h2 : A * (A * W) = -W := sq_mul_eq hA
  have h3 := LinearMap.trace_mul_comm ℝ (A * W) A
  rw [h1, h2, map_neg] at h3
  linarith

/-- Membership in `skewEnd`, unfolded. -/
theorem mem_skewEnd_iff_form {T : Module.End ℝ Octonion} :
    T ∈ skewEnd ↔ ∀ x y, octDotForm (T x) y = -octDotForm x (T y) := by
  rw [← LieSubalgebra.mem_toSubmodule]
  change T ∈ LinearMap.skewAdjointSubmodule octDotForm ↔ _
  rw [LinearMap.mem_skewAdjointSubmodule]
  simp only [LinearMap.IsSkewAdjoint, LinearMap.IsAdjointPair, Pi.neg_apply, map_neg]

/-- The product of two anticommuting skew endomorphisms is skew. -/
theorem mul_mem_skewEnd_of_anticomm {X Y : Module.End ℝ Octonion} (hX : X ∈ skewEnd)
    (hY : Y ∈ skewEnd) (hXY : Y * X = -(X * Y)) : X * Y ∈ skewEnd := by
  rw [mem_skewEnd_iff_form] at hX hY ⊢
  intro x y
  have e : Y (X y) = -(X (Y y)) := by
    have := LinearMap.congr_fun hXY y
    simpa only [Module.End.mul_apply, LinearMap.neg_apply] using this
  rw [Module.End.mul_apply, Module.End.mul_apply, hX, hY, e, map_neg, neg_neg]

/-- Among seven indices one avoids any three given ones. -/
theorem exists_ne_three : ∀ a b c : Fin 7, ∃ k : Fin 7, k ≠ a ∧ k ≠ b ∧ k ≠ c := by
  decide

/-- A family with the Clifford relations `Γ_iΓ_j + Γ_jΓ_i = -2δ_ij` that is skew is a Clifford family. -/
theorem cliffordSeven_of_anticomm {Γ : Fin 7 → Module.End ℝ Octonion}
    (hrel : ∀ i j, Γ i * Γ j + Γ j * Γ i = (if i = j then (-2 : ℝ) else 0) • (1 : Module.End ℝ Octonion))
    (hskew : ∀ i, Γ i ∈ skewEnd) : CliffordSeven Γ where
  sq i := by
    have h := hrel i i
    simp only [↓reduceIte] at h
    exact eq_neg_one_of_add_self h
  anticomm i j hij := by
    have h := hrel i j
    simp only [hij, ↓reduceIte, zero_smul] at h
    exact eq_neg_of_add_eq_zero_left h
  skew := hskew

theorem card_cliffordIndex : Fintype.card CliffordIndex = 28 := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_subtype]
  decide

namespace CliffordSeven

variable {Γ : Fin 7 → Module.End ℝ Octonion}

theorem cliffordWord_mem (h : CliffordSeven Γ) (k : CliffordIndex) : cliffordWord Γ k ∈ skewEnd := by
  rcases k with i | ⟨⟨a, b⟩, hab⟩
  · exact h.skew i
  · exact mul_mem_skewEnd_of_anticomm (h.skew a) (h.skew b) (h.anticomm b a (ne_of_gt hab))

/-- Every Clifford word squares to `-1`. -/
theorem cliffordWord_sq (h : CliffordSeven Γ) (k : CliffordIndex) :
    cliffordWord Γ k * cliffordWord Γ k = -1 := by
  rcases k with i | ⟨⟨a, b⟩, hab⟩
  · exact h.sq i
  · exact mul_mul_self_eq (h.sq a) (h.sq b) (h.anticomm b a (ne_of_gt hab))

/-- Distinct Clifford words are trace orthogonal. -/
theorem trace_cliffordWord_mul_of_ne (h : CliffordSeven Γ) {m n : CliffordIndex} (hmn : m ≠ n) :
    LinearMap.trace ℝ Octonion (cliffordWord Γ m * cliffordWord Γ n) = 0 := by
  rcases m with a | ⟨⟨a, b⟩, hab⟩ <;> rcases n with c | ⟨⟨c, d⟩, hcd⟩
  · have hac : a ≠ c := fun e => hmn (by rw [e])
    exact trace_eq_zero_of_anticomm (h.sq a) (comm_mul_anti rfl (h.anticomm a c hac))
  · obtain ⟨k, hka, hkc, hkd⟩ := exists_ne_three a c d
    exact trace_eq_zero_of_anticomm (h.sq k)
      (anti_mul_comm (h.anticomm k a hka) (anti_mul_anti (h.anticomm k c hkc) (h.anticomm k d hkd)))
  · obtain ⟨k, hka, hkb, hkc⟩ := exists_ne_three a b c
    exact trace_eq_zero_of_anticomm (h.sq k)
      (comm_mul_anti (anti_mul_anti (h.anticomm k a hka) (h.anticomm k b hkb)) (h.anticomm k c hkc))
  · show LinearMap.trace ℝ Octonion (Γ a * Γ b * (Γ c * Γ d)) = 0
    have hba : b ≠ a := ne_of_gt hab
    by_cases ha : a ≠ c ∧ a ≠ d
    · exact trace_eq_zero_of_anticomm (h.sq a)
        (anti_mul_comm (comm_mul_anti rfl (h.anticomm a b hba.symm))
          (anti_mul_anti (h.anticomm a c ha.1) (h.anticomm a d ha.2)))
    by_cases hb : b ≠ c ∧ b ≠ d
    · exact trace_eq_zero_of_anticomm (h.sq b)
        (anti_mul_comm (anti_mul_comm (h.anticomm b a hba) rfl)
          (anti_mul_anti (h.anticomm b c hb.1) (h.anticomm b d hb.2)))
    exfalso
    rw [not_and_or, not_not, not_not] at ha hb
    rcases ha with rfl | rfl
    · rcases hb with rfl | rfl
      · exact hba rfl
      · exact hmn rfl
    · rcases hb with rfl | rfl
      · exact lt_asymm hab hcd
      · exact hba rfl

/-- The trace pairing of Clifford words: `tr (S_m S_n) = -8 δ_mn`. -/
theorem trace_cliffordWord_mul (h : CliffordSeven Γ) (m n : CliffordIndex) :
    LinearMap.trace ℝ Octonion (cliffordWord Γ m * cliffordWord Γ n) = if m = n then -8 else 0 := by
  split_ifs with e
  · subst e
    rw [h.cliffordWord_sq, map_neg, LinearMap.trace_one, finrank_octonion]
    norm_num
  · exact h.trace_cliffordWord_mul_of_ne e

/-- Coefficient extraction: `tr (S_m · Σ c_n S_n) = -8 c_m`. -/
theorem trace_cliffordWord_mul_sum (h : CliffordSeven Γ) (c : CliffordIndex → ℝ) (m : CliffordIndex) :
    LinearMap.trace ℝ Octonion (cliffordWord Γ m * ∑ n, c n • cliffordWord Γ n) = -8 * c m := by
  rw [Finset.mul_sum, map_sum]
  simp only [mul_smul_comm, map_smul, h.trace_cliffordWord_mul, smul_eq_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

theorem linearIndependent_cliffordWord (h : CliffordSeven Γ) : LinearIndependent ℝ (cliffordWord Γ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg m
  have := h.trace_cliffordWord_mul_sum g m
  rw [hg, mul_zero, map_zero] at this
  linarith

/-- Every skew endomorphism is a real combination of the 28 Clifford words. -/
theorem mem_span_cliffordWord (h : CliffordSeven Γ) {T : Module.End ℝ Octonion} (hT : T ∈ skewEnd) :
    T ∈ Submodule.span ℝ (Set.range (cliffordWord Γ)) := by
  have hle : Submodule.span ℝ (Set.range (cliffordWord Γ)) ≤ skewEnd.toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact h.cliffordWord_mem k
  have hfin : Module.finrank ℝ skewEnd.toSubmodule = 28 := finrank_skewEnd
  have : FiniteDimensional ℝ skewEnd.toSubmodule :=
    Module.finite_of_finrank_pos (by rw [hfin]; norm_num)
  have heq := Submodule.eq_of_le_of_finrank_eq hle
    (by rw [finrank_span_eq_card h.linearIndependent_cliffordWord, card_cliffordIndex, hfin])
  rw [heq]
  exact hT

/-- A skew endomorphism commuting with every generator is zero. -/
theorem eq_zero_of_commute (h : CliffordSeven Γ) {T : Module.End ℝ Octonion} (hT : T ∈ skewEnd)
    (hc : ∀ i, Γ i * T = T * Γ i) : T = 0 := by
  obtain ⟨c, hcT⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (h.mem_span_cliffordWord hT)
  have hz : ∀ m, LinearMap.trace ℝ Octonion (cliffordWord Γ m * T) = 0 := by
    intro m
    rcases m with a | ⟨⟨a, b⟩, hab⟩
    · obtain ⟨k, hka, -, -⟩ := exists_ne_three a a a
      exact trace_eq_zero_of_anticomm (h.sq k) (anti_mul_comm (h.anticomm k a hka) (hc k))
    · exact trace_eq_zero_of_anticomm (h.sq a)
        (anti_mul_comm (comm_mul_anti rfl (h.anticomm a b (ne_of_lt hab))) (hc a))
  have hc0 : ∀ m, c m = 0 := by
    intro m
    have := h.trace_cliffordWord_mul_sum c m
    rw [hcT, hz] at this
    linarith
  rw [← hcT]
  simp only [hc0, zero_smul, Finset.sum_const_zero]

end CliffordSeven

/-- Left multiplications by the seven imaginary units form a Clifford family. -/
theorem cliffordSeven_leftMul : CliffordSeven (fun i => leftMul (imagUnit i)) :=
  cliffordSeven_of_anticomm leftMul_imagUnit_anticomm (fun i => leftMul_mem_skewEnd (octRe_imagUnit i))

/-- Right multiplications by the seven imaginary units form a Clifford family. -/
theorem cliffordSeven_rightMul : CliffordSeven (fun i => rightMul (imagUnit i)) :=
  cliffordSeven_of_anticomm rightMul_imagUnit_anticomm (fun i => rightMul_mem_skewEnd (octRe_imagUnit i))

end CKM.NativeDerivationTriality

#print axioms CKM.NativeDerivationTriality.card_cliffordIndex
#print axioms CKM.NativeDerivationTriality.CliffordSeven.cliffordWord_mem
#print axioms CKM.NativeDerivationTriality.CliffordSeven.linearIndependent_cliffordWord
#print axioms CKM.NativeDerivationTriality.CliffordSeven.mem_span_cliffordWord
#print axioms CKM.NativeDerivationTriality.CliffordSeven.eq_zero_of_commute
#print axioms CKM.NativeDerivationTriality.cliffordSeven_leftMul
#print axioms CKM.NativeDerivationTriality.cliffordSeven_rightMul

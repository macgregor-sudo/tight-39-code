module

public import HTKronAlgebra

@[expose] public section

/-!
# Coefficient bounds and Kronecker exactness for the native quadratic forms

First-party code. Uses the generic base-`B` uniqueness
`HTKron.quadratic_coeff_eq_zero` unchanged.

`component_identity`: if the exact evaluation at the Golomb–Kronecker point agrees, the coefficient
bound `2 (BE + BB) < 2^width` holds, the columns are strictly sorted and the Golomb marks are Sidon,
then the native and Book quadratic forms agree over every commutative ring.
-/

set_option autoImplicit false

noncomputable section

namespace Option2.NativeStress.HTRouteKron

open scoped BigOperators
open QuarticCertificate.RowBridge BookHT.TangentCoordinates BookHT.Dictionary
open ConfigurationResidualIndices

/-! ## The coordinate ℓ¹ norm -/

def n1 (x : Z4) : ℕ := x.a.natAbs + x.b.natAbs + x.c.natAbs + x.d.natAbs

lemma n1_cast (x : Z4) : (n1 x : ℤ) = |x.a| + |x.b| + |x.c| + |x.d| := by
  simp [n1, Int.natCast_natAbs]

lemma n1_zero : n1 0 = 0 := rfl

lemma n1_add (x y : Z4) : n1 (x + y) ≤ n1 x + n1 y := by
  have := Int.natAbs_add_le x.a y.a
  have := Int.natAbs_add_le x.b y.b
  have := Int.natAbs_add_le x.c y.c
  have := Int.natAbs_add_le x.d y.d
  simp only [n1, Z4.hadd_a, Z4.hadd_b, Z4.hadd_c, Z4.hadd_d]
  omega

lemma n1_neg (x : Z4) : n1 (-x) = n1 x := by
  simp [n1]

lemma n1_sub (x y : Z4) : n1 (x - y) ≤ n1 x + n1 y := by
  rw [sub_eq_add_neg]
  exact (n1_add _ _).trans (by rw [n1_neg])

lemma n1_intCast_mul (n : ℤ) (x : Z4) : n1 ((n : Z4) * x) = n.natAbs * n1 x := by
  simp only [n1, Z4.intCast_mul_a, Z4.intCast_mul_b, Z4.intCast_mul_c, Z4.intCast_mul_d,
    Int.natAbs_mul]
  ring

lemma n1_intCast (n : ℤ) : n1 (n : Z4) = n.natAbs := by
  simp [n1]

lemma abs_sub4 (p q r s : ℤ) : |p + q - (r + s)| ≤ |p| + |q| + |r| + |s| := by
  have h1 := abs_sub (p + q) (r + s)
  have h2 := abs_add_le p q
  have h3 := abs_add_le r s
  linarith

lemma abs_add4 (p q r s : ℤ) : |p + q + (r + s)| ≤ |p| + |q| + |r| + |s| := by
  have h1 := abs_add_le (p + q) (r + s)
  have h2 := abs_add_le p q
  have h3 := abs_add_le r s
  linarith

lemma n1_mul (x y : Z4) : n1 (x * y) ≤ 3 * n1 x * n1 y := by
  have key : (n1 (x * y) : ℤ) ≤ 3 * (n1 x : ℤ) * (n1 y : ℤ) := by
    rw [n1_cast, n1_cast, n1_cast]
    simp only [Z4.hmul_a, Z4.hmul_b, Z4.hmul_c, Z4.hmul_d]
    have ha := abs_sub4 (x.a * y.a) (3 * (x.c * y.c)) (x.b * y.b) (3 * (x.d * y.d))
    have hb : |x.a * y.b + x.b * y.a + 3 * (x.c * y.d + x.d * y.c)| ≤
        |x.a * y.b| + |x.b * y.a| + |3 * (x.c * y.d)| + |3 * (x.d * y.c)| := by
      have := abs_add4 (x.a * y.b) (x.b * y.a) (3 * (x.c * y.d)) (3 * (x.d * y.c))
      rw [mul_add] at *
      linarith
    have hc := abs_sub4 (x.a * y.c) (x.c * y.a) (x.b * y.d) (x.d * y.b)
    have hd := abs_add4 (x.a * y.d) (x.d * y.a) (x.b * y.c) (x.c * y.b)
    simp only [abs_mul, abs_of_pos (show (0 : ℤ) < 3 by norm_num)] at ha hb hc hd
    have p1 := abs_nonneg x.a; have p2 := abs_nonneg x.b
    have p3 := abs_nonneg x.c; have p4 := abs_nonneg x.d
    have q1 := abs_nonneg y.a; have q2 := abs_nonneg y.b
    have q3 := abs_nonneg y.c; have q4 := abs_nonneg y.d
    nlinarith [mul_nonneg p1 q1, mul_nonneg p1 q2, mul_nonneg p1 q3, mul_nonneg p1 q4,
      mul_nonneg p2 q1, mul_nonneg p2 q2, mul_nonneg p2 q3, mul_nonneg p2 q4,
      mul_nonneg p3 q1, mul_nonneg p3 q2, mul_nonneg p3 q3, mul_nonneg p3 q4,
      mul_nonneg p4 q1, mul_nonneg p4 q2, mul_nonneg p4 q3, mul_nonneg p4 q4]
  exact_mod_cast key

lemma n1_list_sum (l : List Z4) : n1 l.sum ≤ (l.map n1).sum := by
  induction l with
  | nil => simp [n1_zero]
  | cons x l ih =>
      simp only [List.sum_cons, List.map_cons]
      exact (n1_add _ _).trans (by omega)

lemma abs_a_le (x : Z4) : x.a.natAbs ≤ n1 x := by unfold n1; omega
lemma abs_b_le (x : Z4) : x.b.natAbs ≤ n1 x := by unfold n1; omega
lemma abs_c_le (x : Z4) : x.c.natAbs ≤ n1 x := by unfold n1; omega
lemma abs_d_le (x : Z4) : x.d.natAbs ≤ n1 x := by unfold n1; omega

/-! ## Column and coefficient bounds -/

def maxL (l : List ℕ) : ℕ := l.foldr max 0

lemma le_maxL (l : List ℕ) (x : ℕ) (h : x ∈ l) : x ≤ maxL l := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
      simp only [maxL, List.foldr_cons] at ih ⊢
      rcases List.mem_cons.1 h with rfl | h
      · exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)

lemma maxL_cons (y : ℕ) (l : List ℕ) : maxL (y :: l) = max y (maxL l) := rfl

def colMaxJ (j : Fin 24) : ℕ := maxL ((d6Entries (eigenIndex j)).map fun e => n1 (ofCoeff e.2))

/-- Largest coordinate ℓ¹ norm of any original eigencolumn entry. -/
def Kc : ℕ := maxL ((List.finRange 24).map colMaxJ)

lemma n1_sparseZ_le (es : List Entry) (hs : es.Pairwise (fun e f => e.1.val < f.1.val)) (n : ℕ) :
    n1 (sparseZ es n) ≤ maxL (es.map fun e => n1 (ofCoeff e.2)) := by
  induction es with
  | nil => simp [sparseZ_nil, n1_zero]
  | cons e es ih =>
      have hes := List.Pairwise.of_cons hs
      have hgt : ∀ f ∈ es, e.1.val < f.1.val := fun f hf => List.rel_of_pairwise_cons hs hf
      rw [sparseZ_cons, List.map_cons, maxL_cons]
      by_cases he : e.1.val = n
      · rw [if_pos he, sparseZ_eq_zero es n (fun f hf => by have := hgt f hf; omega), add_zero]
        exact le_max_left _ _
      · rw [if_neg he, zero_add]
        exact (ih hes).trans (le_max_right _ _)

lemma n1_colZ_le (hs : ∀ j, (d6Entries (eigenIndex j)).Pairwise (fun e f => e.1.val < f.1.val))
    (j : Fin 24) (u : Fin 1053) : n1 (colZ j u) ≤ Kc :=
  (n1_sparseZ_le _ (hs j) u.val).trans
    (le_maxL _ _ (List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩))

def absSum (l : List (Fin 1053 × Fin 1053 × ℤ)) : ℕ := (l.map fun t => t.2.2.natAbs).sum

/-- Computable bound for every native coefficient `NE d s es j k`. -/
def BE (d : ℕ) (s : NativeH.HSpec) (es : List NativeH.Entry) : ℕ :=
  9 * Kc * Kc * (es.map fun e => n1 (weight d s e) * absSum (labelShape e.label).quadratic).sum

/-- Computable bound for every Book coefficient `NB sc l j k`. -/
def BB (sc : ℤ) (l : List (Fin 24 × Fin 24 × ℤ)) : ℕ := (l.map fun t => (sc * t.2.2).natAbs).sum

section Bounds

variable (hs : ∀ j, (d6Entries (eigenIndex j)).Pairwise (fun e f => e.1.val < f.1.val))
include hs

lemma n1_qZ_le (l : List (Fin 1053 × Fin 1053 × ℤ)) (j k : Fin 24) :
    n1 (qZ l j k) ≤ 3 * Kc * Kc * absSum l := by
  induction l with
  | nil => simp [qZ, n1_zero]
  | cons t l ih =>
      have h1 : qZ (t :: l) j k = (t.2.2 : Z4) * (colZ j t.1 * colZ k t.2.1) + qZ l j k := by
        simp [qZ]
      have h2 : absSum (t :: l) = t.2.2.natAbs + absSum l := by simp [absSum]
      rw [h1, h2]
      refine (n1_add _ _).trans ?_
      rw [n1_intCast_mul]
      have hm := n1_mul (colZ j t.1) (colZ k t.2.1)
      have hj := n1_colZ_le hs j t.1
      have hk := n1_colZ_le hs k t.2.1
      have : n1 (colZ j t.1 * colZ k t.2.1) ≤ 3 * Kc * Kc :=
        hm.trans (by
          have := Nat.mul_le_mul (Nat.mul_le_mul_left 3 hj) hk
          simpa [mul_assoc] using this)
      have h4 := Nat.mul_le_mul_left t.2.2.natAbs this
      calc t.2.2.natAbs * n1 (colZ j t.1 * colZ k t.2.1) + n1 (qZ l j k)
          ≤ t.2.2.natAbs * (3 * Kc * Kc) + 3 * Kc * Kc * absSum l := Nat.add_le_add h4 ih
        _ = 3 * Kc * Kc * (t.2.2.natAbs + absSum l) := by ring

lemma n1_NE_le (d : ℕ) (s : NativeH.HSpec) (es : List NativeH.Entry) (j k : Fin 24) :
    n1 (NE d s es j k) ≤ BE d s es := by
  unfold NE BE
  induction es with
  | nil => simp [n1_zero]
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons]
      refine (n1_add _ _).trans ?_
      have hm := n1_mul (weight d s e) (qZ (labelShape e.label).quadratic j k)
      have hq := n1_qZ_le hs (labelShape e.label).quadratic j k
      have h3 : n1 (weight d s e * qZ (labelShape e.label).quadratic j k) ≤
          9 * Kc * Kc * (n1 (weight d s e) * absSum (labelShape e.label).quadratic) := by
        refine hm.trans ?_
        have := Nat.mul_le_mul_left (3 * n1 (weight d s e)) hq
        calc 3 * n1 (weight d s e) * n1 (qZ (labelShape e.label).quadratic j k)
            ≤ 3 * n1 (weight d s e) * (3 * Kc * Kc * absSum (labelShape e.label).quadratic) := this
          _ = _ := by ring
      calc _ ≤ _ := Nat.add_le_add h3 ih
        _ = _ := by ring

end Bounds

lemma n1_NB_le (sc : ℤ) (l : List (Fin 24 × Fin 24 × ℤ)) (j k : Fin 24) :
    n1 (NB sc l j k) ≤ BB sc l := by
  unfold NB BB
  induction l with
  | nil => simp [n1_zero]
  | cons t l ih =>
      simp only [List.map_cons, List.sum_cons]
      refine (n1_add _ _).trans ?_
      have : n1 (if t.1 = j ∧ t.2.1 = k then ((sc * t.2.2 : ℤ) : Z4) else 0) ≤ (sc * t.2.2).natAbs := by
        split_ifs
        · rw [n1_intCast]
        · simp [n1_zero]
      omega

/-! ## Symmetrization -/

lemma sym_sum {A : Type*} [AddCommMonoid A] {n : ℕ} (f : Fin n → Fin n → A) :
    ∑ j, ∑ k, f j k = ∑ j, ∑ k, (if j ≤ k then (if j = k then f j j else f j k + f k j) else 0) := by
  have h1 : ∀ j k, f j k = (if j < k then f j k else 0) + (if j = k then f j k else 0) +
      (if k < j then f j k else 0) := by
    intro j k
    rcases lt_trichotomy j k with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.2 h.le]
  have h2 : ∀ j k, (if j ≤ k then (if j = k then f j j else f j k + f k j) else 0) =
      (if j < k then f j k else 0) + (if j = k then f j k else 0) + (if j < k then f k j else 0) := by
    intro j k
    rcases lt_trichotomy j k with h | h | h
    · simp [h, h.le, h.ne]
    · subst h; simp
    · simp [not_le.2 h, not_lt.2 h.le, h.ne']
  conv_lhs => enter [2, j, 2, k]; rw [h1 j k]
  conv_rhs => enter [2, j, 2, k]; rw [h2 j k]
  simp only [Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

/-! ## The Golomb–Kronecker point -/

/-- All `(j, k, g j + g k)` with `j ≤ k`. -/
def sumPairs : List (Fin 24 × Fin 24 × ℕ) :=
  (List.finRange 24).flatMap fun j =>
    ((List.finRange 24).filter fun k => decide (j ≤ k)).map fun k => (j, k, gol j + gol k)

lemma mem_sumPairs (j k : Fin 24) (h : j ≤ k) : (j, k, gol j + gol k) ∈ sumPairs := by
  simp [sumPairs, h]

lemma sidon_of_nodup (h : (sumPairs.map fun p => p.2.2).Nodup) :
    ∀ j l j' l' : Fin 24, j ≤ l → j' ≤ l' → gol j + gol l = gol j' + gol l' → j = j' ∧ l = l' := by
  intro j l j' l' h1 h2 h3
  have := List.inj_on_of_nodup_map h (mem_sumPairs j l h1) (mem_sumPairs j' l' h2) h3
  simp only [Prod.mk.injEq] at this
  exact ⟨this.1, this.2.1⟩

lemma ystar_eq (j : Fin 24) : ystar j = ((2 : ℤ) ^ width) ^ gol j := by
  rw [← pow_mul]
  show ((2 ^ (width * gol j) : ℕ) : ℤ) = _
  push_cast
  rfl

lemma comp_sum (π : Z4 →+ ℤ) (hπ : ∀ (n : ℤ) (x : Z4), π ((n : Z4) * x) = n * π x)
    (N : Fin 24 → Fin 24 → Z4) :
    π (∑ j, ∑ k, (ystar j : Z4) * (ystar k : Z4) * N j k) =
      ∑ j, ∑ k, (π (N j k)) * (((2 : ℤ) ^ width) ^ gol j * ((2 : ℤ) ^ width) ^ gol k) := by
  simp only [map_sum]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  rw [show (ystar j : Z4) * (ystar k : Z4) * N j k = ((ystar j * ystar k : ℤ) : Z4) * N j k by
    push_cast; ring, hπ, ystar_eq, ystar_eq]
  ring

/-- Exactness of one evaluation at the Golomb–Kronecker point. -/
theorem kron_vanish (N : Fin 24 → Fin 24 → Z4) (Bd : ℕ) (hN : ∀ j k, n1 (N j k) ≤ Bd)
    (hB : 2 * Bd < 2 ^ width)
    (hsid : ∀ j l j' l' : Fin 24, j ≤ l → j' ≤ l' → gol j + gol l = gol j' + gol l' →
      j = j' ∧ l = l')
    (h : ∑ j, ∑ k, (ystar j : Z4) * (ystar k : Z4) * N j k = 0)
    {R : Type*} [CommRing R] (φ : Z4 →+* R) (y : Fin 24 → R) :
    ∑ j, ∑ k, y j * y k * φ (N j k) = 0 := by
  classical
  let M : Fin 24 → Fin 24 → Z4 := fun j k => if j = k then N j j else N j k + N k j
  have hMb : ∀ j k, n1 (M j k) ≤ 2 * Bd := by
    intro j k
    by_cases hjk : j = k
    · simp only [M, if_pos hjk]; have := hN j j; omega
    · simp only [M, if_neg hjk]
      have := n1_add (N j k) (N k j); have := hN j k; have := hN k j; omega
  have hB1 : (1 : ℤ) < 2 ^ width := by
    have : (1 : ℤ) < 2 ^ 1 := by norm_num
    exact lt_of_lt_of_le this (pow_le_pow_right₀ (by norm_num) (by unfold width; norm_num))
  have hcomp : ∀ (π : Z4 →+ ℤ), (∀ (n : ℤ) (x : Z4), π ((n : Z4) * x) = n * π x) →
      (∀ x, (π x).natAbs ≤ n1 x) → ∀ j k, j ≤ k → π (M j k) = 0 := by
    intro π hπ hle
    have h0 := comp_sum π hπ N
    rw [h, map_zero, sym_sum] at h0
    apply HTKron.quadratic_coeff_eq_zero ((2 : ℤ) ^ width) hB1 gol hsid (fun j k => π (M j k))
    · intro j k _
      have h1 := hle (M j k)
      have h2 := hMb j k
      have : ((π (M j k)).natAbs : ℤ) < 2 ^ width := by
        have : (π (M j k)).natAbs < 2 ^ width := by omega
        exact_mod_cast this
      rwa [Int.natCast_natAbs] at this
    · refine Eq.trans ?_ h0.symm
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro k _
      by_cases hjk : j ≤ k
      · by_cases he : j = k
        · subst he; simp [M]
        · simp only [hjk, if_true, he, if_false, M, map_add]; ring
      · simp [hjk]
  have hM0 : ∀ j k, j ≤ k → M j k = 0 := by
    intro j k hjk
    ext
    · exact hcomp Z4.aHom (fun n x => Z4.intCast_mul_a n x) abs_a_le j k hjk
    · exact hcomp Z4.bHom (fun n x => Z4.intCast_mul_b n x) abs_b_le j k hjk
    · exact hcomp Z4.cHom (fun n x => Z4.intCast_mul_c n x) abs_c_le j k hjk
    · exact hcomp Z4.dHom (fun n x => Z4.intCast_mul_d n x) abs_d_le j k hjk
  rw [sym_sum]
  apply Finset.sum_eq_zero; intro j _
  apply Finset.sum_eq_zero; intro k _
  by_cases hjk : j ≤ k
  · have h0 := hM0 j k hjk
    by_cases he : j = k
    · subst he
      simp only [M, if_pos rfl] at h0
      simp [h0]
    · simp only [M, if_neg he] at h0
      simp only [hjk, if_true, he, if_false]
      rw [show y j * y k * φ (N j k) + y k * y j * φ (N k j) = y j * y k * φ (N j k + N k j) by
        rw [map_add]; ring, h0, map_zero, mul_zero]
  · simp [hjk]

/-- Exact native/Book agreement over every commutative ring from one Kronecker evaluation. -/
theorem component_identity (d : ℕ) (s : NativeH.HSpec) (es : List NativeH.Entry) (sc : ℤ)
    (l : List (Fin 24 × Fin 24 × ℤ))
    (hs : ∀ j, (d6Entries (eigenIndex j)).Pairwise (fun e f => e.1.val < f.1.val))
    (hsid : ∀ j l j' l' : Fin 24, j ≤ l → j' ≤ l' → gol j + gol l = gol j' + gol l' →
      j = j' ∧ l = l')
    (hval : engine d s es (stateList ystar) = bookVal sc l ystar)
    (hB : 2 * (BE d s es + BB sc l) < 2 ^ width)
    {R : Type*} [CommRing R] (φ : Z4 →+* R) (y : Fin 24 → R) :
    engR φ d s es y = bookR sc l y := by
  have hZ : ∑ j, ∑ k, (ystar j : Z4) * (ystar k : Z4) * (NE d s es j k - NB sc l j k) = 0 := by
    have h1 := engine_eq hs d s es ystar
    have h2 := bookVal_eq sc l ystar
    rw [hval, h2, engR_expand, bookR_expand sc l (RingHom.id Z4)] at h1
    simp only [RingHom.id_apply] at h1
    simp only [mul_sub, Finset.sum_sub_distrib, h1, sub_self]
  have hv := kron_vanish (fun j k => NE d s es j k - NB sc l j k) (BE d s es + BB sc l)
    (fun j k => (n1_sub _ _).trans (Nat.add_le_add (n1_NE_le hs d s es j k) (n1_NB_le sc l j k)))
    hB hsid hZ φ y
  rw [engR_expand, bookR_expand sc l φ, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  rw [← hv]
  apply Finset.sum_congr rfl; intro j _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro k _
  rw [map_sub, mul_sub]

end Option2.NativeStress.HTRouteKron

end

module

public import HTKronLists
public import HTKronExact
public import NativeHCoefficientPolarization

@[expose] public section

/-!
# Polynomial structure, complex image and Kronecker exactness

First-party code.
* `toC : Z4 →+* ℂ` sends `(a, b, c, d)` to `a + b i + c √3 + d i √3`.
* `ptR φ y` is the native point `Σ_j y_j φ(column_j)` over any commutative ring; `engR`, `bookR`
  are the native and Book quadratic forms. Both are expanded as `Σ_j Σ_k y_j y_k φ(N j k)` with
  explicit `Z4` coefficient matrices `NE`, `NB`.
* `n1` is the coordinate ℓ¹ norm; `n1 (x*y) ≤ 3 n1 x n1 y`; the coefficient matrices obey
  explicit computable bounds `BE`, `BB`.
* `kron_vanish`: one exact evaluation at the Kronecker point `y_j = 2^(width * g_j)` (Golomb `g`)
  plus the bound forces every symmetrized coefficient to vanish (via `HTKron`).
-/

set_option autoImplicit false

noncomputable section

namespace Option2.NativeStress.HTRouteKron

open scoped BigOperators
open QuarticCertificate.RowBridge BookHT.TangentCoordinates BookHT.Dictionary
open ConfigurationResidualIndices

/-! ## Coordinate projections -/

def Z4.aHom : Z4 →+ ℤ := ⟨⟨Z4.a, rfl⟩, fun _ _ => rfl⟩
def Z4.bHom : Z4 →+ ℤ := ⟨⟨Z4.b, rfl⟩, fun _ _ => rfl⟩
def Z4.cHom : Z4 →+ ℤ := ⟨⟨Z4.c, rfl⟩, fun _ _ => rfl⟩
def Z4.dHom : Z4 →+ ℤ := ⟨⟨Z4.d, rfl⟩, fun _ _ => rfl⟩

@[simp] lemma Z4.conj_a (x : Z4) : (Z4.conj x).a = x.a := rfl
@[simp] lemma Z4.conj_b (x : Z4) : (Z4.conj x).b = -x.b := rfl
@[simp] lemma Z4.conj_c (x : Z4) : (Z4.conj x).c = x.c := rfl
@[simp] lemma Z4.conj_d (x : Z4) : (Z4.conj x).d = -x.d := rfl
@[simp] lemma Z4.ofInt_a (n : ℤ) : (Z4.ofInt n).a = n := rfl
@[simp] lemma Z4.ofInt_b (n : ℤ) : (Z4.ofInt n).b = 0 := rfl
@[simp] lemma Z4.ofInt_c (n : ℤ) : (Z4.ofInt n).c = 0 := rfl
@[simp] lemma Z4.ofInt_d (n : ℤ) : (Z4.ofInt n).d = 0 := rfl

lemma Z4.intCast_mul_a (n : ℤ) (x : Z4) : ((n : Z4) * x).a = n * x.a := by simp
lemma Z4.intCast_mul_b (n : ℤ) (x : Z4) : ((n : Z4) * x).b = n * x.b := by simp
lemma Z4.intCast_mul_c (n : ℤ) (x : Z4) : ((n : Z4) * x).c = n * x.c := by simp
lemma Z4.intCast_mul_d (n : ℤ) (x : Z4) : ((n : Z4) * x).d = n * x.d := by simp

/-! ## The complex image -/

noncomputable def s3 : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)

lemma s3_mul_self : s3 * s3 = 3 := by
  unfold s3
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

noncomputable def toC : Z4 →+* ℂ where
  toFun x := (x.a : ℂ) + (x.b : ℂ) * Complex.I + (x.c : ℂ) * s3 + (x.d : ℂ) * Complex.I * s3
  map_one' := by simp
  map_mul' := by
    intro x y
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have hs := s3_mul_self
    simp only [Z4.hmul_a, Z4.hmul_b, Z4.hmul_c, Z4.hmul_d]
    push_cast
    linear_combination (-((x.b : ℂ) + (x.d : ℂ) * s3) * ((y.b : ℂ) + (y.d : ℂ) * s3)) * hI +
      (-Complex.I * (x.c : ℂ) * (y.d : ℂ) - Complex.I * (x.d : ℂ) * (y.c : ℂ) -
        (x.c : ℂ) * (y.c : ℂ) + (x.d : ℂ) * (y.d : ℂ)) * hs
  map_zero' := by simp
  map_add' := by
    intro x y
    simp only [Z4.hadd_a, Z4.hadd_b, Z4.hadd_c, Z4.hadd_d]
    push_cast
    ring

lemma toC_apply (x : Z4) :
    toC x = (x.a : ℂ) + (x.b : ℂ) * Complex.I + (x.c : ℂ) * s3 + (x.d : ℂ) * Complex.I * s3 := rfl

lemma toC_conj (x : Z4) : toC (Z4.conj x) = star (toC x) := by
  have h3 : star s3 = s3 := by unfold s3; exact Complex.conj_ofReal _
  simp only [toC_apply, Z4.conj_a, Z4.conj_b, Z4.conj_c, Z4.conj_d, star_add, star_mul',
    Complex.star_def, Complex.conj_I, map_intCast]
  rw [show (starRingEnd ℂ) s3 = s3 from h3]
  push_cast
  ring

lemma toC_neg' (x : Z4) : toC (Z4.neg x) = -toC x := by
  rw [Z4.neg_eq, map_neg]

lemma toC_smul (n : ℤ) (x : Z4) : toC (Z4.smul n x) = (n : ℂ) * toC x := by
  rw [Z4.smul_eq, map_mul, map_intCast]

lemma toC_ofCoeff (q : Coeff) : toC (ofCoeff q) = (denominator : ℂ) * coefficient q := by
  have hd : (denominator : ℂ) ≠ 0 := by
    exact_mod_cast (show denominator ≠ 0 by decide)
  simp only [toC_apply, ofCoeff, coefficient, NativeH.Literal.toComplex, s3]
  field_simp

lemma toC_ofLit (c : NativeH.Literal) : toC (ofLit c) = (c.denominator : ℂ) * c.toComplex := by
  have hd : (c.denominator : ℂ) ≠ 0 := by exact_mod_cast c.denominator_pos.ne'
  simp only [toC_apply, ofLit, NativeH.Literal.toComplex, s3]
  field_simp

lemma toC_orient (s : NativeH.HSpec) (c : NativeH.Literal) :
    toC (orient s (ofLit c)) = (c.denominator : ℂ) * NativeH.orientedValue s c := by
  unfold orient NativeH.orientedValue
  cases hc : s.conjugated <;> cases hn : s.negated <;>
    simp [toC_conj, toC_neg', toC_ofLit, star_mul', Complex.conj_natCast]

/-! ## Native point and quadratic forms over any commutative ring -/

/-- The `Z4` coefficient of eigencolumn `j` at coordinate `u`. -/
def colZ (j : Fin 24) (u : Fin 1053) : Z4 := sparseZ (d6Entries (eigenIndex j)) u.val

section Ring

variable {R : Type*} [CommRing R]

def ptR (φ : Z4 →+* R) (y : Fin 24 → R) (u : Fin 1053) : R := ∑ j, y j * φ (colZ j u)

def qZ (l : List (Fin 1053 × Fin 1053 × ℤ)) (j k : Fin 24) : Z4 :=
  (l.map fun t => (t.2.2 : Z4) * (colZ j t.1 * colZ k t.2.1)).sum

noncomputable def engR (φ : Z4 →+* R) (d : ℕ) (s : NativeH.HSpec) (es : List NativeH.Entry)
    (y : Fin 24 → R) : R :=
  (es.map fun e => φ (weight d s e) * quadraticValue 1 (labelShape e.label).quadratic (ptR φ y)).sum

def NE (d : ℕ) (s : NativeH.HSpec) (es : List NativeH.Entry) (j k : Fin 24) : Z4 :=
  (es.map fun e => weight d s e * qZ (labelShape e.label).quadratic j k).sum

def bookR (sc : ℤ) (l : List (Fin 24 × Fin 24 × ℤ)) (y : Fin 24 → R) : R :=
  (l.map fun t => ((sc * t.2.2 : ℤ) : R) * (y t.1 * y t.2.1)).sum

def NB (sc : ℤ) (l : List (Fin 24 × Fin 24 × ℤ)) (j k : Fin 24) : Z4 :=
  (l.map fun t => if t.1 = j ∧ t.2.1 = k then ((sc * t.2.2 : ℤ) : Z4) else 0).sum

lemma quadraticValue_ptR (φ : Z4 →+* R) (y : Fin 24 → R) (l : List (Fin 1053 × Fin 1053 × ℤ)) :
    quadraticValue 1 l (ptR φ y) = ∑ j, ∑ k, y j * y k * φ (qZ l j k) := by
  induction l with
  | nil => simp [quadraticValue, qZ]
  | cons t l ih =>
      have hq : ∀ j k, qZ (t :: l) j k = (t.2.2 : Z4) * (colZ j t.1 * colZ k t.2.1) + qZ l j k := by
        intro j k; simp [qZ]
      have hv : quadraticValue 1 (t :: l) (ptR φ y) =
          1 * (t.2.2 : R) * ptR φ y t.1 * ptR φ y t.2.1 + quadraticValue 1 l (ptR φ y) := by
        simp [quadraticValue]
      have key : 1 * (t.2.2 : R) * ptR φ y t.1 * ptR φ y t.2.1 = ∑ j, ∑ k,
          y j * y k * ((t.2.2 : R) * (φ (colZ j t.1) * φ (colZ k t.2.1))) := by
        rw [show 1 * (t.2.2 : R) * ptR φ y t.1 * ptR φ y t.2.1 =
          (t.2.2 : R) * (ptR φ y t.1 * ptR φ y t.2.1) by ring, ptR, ptR, Finset.sum_mul_sum]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _
        ring
      rw [hv, ih, key]
      simp only [hq, map_add, map_mul, map_intCast, mul_add, Finset.sum_add_distrib]

lemma engR_expand (φ : Z4 →+* R) (d : ℕ) (s : NativeH.HSpec) (es : List NativeH.Entry)
    (y : Fin 24 → R) : engR φ d s es y = ∑ j, ∑ k, y j * y k * φ (NE d s es j k) := by
  induction es with
  | nil => simp [engR, NE]
  | cons e es ih =>
      have h1 : engR φ d s (e :: es) y = φ (weight d s e) *
          quadraticValue 1 (labelShape e.label).quadratic (ptR φ y) + engR φ d s es y := by
        simp [engR]
      have h2 : ∀ j k, NE d s (e :: es) j k =
          weight d s e * qZ (labelShape e.label).quadratic j k + NE d s es j k := by
        intro j k; simp [NE]
      rw [h1, ih, quadraticValue_ptR]
      simp only [h2, map_add, map_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro k _
      ring

lemma bookR_expand (sc : ℤ) (l : List (Fin 24 × Fin 24 × ℤ)) (φ : Z4 →+* R) (y : Fin 24 → R) :
    bookR sc l y = ∑ j, ∑ k, y j * y k * φ (NB sc l j k) := by
  induction l with
  | nil => simp [bookR, NB]
  | cons t l ih =>
      have h1 : bookR sc (t :: l) y = ((sc * t.2.2 : ℤ) : R) * (y t.1 * y t.2.1) + bookR sc l y := by
        simp [bookR]
      have h2 : ∀ j k, NB sc (t :: l) j k =
          (if t.1 = j ∧ t.2.1 = k then ((sc * t.2.2 : ℤ) : Z4) else 0) + NB sc l j k := by
        intro j k; simp [NB]
      rw [h1, ih]
      simp only [h2, map_add, mul_add, Finset.sum_add_distrib]
      congr 1
      have : ∀ j k, y j * y k * φ (if t.1 = j ∧ t.2.1 = k then ((sc * t.2.2 : ℤ) : Z4) else 0) =
          if k = t.2.1 then (if j = t.1 then ((sc * t.2.2 : ℤ) : R) * (y t.1 * y t.2.1) else 0)
          else 0 := by
        intro j k
        by_cases hj : j = t.1 <;> by_cases hk : k = t.2.1
        · subst hj hk; simp [mul_comm]
        · simp [hk, Ne.symm hk]
        · simp [hj, Ne.symm hj]
        · simp [hj, hk, Ne.symm hj]
      simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Ring

/-! ## The computed values are the ring expressions at the integer point -/

lemma ptR_id (ys : Fin 24 → ℤ) (u : Fin 1053) :
    ptR (RingHom.id Z4) (fun j => (ys j : Z4)) u =
      ∑ j : Fin 24, (ys j : Z4) * sparseZ (d6Entries (eigenIndex j)) u.val := rfl

lemma traceW_eq (k : Fin 27) :
    traceW k = NativePolynomial.IntegralStructureConstants.coordinateTraceWeight k := rfl

section Engine

variable (hs : ∀ j, (d6Entries (eigenIndex j)).Pairwise (fun e f => e.1.val < f.1.val))
include hs

lemma stateList_ptR (ys : Fin 24 → ℤ) (p : Fin 39) :
    stateList ys p = List.ofFn fun k : Fin 27 =>
      ptR (RingHom.id Z4) (fun j => (ys j : Z4))
        (NativePolynomial.ConfigurationResiduals.variableIndex p k) := by
  rw [stateList_spec ys hs p]
  rfl

lemma rowVal_eq (ys : Fin 24 → ℤ) (lab : FLabel) :
    rowVal (stateList ys) lab =
      quadraticValue 1 (labelShape lab).quadratic (ptR (RingHom.id Z4) (fun j => (ys j : Z4))) := by
  rcases lab with ⟨p, k⟩ | lab
  · show idVal (stateList ys p) (productTable k) = _
    rw [idVal_eq, tableVal, stateList_ptR hs]
    simp only [labelShape, quadraticValue, List.map_map]
    congr 1
    apply List.map_congr_left
    intro e _
    simp only [Function.comp_apply, getD_ofFn27, one_mul]
    push_cast
    ring
  rcases lab with i | lab
  · simp [rowVal, labelShape, quadraticValue]
  rcases lab with ⟨f, k⟩ | pq
  · simp [rowVal, labelShape, quadraticValue]
  · show pairDot (stateList ys pq.val.1) (stateList ys pq.val.2) = _
    rw [stateList_ptR hs, stateList_ptR hs, pairDot_ofFn]
    simp only [labelShape, quadraticValue, List.map_ofFn, List.sum_ofFn, Function.comp_def,
      one_mul, traceW_eq, mul_assoc]

lemma termVal_eq (d : ℕ) (s : NativeH.HSpec) (ys : Fin 24 → ℤ) (e : NativeH.Entry) :
    termVal d s (stateList ys) e = weight d s e * rowVal (stateList ys) e.label := by
  rcases e with ⟨lab, c⟩
  rcases lab with ⟨p, k⟩ | lab
  · rfl
  rcases lab with i | lab
  · show Z4.zero = _
    simp [rowVal]
  rcases lab with ⟨f, k⟩ | pq
  · show Z4.zero = _
    simp [rowVal]
  · rfl

lemma engine_eq (d : ℕ) (s : NativeH.HSpec) (es : List NativeH.Entry) (ys : Fin 24 → ℤ) :
    engine d s es (stateList ys) = engR (RingHom.id Z4) d s es (fun j => (ys j : Z4)) := by
  unfold engine engR
  rw [sumZ_eq]
  congr 1
  apply List.map_congr_left
  intro e _
  rw [termVal_eq hs, rowVal_eq hs]
  rfl

end Engine

lemma ofInt_book (a b c : ℤ) :
    Z4.ofInt (Int.mul a (Int.mul b c)) = (a : Z4) * ((b : Z4) * (c : Z4)) := by
  ext <;> simp <;> rfl

lemma bookVal_eq (sc : ℤ) (l : List (Fin 24 × Fin 24 × ℤ)) (ys : Fin 24 → ℤ) :
    bookVal sc l ys = bookR sc l (fun j => (ys j : Z4)) := by
  unfold bookVal bookR
  induction l with
  | nil => rfl
  | cons t l ih =>
      simp only [List.map_cons, List.foldr_cons, List.sum_cons]
      rw [ih]
      simp only [Z4.add_eq]
      congr 1
      rw [ofInt_book]
      rfl

end Option2.NativeStress.HTRouteKron

end

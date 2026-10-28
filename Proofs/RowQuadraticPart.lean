module

public import RowEvaluation
public import PolynomialJetPrerequisitesModule

@[expose] public section

/-!
# The quadratic part of the F rows, before and after translation

Every F row has total degree at most two (`RowEvaluation.fRow_eq_shapePolynomial`).  This module
proves:

* a generic translation lemma: for any polynomial `f` over a commutative ring and any point `P`,
  the coefficients of `translate P f` and of `f` agree at every exponent of degree at least the
  total degree of `f`; in particular `homogeneousComponent n (translate P f) = homogeneousComponent n f`
  whenever `totalDegree f ≤ n` (`homogeneousComponent_translate_of_totalDegree_le`);
* the explicit quadratic part of each row: `homogeneousComponent 2 (fRow h t r)` and
  `homogeneousComponent 2 (translate P (fRow h t r))` both equal the table polynomial
  `∑_{(i,j,c) ∈ quadTable r} C (s·c) · X i · X j`, with `s = h` for idempotency rows and `s = 1`
  otherwise (`quadraticScale`);  trace and frame-unit rows have quadratic part `0`;
* a coefficient form: after orienting every term so that `i ≤ j`, the coefficient of
  `X i · X j` is the scale times the sum of the oriented table entries at `(i, j)`
  (`coeff_quadraticPolynomial_pair`).

`translate` is the consumer's `PolynomialJets.translate P f = eval₂ C (fun j => X j + C (P j)) f`.
-/

namespace QuarticCertificate.RowBridge

open MvPolynomial PolynomialJets
open NativePolynomial.ConfigurationResiduals ConfigurationResidualIndices

/-! ## Translation as a ring homomorphism -/

section Translate

variable {σ R : Type*} [CommRing R]

theorem translate_eq_eval₂Hom (P : σ → R) (f : MvPolynomial σ R) :
    translate P f = eval₂Hom C (fun j => X j + C (P j)) f := rfl

@[simp] theorem translate_C (P : σ → R) (a : R) : translate P (C a) = C a := by
  rw [translate_eq_eval₂Hom, eval₂Hom_C]

@[simp] theorem translate_X (P : σ → R) (i : σ) : translate P (X i) = X i + C (P i) := by
  rw [translate_eq_eval₂Hom, eval₂Hom_X']

theorem translate_add (P : σ → R) (f g : MvPolynomial σ R) :
    translate P (f + g) = translate P f + translate P g := by
  simp only [translate_eq_eval₂Hom, map_add]

theorem translate_mul (P : σ → R) (f g : MvPolynomial σ R) :
    translate P (f * g) = translate P f * translate P g := by
  simp only [translate_eq_eval₂Hom, map_mul]

theorem translate_list_sum {α : Type*} (P : σ → R) (l : List α) (F : α → MvPolynomial σ R) :
    translate P (l.map F).sum = (l.map fun e => translate P (F e)).sum := by
  rw [translate_eq_eval₂Hom, map_list_sum, List.map_map]
  rfl

theorem translate_monomial_mul_X (P : σ → R) (f : MvPolynomial σ R) (i : σ) :
    translate P (f * X i) = translate P f * X i + translate P f * C (P i) := by
  rw [translate_mul, translate_X, mul_add]

/-! ## The top coefficients are translation invariant (generic) -/

/-- If every exponent in the support of `f` has degree at most `degree e`, then the coefficient
of `e` is unchanged by translation.  Proved for monomials by induction on the exponent
(`induction_on_monomial`), then by linearity (`as_sum`). -/
theorem coeff_translate_of_support_degree_le (P : σ → R) (f : MvPolynomial σ R)
    (e : σ →₀ ℕ) (hf : ∀ d ∈ f.support, d.degree ≤ e.degree) :
    (translate P f).coeff e = f.coeff e := by
  classical
  -- the statement for one monomial, for every exponent of large enough degree
  have hmonomial : ∀ (s : σ →₀ ℕ) (a : R), ∀ e : σ →₀ ℕ,
      (∀ d ∈ (monomial s a).support, d.degree ≤ e.degree) →
      (translate P (monomial s a)).coeff e = (monomial s a).coeff e := by
    refine induction_on_monomial (motive := fun p => ∀ e : σ →₀ ℕ,
      (∀ d ∈ p.support, d.degree ≤ e.degree) → (translate P p).coeff e = p.coeff e) ?_ ?_
    · intro a e _
      rw [translate_C]
    · intro p n ih e he
      have hshift : ∀ d ∈ p.support, d.degree + 1 ≤ e.degree := by
        intro d hd
        have := he (d + Finsupp.single n 1) (by
          rw [support_mul_X]
          exact Finset.mem_map_of_mem _ hd)
        simpa [map_add, Finsupp.degree_single] using this
      have hnot : p.coeff e = 0 := by
        by_contra hne
        have := hshift e (mem_support_iff.mpr hne)
        omega
      have htop : (translate P p).coeff e = 0 := by
        rw [ih e (fun d hd => by have := hshift d hd; omega), hnot]
      rw [translate_monomial_mul_X, MvPolynomial.coeff_add, mul_comm (translate P p) (C (P n)), coeff_C_mul,
        htop, mul_zero, add_zero, coeff_mul_X', coeff_mul_X']
      split_ifs with hn
      · apply ih
        intro d hd
        have hd' := hshift d hd
        have hle : Finsupp.single n 1 ≤ e := by
          rw [Finsupp.single_le_iff]
          exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hn)
        have hsplit : e = (e - Finsupp.single n 1) + Finsupp.single n 1 :=
          (tsub_add_cancel_of_le hle).symm
        have hdeg : e.degree = (e - Finsupp.single n 1).degree + 1 := by
          conv_lhs => rw [hsplit]
          rw [map_add, Finsupp.degree_single]
        omega
      · rfl
  conv_lhs => rw [as_sum f]
  rw [translate_eq_eval₂Hom, map_sum, coeff_sum]
  conv_rhs => rw [as_sum f, coeff_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← translate_eq_eval₂Hom]
  apply hmonomial
  intro d' hd'
  have hd'' : d' = d := by
    by_contra hne
    rw [support_monomial] at hd'
    split_ifs at hd' <;> simp_all
  rw [hd'']
  exact hf d hd

/-- **Translation invariance of the top component.** If `totalDegree f ≤ n`, the degree-`n`
homogeneous component of `translate P f` equals that of `f`. -/
theorem homogeneousComponent_translate_of_totalDegree_le (P : σ → R) (f : MvPolynomial σ R)
    {n : ℕ} (hf : f.totalDegree ≤ n) :
    homogeneousComponent n (translate P f) = homogeneousComponent n f := by
  ext e
  rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
  split_ifs with he
  · apply coeff_translate_of_support_degree_le
    intro d hd
    have := le_totalDegree hd
    rw [he]
    exact le_trans this hf
  · rfl

end Translate

/-! ## Quadratic part of the shape polynomials -/

variable {R : Type*} [CommRing R]

theorem isHomogeneous_C_mul_X_mul_X (c : R) (i j : Fin 1053) :
    (C c * X i * X j : MvPolynomial (Fin 1053) R).IsHomogeneous 2 :=
  ((isHomogeneous_C _ c).mul (isHomogeneous_X R i)).mul (isHomogeneous_X R j)

theorem isHomogeneous_C_mul_X (c : R) (i : Fin 1053) :
    (C c * X i : MvPolynomial (Fin 1053) R).IsHomogeneous 1 := by
  simpa using (isHomogeneous_C _ c).mul (isHomogeneous_X R i)

theorem homogeneousComponent_two_C_mul_X_mul_X (c : R) (i j : Fin 1053) :
    homogeneousComponent 2 (C c * X i * X j : MvPolynomial (Fin 1053) R) = C c * X i * X j :=
  homogeneousComponent_eq_self (isHomogeneous_C_mul_X_mul_X c i j)

theorem homogeneousComponent_two_C_mul_X (c : R) (i : Fin 1053) :
    homogeneousComponent 2 (C c * X i : MvPolynomial (Fin 1053) R) = 0 := by
  rw [homogeneousComponent_of_mem (isHomogeneous_C_mul_X c i)]
  rfl

theorem homogeneousComponent_two_C (c : R) :
    homogeneousComponent 2 (C c : MvPolynomial (Fin 1053) R) = 0 := by
  rw [homogeneousComponent_of_mem (isHomogeneous_C (Fin 1053) c)]
  rfl

/-- The translate of one quadratic term, expanded by degree. -/
theorem translate_quadraticTerm (P : Fin 1053 → R) (c : R) (i j : Fin 1053) :
    translate P (C c * X i * X j) =
      C c * X i * X j + (C (c * P j) * X i + C (c * P i) * X j) + C (c * P i * P j) := by
  simp only [translate_mul, translate_C, translate_X, map_mul]
  ring

/-- The translate of one linear term. -/
theorem translate_linearTerm (P : Fin 1053 → R) (c : R) (i : Fin 1053) :
    translate P (C c * X i) = C c * X i + C (c * P i) := by
  simp only [translate_mul, translate_C, translate_X, map_mul]
  ring

theorem homogeneousComponent_two_quadraticPolynomial (a : R)
    (l : List (Fin 1053 × Fin 1053 × ℤ)) :
    homogeneousComponent 2 (quadraticPolynomial a l) = quadraticPolynomial a l := by
  unfold quadraticPolynomial
  rw [map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  exact homogeneousComponent_two_C_mul_X_mul_X _ _ _

theorem homogeneousComponent_two_linearPolynomial (l : List (Fin 1053 × ℤ)) :
    homogeneousComponent 2 (linearPolynomial l : MvPolynomial (Fin 1053) R) = 0 := by
  unfold linearPolynomial
  rw [map_list_sum, List.map_map]
  apply List.sum_eq_zero
  intro p hp
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hp
  exact homogeneousComponent_two_C_mul_X _ _

theorem homogeneousComponent_two_translate_quadraticPolynomial (P : Fin 1053 → R) (a : R)
    (l : List (Fin 1053 × Fin 1053 × ℤ)) :
    homogeneousComponent 2 (translate P (quadraticPolynomial a l)) = quadraticPolynomial a l := by
  unfold quadraticPolynomial
  rw [translate_list_sum, map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, translate_quadraticTerm, map_add,
    homogeneousComponent_two_C_mul_X_mul_X, homogeneousComponent_two_C_mul_X,
    homogeneousComponent_two_C, add_zero]

theorem homogeneousComponent_two_translate_linearPolynomial (P : Fin 1053 → R)
    (l : List (Fin 1053 × ℤ)) :
    homogeneousComponent 2 (translate P (linearPolynomial l : MvPolynomial (Fin 1053) R)) = 0 := by
  unfold linearPolynomial
  rw [translate_list_sum, map_list_sum, List.map_map]
  apply List.sum_eq_zero
  intro p hp
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hp
  simp only [Function.comp_apply, translate_linearTerm, map_add,
    homogeneousComponent_two_C_mul_X, homogeneousComponent_two_C, add_zero]

/-- The quadratic part of a shape polynomial is its table polynomial. -/
theorem homogeneousComponent_two_shapePolynomial (h t : R) (s : RowShape) :
    homogeneousComponent 2 (shapePolynomial h t s) =
      quadraticPolynomial (quadraticScale h s) s.quadratic := by
  rw [shapePolynomial, map_add, map_add, homogeneousComponent_two_quadraticPolynomial,
    homogeneousComponent_two_linearPolynomial, homogeneousComponent_two_C, add_zero, add_zero]

/-- The quadratic part of a translated shape polynomial is the same table polynomial. -/
theorem homogeneousComponent_two_translate_shapePolynomial (P : Fin 1053 → R) (h t : R)
    (s : RowShape) :
    homogeneousComponent 2 (translate P (shapePolynomial h t s)) =
      quadraticPolynomial (quadraticScale h s) s.quadratic := by
  rw [shapePolynomial, translate_add, translate_add, translate_C, map_add, map_add,
    homogeneousComponent_two_translate_quadraticPolynomial,
    homogeneousComponent_two_translate_linearPolynomial, homogeneousComponent_two_C,
    add_zero, add_zero]

/-! ## The F rows -/

/-- The quadratic table of row `r`: terms `(i, j, c)` meaning `c · X i · X j`. -/
def quadTable (r : Fin 2184) : List (Fin 1053 × Fin 1053 × ℤ) := (rowShape r).quadratic

/-- Whether the quadratic table of row `r` carries the factor `h` (idempotency rows). -/
def quadScaledByHalf (r : Fin 2184) : Bool := (rowShape r).halfScaled

theorem quadraticScale_rowShape (h : R) (r : Fin 2184) :
    quadraticScale h (rowShape r) = if quadScaledByHalf r then h else 1 := rfl

/-- The quadratic part of an F row is its explicit table polynomial. -/
theorem homogeneousComponent_two_fRow (h t : R) (r : Fin 2184) :
    homogeneousComponent 2 (fRow h t r) =
      quadraticPolynomial (quadraticScale h (rowShape r)) (quadTable r) := by
  rw [fRow_eq_shapePolynomial, homogeneousComponent_two_shapePolynomial]
  rfl

/-- **Quadratic part of a translated row.** Translation does not change it. -/
theorem homogeneousComponent_two_translate_fRow (P : Fin 1053 → R) (h t : R) (r : Fin 2184) :
    homogeneousComponent 2 (translate P (fRow h t r)) =
      quadraticPolynomial (quadraticScale h (rowShape r)) (quadTable r) := by
  rw [fRow_eq_shapePolynomial, homogeneousComponent_two_translate_shapePolynomial]
  rfl

/-- Translation does not change the quadratic part of any F row. -/
theorem homogeneousComponent_two_translate_fRow_eq (P : Fin 1053 → R) (h t : R) (r : Fin 2184) :
    homogeneousComponent 2 (translate P (fRow h t r)) = homogeneousComponent 2 (fRow h t r) := by
  rw [homogeneousComponent_two_translate_fRow, homogeneousComponent_two_fRow]

/-- Trace rows are linear: their quadratic table is empty. -/
theorem quadTable_trace (i : Fin 39) : quadTable (fNumber (fTrace i)) = [] := by
  simp only [quadTable, rowShape, Equiv.symm_apply_apply, fTrace, labelShape]

/-- Frame-unit rows are linear: their quadratic table is empty. -/
theorem quadTable_sum (f : Fin 13) (k : Fin 27) : quadTable (fNumber (fSum f k)) = [] := by
  simp only [quadTable, rowShape, Equiv.symm_apply_apply, fSum, labelShape]

/-- Computable value of the quadratic part of row `r` at a point `x`. -/
def quadraticPartValue (h : R) (r : Fin 2184) (x : Fin 1053 → R) : R :=
  quadraticValue (quadraticScale h (rowShape r)) (quadTable r) x

theorem eval_homogeneousComponent_two_translate_fRow (P x : Fin 1053 → R) (h t : R)
    (r : Fin 2184) :
    eval x (homogeneousComponent 2 (translate P (fRow h t r))) = quadraticPartValue h r x := by
  rw [homogeneousComponent_two_translate_fRow, eval_quadraticPolynomial]
  rfl

/-! ## Coefficient (symmetric matrix) form -/

/-- Orient a quadratic term so that its first index is the smaller one. -/
def orientTerm (e : Fin 1053 × Fin 1053 × ℤ) : Fin 1053 × Fin 1053 × ℤ :=
  if e.1 ≤ e.2.1 then e else (e.2.1, e.1, e.2.2)

/-- A quadratic table with every term oriented (`i ≤ j`): the upper-triangular sparse form of
the symmetric coefficient matrix, with repeated positions not yet merged. -/
def orientedTable (l : List (Fin 1053 × Fin 1053 × ℤ)) : List (Fin 1053 × Fin 1053 × ℤ) :=
  l.map orientTerm

theorem quadraticPolynomial_orientedTable (a : R) (l : List (Fin 1053 × Fin 1053 × ℤ)) :
    quadraticPolynomial a (orientedTable l) = quadraticPolynomial a l := by
  unfold quadraticPolynomial orientedTable
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply, orientTerm]
  split_ifs <;> ring

/-- The merged integer coefficient at the oriented position `(i, j)`. -/
def tableCoefficient (l : List (Fin 1053 × Fin 1053 × ℤ)) (i j : Fin 1053) : ℤ :=
  ((orientedTable l).map fun e => if e.1 = i ∧ e.2.1 = j then e.2.2 else 0).sum

/-- The orientation of an index pair (smaller index first). -/
def orientPair (p q : Fin 1053) : Fin 1053 × Fin 1053 := if p ≤ q then (p, q) else (q, p)

theorem orientTerm_fst_snd (e : Fin 1053 × Fin 1053 × ℤ) :
    ((orientTerm e).1, (orientTerm e).2.1) = orientPair e.1 e.2.1 ∧ (orientTerm e).2.2 = e.2.2 := by
  unfold orientTerm orientPair
  split_ifs <;> exact ⟨rfl, rfl⟩

/-- Two degree-two exponents agree exactly when the oriented index pairs agree. -/
theorem single_add_single_eq_iff {p q i j : Fin 1053} (hij : i ≤ j) :
    Finsupp.single p 1 + Finsupp.single q 1 = Finsupp.single i 1 + Finsupp.single j 1 ↔
      orientPair p q = (i, j) := by
  classical
  have hinj : Function.Injective (Finsupp.toMultiset : (Fin 1053 →₀ ℕ) → Multiset (Fin 1053)) :=
    fun a b hab => by rw [← Finsupp.toMultiset_toFinsupp a, hab, Finsupp.toMultiset_toFinsupp]
  rw [← hinj.eq_iff]
  simp only [map_add, Finsupp.toMultiset_single, one_nsmul, Multiset.singleton_add]
  rw [Multiset.cons_eq_cons]
  unfold orientPair
  constructor
  · rintro (⟨rfl, hqj⟩ | ⟨hpi, cs, hq, hp⟩)
    · have hqj' : q = j := by simpa using hqj
      subst hqj'
      simp [hij]
    · obtain ⟨rfl, rfl⟩ := (Multiset.singleton_eq_cons_iff _).mp hq
      obtain ⟨rfl, -⟩ := (Multiset.singleton_eq_cons_iff _).mp hp
      have hlt := lt_of_le_of_ne hij (Ne.symm hpi)
      simp [not_le.mpr hlt]
  · intro h
    split_ifs at h with hpq
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨rfl, rfl⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hne : p ≠ q := fun hpq' => hpq (le_of_eq hpq')
      exact Or.inr ⟨hne, 0, by simp, by simp⟩

theorem C_mul_X_mul_X_eq_monomial (c : R) (p q : Fin 1053) :
    (C c * X p * X q : MvPolynomial (Fin 1053) R) =
      monomial (Finsupp.single p 1 + Finsupp.single q 1) c := by
  simp only [X, C_mul_monomial, monomial_mul_monomial, mul_one]

/-- The coefficient of `X i · X j` (`i ≤ j`) in one quadratic term. -/
theorem coeff_quadraticTerm_pair (c : R) (p q : Fin 1053) {i j : Fin 1053} (hij : i ≤ j) :
    (C c * X p * X q : MvPolynomial (Fin 1053) R).coeff
        (Finsupp.single i 1 + Finsupp.single j 1) =
      if orientPair p q = (i, j) then c else 0 := by
  classical
  rw [C_mul_X_mul_X_eq_monomial, coeff_monomial]
  simp only [single_add_single_eq_iff hij]

/-- **Coefficient form.** For `i ≤ j`, the coefficient of `X i · X j` in the table polynomial is
the scale times the merged oriented table coefficient at `(i, j)`. -/
theorem coeff_quadraticPolynomial_pair (a : R) (l : List (Fin 1053 × Fin 1053 × ℤ))
    {i j : Fin 1053} (hij : i ≤ j) :
    (quadraticPolynomial a l).coeff (Finsupp.single i 1 + Finsupp.single j 1) =
      a * (tableCoefficient l i j : R) := by
  classical
  unfold quadraticPolynomial tableCoefficient orientedTable
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons, MvPolynomial.coeff_add, ih, Int.cast_add, mul_add]
    congr 1
    rw [coeff_quadraticTerm_pair (a * (e.2.2 : R)) e.1 e.2.1 hij]
    obtain ⟨hpair, hval⟩ := orientTerm_fst_snd e
    have hiff : ((orientTerm e).1 = i ∧ (orientTerm e).2.1 = j) ↔ orientPair e.1 e.2.1 = (i, j) := by
      rw [← hpair, Prod.mk.injEq]
    by_cases h : orientPair e.1 e.2.1 = (i, j)
    · rw [if_pos h, if_pos (hiff.mpr h), hval]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mp h')), Int.cast_zero, mul_zero]

/-- The coefficient of `X i · X j` (`i ≤ j`) in the quadratic part of the translated row `r`. -/
theorem coeff_homogeneousComponent_two_translate_fRow (P : Fin 1053 → R) (h t : R)
    (r : Fin 2184) {i j : Fin 1053} (hij : i ≤ j) :
    (homogeneousComponent 2 (translate P (fRow h t r))).coeff
        (Finsupp.single i 1 + Finsupp.single j 1) =
      quadraticScale h (rowShape r) * (tableCoefficient (quadTable r) i j : R) := by
  rw [homogeneousComponent_two_translate_fRow, coeff_quadraticPolynomial_pair _ _ hij]

end QuarticCertificate.RowBridge

module

public import RowQuadraticPart

@[expose] public section

/-!
# The Jacobian entries of the translated F rows

For a point `P` and a configuration variable `a`, the consumer's linear coefficient matrix
`PolynomialJets.equationLinearMatrix (fun r => translate P (fRow h t r)) r a`
is the coefficient of `X a` in `translate P (fRow h t r)`, i.e. the partial derivative of the
row at `P`.  This module gives it as a computable expression over the row's sparse table:

  `jacobianEntry h t r P a = ∑_{(i,j,c) ∈ quadTable r} s·c·([i = a]·P j + [j = a]·P i)
                             + ∑_{(i,c) ∈ linear part} [i = a]·c`

with `s = h` for idempotency rows and `s = 1` otherwise, proves
`equationLinearMatrix_translate_fRow`, and supplies a sparse-list form `jacobianRow` (one entry
per occurrence of a variable, looked up by summation), the vanishing of the entry outside the
row's slot variables, a dense-on-slots list `jacobianRowOnSlots`, and a kernel-checkable
criterion (`sparseLookup_eq_jacobianEntry_of_check`) that a literal sparse row is the Jacobian
row.  Everything is generic over a commutative ring `R`.
-/

namespace QuarticCertificate.RowBridge

open MvPolynomial PolynomialJets
open NativePolynomial.ConfigurationResiduals ConfigurationResidualIndices

variable {R : Type*} [CommRing R]

/-! ## Coefficients of `X a` in the elementary terms -/

theorem coeff_list_sum {α : Type*} (m : Fin 1053 →₀ ℕ) (l : List α)
    (F : α → MvPolynomial (Fin 1053) R) :
    (l.map F).sum.coeff m = (l.map fun e => (F e).coeff m).sum := by
  induction l with
  | nil => simp
  | cons e l ih => simp only [List.map_cons, List.sum_cons, MvPolynomial.coeff_add, ih]

theorem coeff_single_one_C (c : R) (a : Fin 1053) :
    (C c : MvPolynomial (Fin 1053) R).coeff (Finsupp.single a 1) = 0 := by
  classical
  rw [coeff_C, if_neg]
  exact fun h => Finsupp.single_ne_zero.mpr one_ne_zero h.symm

theorem coeff_single_one_C_mul_X (c : R) (i a : Fin 1053) :
    (C c * X i : MvPolynomial (Fin 1053) R).coeff (Finsupp.single a 1) =
      if i = a then c else 0 := by
  classical
  rw [coeff_C_mul, coeff_X]
  simp only [Finsupp.single_left_inj one_ne_zero]
  split_ifs <;> simp

theorem coeff_single_one_C_mul_X_mul_X (c : R) (i j a : Fin 1053) :
    (C c * X i * X j : MvPolynomial (Fin 1053) R).coeff (Finsupp.single a 1) = 0 :=
  (isHomogeneous_C_mul_X_mul_X c i j).coeff_eq_zero (by simp)

/-- The coefficient of `X a` in the translate of one quadratic term `c · X i · X j`. -/
theorem coeff_single_one_translate_quadraticTerm (P : Fin 1053 → R) (c : R) (i j a : Fin 1053) :
    (translate P (C c * X i * X j)).coeff (Finsupp.single a 1) =
      c * ((if i = a then P j else 0) + (if j = a then P i else 0)) := by
  rw [translate_quadraticTerm]
  simp only [MvPolynomial.coeff_add, coeff_single_one_C_mul_X_mul_X, coeff_single_one_C_mul_X,
    coeff_single_one_C, zero_add, add_zero]
  split_ifs <;> ring

/-- The coefficient of `X a` in the translate of one linear term `c · X i`. -/
theorem coeff_single_one_translate_linearTerm (P : Fin 1053 → R) (c : R) (i a : Fin 1053) :
    (translate P (C c * X i)).coeff (Finsupp.single a 1) = if i = a then c else 0 := by
  rw [translate_linearTerm, MvPolynomial.coeff_add, coeff_single_one_C_mul_X, coeff_single_one_C,
    add_zero]

/-! ## The Jacobian entry of a shape -/

/-- Computable coefficient of `X a` in `translate P (shapePolynomial h t s)`. -/
def shapeJacobianEntry (h : R) (s : RowShape) (P : Fin 1053 → R) (a : Fin 1053) : R :=
  (s.quadratic.map fun e => quadraticScale h s * (e.2.2 : R) *
      ((if e.1 = a then P e.2.1 else 0) + (if e.2.1 = a then P e.1 else 0))).sum +
    (s.linear.map fun e => if e.1 = a then (e.2 : R) else 0).sum

theorem coeff_single_one_translate_shapePolynomial (P : Fin 1053 → R) (h t : R) (s : RowShape)
    (a : Fin 1053) :
    (translate P (shapePolynomial h t s)).coeff (Finsupp.single a 1) =
      shapeJacobianEntry h s P a := by
  rw [shapePolynomial, translate_add, translate_add, translate_C, quadraticPolynomial,
    linearPolynomial, translate_list_sum, translate_list_sum, MvPolynomial.coeff_add,
    MvPolynomial.coeff_add, coeff_single_one_C, add_zero, coeff_list_sum, coeff_list_sum,
    shapeJacobianEntry]
  simp only [coeff_single_one_translate_quadraticTerm, coeff_single_one_translate_linearTerm]

/-! ## The F rows -/

/-- **Jacobian entry** of row `r` at the point `P` in the variable `a` (computable). -/
def jacobianEntry (h t : R) (r : Fin 2184) (P : Fin 1053 → R) (a : Fin 1053) : R :=
  shapeJacobianEntry h (rowShape r) P a

/-- **Jacobian bridge.** The consumer's linear coefficient matrix of the translated F rows is
the computable `jacobianEntry`. -/
theorem equationLinearMatrix_translate_fRow (P : Fin 1053 → R) (h t : R) (r : Fin 2184)
    (a : Fin 1053) :
    equationLinearMatrix (fun r => translate P (fRow h t r)) r a = jacobianEntry h t r P a := by
  rw [equationLinearMatrix, fRow_eq_shapePolynomial,
    coeff_single_one_translate_shapePolynomial]
  rfl

/-! ## Sparse-list form -/

/-- Value at `a` of a sparse list of `(index, value)` pairs (repeated indices are summed). -/
def sparseLookup (l : List (Fin 1053 × R)) (a : Fin 1053) : R :=
  (l.map fun e => if e.1 = a then e.2 else 0).sum

/-- The Jacobian row of a shape as a sparse list: two entries per quadratic term, one per
linear term. -/
def shapeJacobianRow (h : R) (s : RowShape) (P : Fin 1053 → R) : List (Fin 1053 × R) :=
  s.quadratic.flatMap (fun e => [(e.1, quadraticScale h s * (e.2.2 : R) * P e.2.1),
      (e.2.1, quadraticScale h s * (e.2.2 : R) * P e.1)]) ++
    s.linear.map fun e => (e.1, (e.2 : R))

theorem sparseLookup_shapeJacobianRow (h : R) (s : RowShape) (P : Fin 1053 → R) (a : Fin 1053) :
    sparseLookup (shapeJacobianRow h s P) a = shapeJacobianEntry h s P a := by
  unfold sparseLookup shapeJacobianRow shapeJacobianEntry
  rw [List.map_append, List.sum_append, List.map_map]
  congr 1
  · generalize s.quadratic = l
    induction l with
    | nil => simp
    | cons e l ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      congr 1
      split_ifs <;> ring

/-- The Jacobian row of row `r` at `P` as a sparse list supported on the row's variables. -/
def jacobianRow (h t : R) (r : Fin 2184) (P : Fin 1053 → R) : List (Fin 1053 × R) :=
  shapeJacobianRow h (rowShape r) P

theorem jacobianEntry_eq_sparseLookup (h t : R) (r : Fin 2184) (P : Fin 1053 → R) (a : Fin 1053) :
    jacobianEntry h t r P a = sparseLookup (jacobianRow h t r P) a :=
  (sparseLookup_shapeJacobianRow h _ P a).symm

/-- Every index of `jacobianRow` is a variable of one of the row's slots. -/
theorem variableSlot_mem_rowSlots_of_mem_jacobianRow (h t : R) (r : Fin 2184)
    (P : Fin 1053 → R) {e : Fin 1053 × R} (he : e ∈ jacobianRow h t r P) :
    variableSlot e.1 ∈ rowSlots r := by
  apply variableSlot_mem_rowSlots r
  simp only [jacobianRow, shapeJacobianRow, List.mem_append, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at he
  simp only [shapeVariables, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map]
  rcases he with ⟨q, hq, rfl | rfl⟩ | ⟨q, hq, rfl⟩
  · exact Or.inl ⟨q, hq, Or.inl rfl⟩
  · exact Or.inl ⟨q, hq, Or.inr rfl⟩
  · exact Or.inr ⟨q, hq, rfl⟩

/-- A sparse lookup vanishes at an index none of whose entries carries it. -/
theorem sparseLookup_eq_zero (l : List (Fin 1053 × R)) (a : Fin 1053)
    (hl : ∀ e ∈ l, e.1 ≠ a) : sparseLookup l a = 0 := by
  unfold sparseLookup
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  rw [if_neg (hl e he)]

/-- The Jacobian entry vanishes at every variable outside the row's slots. -/
theorem jacobianEntry_eq_zero_of_not_mem (h t : R) (r : Fin 2184) (P : Fin 1053 → R)
    {a : Fin 1053} (ha : variableSlot a ∉ rowSlots r) : jacobianEntry h t r P a = 0 := by
  rw [jacobianEntry_eq_sparseLookup]
  apply sparseLookup_eq_zero
  intro e he hea
  exact ha (hea ▸ variableSlot_mem_rowSlots_of_mem_jacobianRow h t r P he)

/-- Each variable is the coordinate `v mod 27` of its slot `v / 27`. -/
def variableCoordinate (v : Fin 1053) : Fin 27 := ⟨v.val % 27, Nat.mod_lt _ (by decide)⟩

theorem variableIndex_slot_coordinate (v : Fin 1053) :
    variableIndex (variableSlot v) (variableCoordinate v) = v := by
  apply Fin.ext
  simp only [variableIndex_val, variableSlot, variableCoordinate]
  omega

/-- The Jacobian row of `r` evaluated at every variable of its slots (zeros included), in the
order slot by slot, coordinate `0 … 26` within a slot. -/
def jacobianRowOnSlots (h t : R) (r : Fin 2184) (P : Fin 1053 → R) : List (Fin 1053 × R) :=
  (rowSlots r).flatMap fun p =>
    (List.finRange 27).map fun k => (variableIndex p k, jacobianEntry h t r P (variableIndex p k))

/-- **Kernel-checkable criterion.** A literal sparse row `L` equals the Jacobian row of `r` at
`P` (as a function of the variable) as soon as (i) at every variable of the row's slots the
lookup of `L` agrees with `jacobianEntry`, and (ii) every index of `L` lies in a slot of the row.
Both hypotheses are Boolean checks over at most 81 variables. -/
theorem sparseLookup_eq_jacobianEntry_of_check [DecidableEq R] (h t : R) (r : Fin 2184)
    (P : Fin 1053 → R) (L : List (Fin 1053 × R))
    (hslots : (rowSlots r).all (fun p => (List.finRange 27).all fun k =>
      decide (sparseLookup L (variableIndex p k) = jacobianEntry h t r P (variableIndex p k))) = true)
    (hsupport : L.all (fun e => decide (variableSlot e.1 ∈ rowSlots r)) = true) :
    ∀ a, sparseLookup L a = jacobianEntry h t r P a := by
  intro a
  by_cases ha : variableSlot a ∈ rowSlots r
  · have := List.all_eq_true.mp hslots _ ha
    have := List.all_eq_true.mp this (variableCoordinate a) (List.mem_finRange _)
    rw [variableIndex_slot_coordinate] at this
    exact of_decide_eq_true this
  · rw [jacobianEntry_eq_zero_of_not_mem h t r P ha]
    apply sparseLookup_eq_zero
    intro e he hea
    have := of_decide_eq_true (List.all_eq_true.mp hsupport e he)
    exact ha (hea ▸ this)

end QuarticCertificate.RowBridge

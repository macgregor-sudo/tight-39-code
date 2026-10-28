module

public import NativeSparse
public import NativeConfigurationPolynomialResiduals

@[expose] public section

/-!
# Computable evaluation of the 2184 original F rows

The kernel cannot evaluate `MvPolynomial`.  This module rewrites every F row
`NativePolynomial.ConfigurationResiduals.fRow h t r` (over an arbitrary commutative ring `R`)
as an explicit sparse polynomial of degree at most two, described by a finite
`RowShape`: a list of quadratic terms `(i, j, c)` meaning `c · X i · X j` (all multiplied
by `h` for the idempotency rows), a list of linear terms `(i, c)` meaning `c · X i`, and a
constant `c₀ - [t]`.

Main results (generic over `CommRing R`):
* `fRow_eq_shapePolynomial : fRow h t r = shapePolynomial h t (rowShape r)`;
* `eval_fRow : eval x (fRow h t r) = rowValue h t r x`, where `rowValue` is a computable
  ring expression with at most 27 products of coordinates;
* `rowValue_congr`: `rowValue h t r x` only reads the coordinates of the row's point slots
  `rowSlots r` (one slot for idempotency and trace rows, three for frame-unit rows, two
  for pairing rows).

The quadratic terms of an idempotency row are the sparse output tables `tbl0 … tbl26` of the
native coordinate product, proved against the integer structure constants in the four-sheets
module `NativeSparse` (`coordinateProduct_of_table`, `numerator_tbl0 … numerator_tbl26`);
this module imports and applies them.  Nothing is assumed beyond the imported definitions.
-/

namespace QuarticCertificate.RowBridge

open MvPolynomial
open NativePolynomial.CoordinateMaps NativePolynomial.ConfigurationResiduals
open NativePolynomial.IntegralStructureConstants
open ConfigurationResidualIndices FrameResiduals
open TitsS.Sparse

/-! ## The sparse product tables, indexed by the output coordinate -/

/-- The sparse table of the integer structure constants `numerator i j k` for output
coordinate `k`, taken from the four-sheets module `NativeSparse`. -/
def productTable : Fin 27 → List (Fin 27 × Fin 27 × ℤ) :=
  ![tbl0, tbl1, tbl2, tbl3, tbl4, tbl5, tbl6, tbl7, tbl8, tbl9, tbl10, tbl11, tbl12, tbl13,
    tbl14, tbl15, tbl16, tbl17, tbl18, tbl19, tbl20, tbl21, tbl22, tbl23, tbl24, tbl25, tbl26]

/-- Every output coordinate of the integer structure constants is the sum over its table. -/
theorem numerator_eq_productTable (k : Fin 27) :
    ∀ i j, numerator i j k = sumIte (productTable k) i j := by
  fin_cases k
  exacts [numerator_tbl0, numerator_tbl1, numerator_tbl2, numerator_tbl3, numerator_tbl4,
    numerator_tbl5, numerator_tbl6, numerator_tbl7, numerator_tbl8, numerator_tbl9,
    numerator_tbl10, numerator_tbl11, numerator_tbl12, numerator_tbl13, numerator_tbl14,
    numerator_tbl15, numerator_tbl16, numerator_tbl17, numerator_tbl18, numerator_tbl19,
    numerator_tbl20, numerator_tbl21, numerator_tbl22, numerator_tbl23, numerator_tbl24,
    numerator_tbl25, numerator_tbl26]

/-! ## Sparse quadratic shapes -/

/-- A sparse polynomial of degree at most two in the 1053 configuration variables.
* `quadratic`: terms `(i, j, c)` standing for `c · X i · X j`;
* `halfScaled`: whether every quadratic term is additionally multiplied by the product
  parameter `h` (true exactly for the idempotency rows);
* `linear`: terms `(i, c)` standing for `c · X i`;
* `constant`, `subtractsThird`: the constant term is `constant - t` if `subtractsThird`,
  and `constant` otherwise. -/
structure RowShape where
  quadratic : List (Fin 1053 × Fin 1053 × ℤ)
  halfScaled : Bool
  linear : List (Fin 1053 × ℤ)
  constant : ℤ
  subtractsThird : Bool

variable {R : Type*} [CommRing R]

/-- The common factor of the quadratic terms: `h` for idempotency rows, `1` otherwise. -/
def quadraticScale (h : R) (s : RowShape) : R := if s.halfScaled then h else 1

/-- The constant term of a shape. -/
def constantTerm (t : R) (s : RowShape) : R :=
  (s.constant : R) - if s.subtractsThird then t else 0

/-- The polynomial `∑ a · c · X i · X j` of a list of quadratic terms. -/
noncomputable def quadraticPolynomial (a : R) (l : List (Fin 1053 × Fin 1053 × ℤ)) :
    MvPolynomial (Fin 1053) R :=
  (l.map fun e => C (a * (e.2.2 : R)) * X e.1 * X e.2.1).sum

/-- The polynomial `∑ c · X i` of a list of linear terms. -/
noncomputable def linearPolynomial (l : List (Fin 1053 × ℤ)) : MvPolynomial (Fin 1053) R :=
  (l.map fun e => C (e.2 : R) * X e.1).sum

/-- The polynomial described by a shape, at the parameters `h` (product) and `t` (pairing). -/
noncomputable def shapePolynomial (h t : R) (s : RowShape) : MvPolynomial (Fin 1053) R :=
  quadraticPolynomial (quadraticScale h s) s.quadratic + linearPolynomial s.linear +
    C (constantTerm t s)

/-- Computable value of a list of quadratic terms at a point `x`. -/
def quadraticValue (a : R) (l : List (Fin 1053 × Fin 1053 × ℤ)) (x : Fin 1053 → R) : R :=
  (l.map fun e => a * (e.2.2 : R) * x e.1 * x e.2.1).sum

/-- Computable value of a list of linear terms at a point `x`. -/
def linearValue (l : List (Fin 1053 × ℤ)) (x : Fin 1053 → R) : R :=
  (l.map fun e => (e.2 : R) * x e.1).sum

/-- Computable value of a shape at a point `x`. -/
def shapeValue (h t : R) (s : RowShape) (x : Fin 1053 → R) : R :=
  quadraticValue (quadraticScale h s) s.quadratic x + linearValue s.linear x + constantTerm t s

theorem eval_quadraticPolynomial (a : R) (l : List (Fin 1053 × Fin 1053 × ℤ))
    (x : Fin 1053 → R) : eval x (quadraticPolynomial a l) = quadraticValue a l x := by
  simp only [quadraticPolynomial, quadraticValue, map_list_sum, List.map_map,
    Function.comp_def, map_mul, eval_C, eval_X]

theorem eval_linearPolynomial (l : List (Fin 1053 × ℤ)) (x : Fin 1053 → R) :
    eval x (linearPolynomial l) = linearValue l x := by
  simp only [linearPolynomial, linearValue, map_list_sum, List.map_map,
    Function.comp_def, map_mul, eval_C, eval_X]

/-- Evaluation of a shape polynomial is the computable shape value. -/
theorem eval_shapePolynomial (h t : R) (s : RowShape) (x : Fin 1053 → R) :
    eval x (shapePolynomial h t s) = shapeValue h t s x := by
  simp only [shapePolynomial, shapeValue, map_add, eval_quadraticPolynomial,
    eval_linearPolynomial, eval_C]

/-! ## The shape of each F row -/

/-- The shape of the F residual with a given typed label:
* idempotency `(i, k)`: `h · ∑_{(a,b,c) ∈ tbl k} c · X(i,a) · X(i,b) - X(i,k)`;
* trace `i`: `X(i,0) + X(i,1) + X(i,2) - 1`;
* frame unit `(f, k)`: `∑_{a<3} X(3f+a, k) - [k < 3]`;
* pairing `i < j`: `∑_k w_k · X(i,k) · X(j,k) - (0 if i, j lie in one frame, t otherwise)`,
  with the trace weights `w_k ∈ {1, 2}`. -/
def labelShape : FLabel → RowShape
  | .inl (i, k) =>
      { quadratic := (productTable k).map fun e => (variableIndex i e.1, variableIndex i e.2.1, e.2.2)
        halfScaled := true
        linear := [(variableIndex i k, -1)]
        constant := 0
        subtractsThird := false }
  | .inr (.inl i) =>
      { quadratic := []
        halfScaled := false
        linear := [(variableIndex i 0, 1), (variableIndex i 1, 1), (variableIndex i 2, 1)]
        constant := -1
        subtractsThird := false }
  | .inr (.inr (.inl (f, k))) =>
      { quadratic := []
        halfScaled := false
        linear := [(variableIndex (framePointIndex f 0) k, 1),
          (variableIndex (framePointIndex f 1) k, 1), (variableIndex (framePointIndex f 2) k, 1)]
        constant := if k.val < 3 then -1 else 0
        subtractsThird := false }
  | .inr (.inr (.inr ij)) =>
      { quadratic := List.ofFn fun k : Fin 27 =>
          (variableIndex ij.val.1 k, variableIndex ij.val.2 k, coordinateTraceWeight k)
        halfScaled := false
        linear := []
        constant := 0
        subtractsThird := !decide (ij.val.1.val / 3 = ij.val.2.val / 3) }

/-- The shape of the numbered F row `r` (canonical `fNumber` order). -/
def rowShape (r : Fin 2184) : RowShape := labelShape (fNumber.symm r)

/-- Every typed F residual is the polynomial of its shape. -/
theorem fResidual_eq_shapePolynomial (h t : R) (q : FLabel) :
    fResidual h t q = shapePolynomial h t (labelShape q) := by
  rcases q with ⟨i, k⟩ | i | ⟨f, k⟩ | ij
  · simp only [fResidual, idempotencyResidual, Pi.sub_apply]
    rw [coordinateProduct_of_table (C h) (point i) (point i) k (productTable k)
      (numerator_eq_productTable k)]
    simp only [labelShape, shapePolynomial, quadraticScale, constantTerm, quadraticPolynomial,
      linearPolynomial, List.map_map, Function.comp_def, point, map_mul, map_intCast,
      ite_true, Bool.false_eq_true, ite_false, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Int.cast_zero, Int.cast_neg, Int.cast_one, sub_zero, map_zero, add_zero]
    ring
  · simp only [fResidual, coordinateTrace_apply, labelShape, shapePolynomial, quadraticScale,
      constantTerm, quadraticPolynomial, linearPolynomial, point, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Int.cast_one, Int.cast_neg, map_one, map_neg,
      Bool.false_eq_true, ite_false, sub_zero, one_mul]
    ring
  · simp only [fResidual, Fin.sum_univ_three, coordinateUnit, labelShape, shapePolynomial,
      quadraticScale, constantTerm, quadraticPolynomial, linearPolynomial, point,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Int.cast_one, map_one,
      Bool.false_eq_true, ite_false, sub_zero, one_mul]
    split_ifs <;> simp only [Int.cast_neg, Int.cast_one, Int.cast_zero, map_neg, map_one,
      map_zero] <;> ring
  · simp only [fResidual, coordinatePairing, labelShape, shapePolynomial, quadraticScale,
      constantTerm, quadraticPolynomial, linearPolynomial, List.map_ofFn, List.sum_ofFn,
      Function.comp_def, point, List.map_nil, List.sum_nil, Int.cast_zero, Bool.false_eq_true,
      ite_false, one_mul, map_intCast, add_zero, zero_sub]
    by_cases hsame : ij.val.1.val / 3 = ij.val.2.val / 3
    · simp only [hsame, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
        neg_zero, map_zero, add_zero, sub_zero]
    · simp only [hsame, decide_false, Bool.not_false, ite_true, ite_false, map_neg, ← sub_eq_add_neg]

/-- **Row bridge.** Every numbered F row is the polynomial of its computable shape. -/
theorem fRow_eq_shapePolynomial (h t : R) (r : Fin 2184) :
    fRow h t r = shapePolynomial h t (rowShape r) :=
  fResidual_eq_shapePolynomial h t (fNumber.symm r)

/-- Computable value of the numbered F row `r` at a point `x`. -/
def rowValue (h t : R) (r : Fin 2184) (x : Fin 1053 → R) : R := shapeValue h t (rowShape r) x

/-- **Evaluation bridge.** Evaluating an F row is the computable ring expression `rowValue`. -/
theorem eval_fRow (h t : R) (r : Fin 2184) (x : Fin 1053 → R) :
    eval x (fRow h t r) = rowValue h t r x := by
  rw [fRow_eq_shapePolynomial, eval_shapePolynomial, rowValue]

/-! ## Dependence on the row's slots -/

/-- All variables named by a shape (with repetitions). -/
def shapeVariables (s : RowShape) : List (Fin 1053) :=
  s.quadratic.flatMap (fun e => [e.1, e.2.1]) ++ s.linear.map Prod.fst

/-- A shape value only reads the variables named by the shape. -/
theorem shapeValue_congr (h t : R) (s : RowShape) {x y : Fin 1053 → R}
    (hxy : ∀ v ∈ shapeVariables s, x v = y v) : shapeValue h t s x = shapeValue h t s y := by
  have hq : ∀ e ∈ s.quadratic, x e.1 = y e.1 ∧ x e.2.1 = y e.2.1 := by
    intro e he
    refine ⟨hxy _ ?_, hxy _ ?_⟩ <;>
      simp only [shapeVariables, List.mem_append, List.mem_flatMap, List.mem_cons,
        List.not_mem_nil, or_false] <;>
      exact Or.inl ⟨e, he, by simp⟩
  have hl : ∀ e ∈ s.linear, x e.1 = y e.1 := by
    intro e he
    exact hxy _ (List.mem_append_right _ (List.mem_map_of_mem he))
  have hquad : (s.quadratic.map fun e =>
        quadraticScale h s * (e.2.2 : R) * x e.1 * x e.2.1) =
      s.quadratic.map fun e => quadraticScale h s * (e.2.2 : R) * y e.1 * y e.2.1 :=
    List.map_congr_left fun e he => by rw [(hq e he).1, (hq e he).2]
  have hlin : (s.linear.map fun e => (e.2 : R) * x e.1) =
      s.linear.map fun e => (e.2 : R) * y e.1 :=
    List.map_congr_left fun e he => by rw [hl e he]
  unfold shapeValue quadraticValue linearValue
  rw [hquad, hlin]

/-- The point slot containing a configuration variable (`v = 27 · slot + coordinate`). -/
def variableSlot (v : Fin 1053) : Fin 39 := ⟨v.val / 27, by omega⟩

@[simp] theorem variableSlot_variableIndex (i : Fin 39) (k : Fin 27) :
    variableSlot (variableIndex i k) = i := by
  apply Fin.ext
  simp only [variableSlot, variableIndex_val]
  omega

/-- The point slots read by the F residual with a given label. -/
def labelSlots : FLabel → List (Fin 39)
  | .inl (i, _) => [i]
  | .inr (.inl i) => [i]
  | .inr (.inr (.inl (f, _))) => [framePointIndex f 0, framePointIndex f 1, framePointIndex f 2]
  | .inr (.inr (.inr ij)) => [ij.val.1, ij.val.2]

/-- The point slots read by the numbered F row `r`. -/
def rowSlots (r : Fin 2184) : List (Fin 39) := labelSlots (fNumber.symm r)

/-- Every variable of a row shape lies in one of the row's slots. -/
theorem variableSlot_mem_labelSlots (q : FLabel) {v : Fin 1053}
    (hv : v ∈ shapeVariables (labelShape q)) : variableSlot v ∈ labelSlots q := by
  rcases q with ⟨i, k⟩ | i | ⟨f, k⟩ | ij
  · simp only [shapeVariables, labelShape, List.mem_append, List.mem_flatMap, List.mem_map,
      List.mem_cons, List.not_mem_nil, or_false] at hv
    simp only [labelSlots, List.mem_cons, List.not_mem_nil, or_false]
    rcases hv with ⟨e, ⟨e', _, rfl⟩, rfl | rfl⟩ | ⟨e, rfl | hfalse, rfl⟩ <;> simp_all
  · simp only [shapeVariables, labelShape, List.flatMap_nil, List.nil_append, List.map_cons,
      List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
    simp only [labelSlots, List.mem_cons, List.not_mem_nil, or_false]
    rcases hv with rfl | rfl | rfl <;> simp
  · simp only [shapeVariables, labelShape, List.flatMap_nil, List.nil_append, List.map_cons,
      List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
    simp only [labelSlots, List.mem_cons, List.not_mem_nil, or_false]
    rcases hv with rfl | rfl | rfl <;> simp
  · simp only [shapeVariables, labelShape, List.mem_append, List.mem_flatMap, List.mem_ofFn,
      List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
    simp only [labelSlots, List.mem_cons, List.not_mem_nil, or_false]
    rcases hv with ⟨e, ⟨k, rfl⟩, rfl | rfl⟩ <;> simp

/-- Every variable named by the shape of row `r` lies in one of the slots `rowSlots r`. -/
theorem variableSlot_mem_rowSlots (r : Fin 2184) {v : Fin 1053}
    (hv : v ∈ shapeVariables (rowShape r)) : variableSlot v ∈ rowSlots r :=
  variableSlot_mem_labelSlots _ hv

/-- **Dependence lemma.** The value of row `r` only depends on the coordinates of the
points in `rowSlots r`. -/
theorem rowValue_congr (h t : R) (r : Fin 2184) {x y : Fin 1053 → R}
    (hxy : ∀ v, variableSlot v ∈ rowSlots r → x v = y v) :
    rowValue h t r x = rowValue h t r y :=
  shapeValue_congr h t _ fun v hv => hxy v (variableSlot_mem_rowSlots r hv)

end QuarticCertificate.RowBridge

module

public import RowJacobian
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Gauge lemma for the original F rows (first-party)

Generic over a commutative ring `R` with `2 h = 1`. Let `X` be a zero of all 2184 original rows,
`ℓ` an equilibrium covector at `X` (`ℓ · L_X = 0` on all 1053 columns), `v` a tangent vector
(`L_X v = 0` on all rows) and `D` a 27 × 27 operator applied state-wise which is a derivation of the
(doubled, symmetrised) native coordinate product, skew for the trace weights, kills the unit and
is trace-free. Then the quadratic parts agree:

  `∑ r, ℓ r · Q_r(D X − v) = ∑ r, ℓ r · Q_r(v)`.

Row by row (all four row types, through the literal `labelShape`):
`2 Q_r(DX) + L_r(D²X) = 0` (`E1`, uses `F(X) = 0` on the rows of the same state / frame) and
`B_r(DX, v) + L_r(Dv) = 0` (`E2`, uses `L_X v = 0` on the rows of the same state / frame), with
`B_r` the doubled polarisation of `Q_r`. Nothing about the native data is assumed here.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace Option2.NativeStress.HTPhaseComplete

open scoped BigOperators
open QuarticCertificate.RowBridge NativePolynomial.ConfigurationResiduals ConfigurationResidualIndices
open NativePolynomial.IntegralStructureConstants

variable {R : Type*} [CommRing R]

/-! ## Generic shape algebra -/

/-- Doubled polarisation of a quadratic list: `∑ a c (x_i y_j + y_i x_j)`. -/
def bil2 (a : R) (l : List (Fin 1053 × Fin 1053 × ℤ)) (x y : Fin 1053 → R) : R :=
  (l.map fun e => a * (e.2.2 : R) * (x e.1 * y e.2.1 + y e.1 * x e.2.1)).sum

theorem quadraticValue_sub' (a : R) (l : List (Fin 1053 × Fin 1053 × ℤ)) (x y : Fin 1053 → R) :
    quadraticValue a l (x - y) = quadraticValue a l x - bil2 a l x y + quadraticValue a l y := by
  induction l with
  | nil => simp [quadraticValue, bil2]
  | cons e l ih =>
    simp only [quadraticValue, bil2, List.map_cons, List.sum_cons, Pi.sub_apply] at ih ⊢
    rw [ih]; ring

/-- The linear part of a shape in direction `v`. -/
def linPart (s : RowShape) (v : Fin 1053 → R) : R := (s.linear.map fun e => (e.2 : R) * v e.1).sum

theorem jac_sum (h : R) (s : RowShape) (P v : Fin 1053 → R) :
    ∑ c, shapeJacobianEntry h s P c * v c = bil2 (quadraticScale h s) s.quadratic P v + linPart s v := by
  unfold shapeJacobianEntry bil2 linPart
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  · generalize s.quadratic = l
    induction l with
    | nil => simp
    | cons e l ih =>
      simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, ih]
      congr 1
      simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, mul_zero, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring
  · generalize s.linear = l
    induction l with
    | nil => simp
    | cons e l ih =>
      simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, ih, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-! ## State vectors and state-wise operators -/

/-- The coordinate of a configuration variable (`v = 27 · slot + coordinate`). -/
def coordOf (v : Fin 1053) : Fin 27 := ⟨v.val % 27, by omega⟩

theorem variableIndex_slot_coord (v : Fin 1053) : variableIndex (variableSlot v) (coordOf v) = v := by
  apply Fin.ext; simp only [variableIndex_val, variableSlot, coordOf]; omega

@[simp] theorem coordOf_variableIndex (i : Fin 39) (k : Fin 27) : coordOf (variableIndex i k) = k := by
  apply Fin.ext; simp only [coordOf, variableIndex_val]; omega

/-- State `i` of a configuration. -/
def sv (x : Fin 1053 → R) (i : Fin 39) : Fin 27 → R := fun k => x (variableIndex i k)

/-- A 27 × 27 operator on one state. -/
def mv (D : Fin 27 → Fin 27 → R) (y : Fin 27 → R) : Fin 27 → R := fun m => ∑ n, D m n * y n

/-- A 27 × 27 operator applied to every state. -/
def opApply (D : Fin 27 → Fin 27 → R) (x : Fin 1053 → R) : Fin 1053 → R :=
  fun v => ∑ n, D (coordOf v) n * x (variableIndex (variableSlot v) n)

@[simp] theorem opApply_vi (D : Fin 27 → Fin 27 → R) (x : Fin 1053 → R) (i : Fin 39) (m : Fin 27) :
    opApply D x (variableIndex i m) = mv D (sv x i) m := by
  simp only [opApply, coordOf_variableIndex, variableSlot_variableIndex, mv, sv]

theorem sv_opApply (D : Fin 27 → Fin 27 → R) (x : Fin 1053 → R) (i : Fin 39) :
    sv (opApply D x) i = mv D (sv x i) := funext fun m => opApply_vi D x i m

/-! ## The native product table -/

/-- Doubled symmetrised product, output coordinate `k`. -/
def tb (k : Fin 27) (y z : Fin 27 → R) : R :=
  ((productTable k).map fun e => (e.2.2 : R) * (y e.1 * z e.2.1 + z e.1 * y e.2.1)).sum

/-- The product quadratic, output coordinate `k`. -/
def tq (k : Fin 27) (y : Fin 27 → R) : R :=
  ((productTable k).map fun e => (e.2.2 : R) * y e.1 * y e.2.1).sum

theorem tb_self (k : Fin 27) (y : Fin 27 → R) : tb k y y = 2 * tq k y := by
  unfold tb tq
  rw [← List.sum_map_mul_left]
  congr 1; apply List.map_congr_left; intro e _; ring

theorem tb_comm (k : Fin 27) (y z : Fin 27 → R) : tb k y z = tb k z y := by
  unfold tb; congr 1; apply List.map_congr_left; intro e _; ring

/-- Derivation of the doubled symmetrised product. -/
def IsDer (D : Fin 27 → Fin 27 → R) : Prop :=
  ∀ (k : Fin 27) (y z : Fin 27 → R), ∑ p, D k p * tb p y z = tb k (mv D y) z + tb k y (mv D z)

/-- Skew for the trace weights `(1,1,1,2,…,2)`. -/
def IsSkew (D : Fin 27 → Fin 27 → R) : Prop :=
  ∀ m n : Fin 27, (coordinateTraceWeight m : R) * D m n + (coordinateTraceWeight n : R) * D n m = 0

/-- Kills the unit `e = (1,1,1,0,…,0)`. -/
def KillsUnit (D : Fin 27 → Fin 27 → R) : Prop := ∀ m : Fin 27, D m 0 + D m 1 + D m 2 = 0

/-- Trace-free: the trace `x₀ + x₁ + x₂` of `D y` vanishes. -/
def TraceFree (D : Fin 27 → Fin 27 → R) : Prop := ∀ n : Fin 27, D 0 n + D 1 n + D 2 n = 0

/-- The weighted pairing of two states. -/
def wpair (y z : Fin 27 → R) : R := ∑ k, (coordinateTraceWeight k : R) * y k * z k

theorem wpair_skew {D : Fin 27 → Fin 27 → R} (hS : IsSkew D) (y z : Fin 27 → R) :
    wpair (mv D y) z = -wpair y (mv D z) := by
  unfold wpair mv
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro n _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro k _
  have := hS k n
  linear_combination (y n * z k) * this

theorem mv_unit {D : Fin 27 → Fin 27 → R} (hU : KillsUnit D) (y : Fin 27 → R)
    (hy : ∀ k : Fin 27, y k = if k.val < 3 then 1 else 0) : mv D y = 0 := by
  funext m
  have hy' : y = fun k : Fin 27 => if k.val < 3 then (1 : R) else 0 := funext hy
  subst hy'
  simp [mv, Fin.sum_univ_succ]
  linear_combination hU m

theorem mv_add3 (D : Fin 27 → Fin 27 → R) (y0 y1 y2 : Fin 27 → R) (m : Fin 27) :
    mv D y0 m + mv D y1 m + mv D y2 m = mv D (fun n => y0 n + y1 n + y2 n) m := by
  simp only [mv, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro n _; ring

theorem two_cancel {h : R} (h2 : (2 : R) * h = 1) {g : R} (hg : 2 * g = 0) : g = 0 := by
  linear_combination h * hg - g * h2

theorem trace_mv {D : Fin 27 → Fin 27 → R} (hT : TraceFree D) (y : Fin 27 → R) :
    mv D y 0 + mv D y 1 + mv D y 2 = 0 := by
  unfold mv
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero; intro n _
  linear_combination (y n) * hT n

/-! ## The four row types -/

section Rows
variable (h t : R)

theorem idem_quad (i : Fin 39) (k : Fin 27) (x : Fin 1053 → R) :
    quadraticValue (quadraticScale h (labelShape (.inl (i, k)))) (labelShape (.inl (i, k))).quadratic x =
      h * tq k (sv x i) := by
  simp only [labelShape, quadraticScale, if_true, quadraticValue, tq, sv, List.map_map,
    Function.comp_def]
  rw [← List.sum_map_mul_left]
  congr 1; apply List.map_congr_left; intro e _; ring

theorem idem_bil (i : Fin 39) (k : Fin 27) (x y : Fin 1053 → R) :
    bil2 (quadraticScale h (labelShape (.inl (i, k)))) (labelShape (.inl (i, k))).quadratic x y =
      h * tb k (sv x i) (sv y i) := by
  simp only [labelShape, quadraticScale, if_true, bil2, tb, sv, List.map_map, Function.comp_def]
  rw [← List.sum_map_mul_left]
  congr 1; apply List.map_congr_left; intro e _; ring

theorem idem_lin (i : Fin 39) (k : Fin 27) (v : Fin 1053 → R) :
    linPart (labelShape (.inl (i, k))) v = -sv v i k := by
  simp [labelShape, linPart, sv]

theorem idem_value (i : Fin 39) (k : Fin 27) (x : Fin 1053 → R) :
    shapeValue h t (labelShape (.inl (i, k))) x = h * tq k (sv x i) - sv x i k := by
  rw [shapeValue, idem_quad]
  simp [labelShape, linearValue, constantTerm, sv]
  ring

theorem trace_quad (i : Fin 39) (x : Fin 1053 → R) :
    quadraticValue (quadraticScale h (labelShape (.inr (.inl i)))) (labelShape (.inr (.inl i))).quadratic x = 0 := by
  simp [labelShape, quadraticValue]

theorem trace_bil (i : Fin 39) (x y : Fin 1053 → R) :
    bil2 (quadraticScale h (labelShape (.inr (.inl i)))) (labelShape (.inr (.inl i))).quadratic x y = 0 := by
  simp [labelShape, bil2]

theorem trace_lin (i : Fin 39) (v : Fin 1053 → R) :
    linPart (labelShape (.inr (.inl i))) v = sv v i 0 + sv v i 1 + sv v i 2 := by
  simp [labelShape, linPart, sv]; ring

theorem frame_quad (f : Fin 13) (k : Fin 27) (x : Fin 1053 → R) :
    quadraticValue (quadraticScale h (labelShape (.inr (.inr (.inl (f, k))))))
      (labelShape (.inr (.inr (.inl (f, k))))).quadratic x = 0 := by
  simp [labelShape, quadraticValue]

theorem frame_bil (f : Fin 13) (k : Fin 27) (x y : Fin 1053 → R) :
    bil2 (quadraticScale h (labelShape (.inr (.inr (.inl (f, k))))))
      (labelShape (.inr (.inr (.inl (f, k))))).quadratic x y = 0 := by
  simp [labelShape, bil2]

theorem frame_lin (f : Fin 13) (k : Fin 27) (v : Fin 1053 → R) :
    linPart (labelShape (.inr (.inr (.inl (f, k))))) v =
      sv v (framePointIndex f 0) k + sv v (framePointIndex f 1) k + sv v (framePointIndex f 2) k := by
  simp [labelShape, linPart, sv]; ring

theorem frame_value (f : Fin 13) (k : Fin 27) (x : Fin 1053 → R) :
    shapeValue h t (labelShape (.inr (.inr (.inl (f, k))))) x =
      sv x (framePointIndex f 0) k + sv x (framePointIndex f 1) k + sv x (framePointIndex f 2) k -
        (if k.val < 3 then 1 else 0) := by
  rw [shapeValue, frame_quad]
  simp only [labelShape, linearValue, constantTerm, sv, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_one, one_mul, add_zero, zero_add, Bool.false_eq_true, ite_false, sub_zero]
  split_ifs <;> simp <;> ring

theorem pair_quad (ij : Pair 39) (x : Fin 1053 → R) :
    quadraticValue (quadraticScale h (labelShape (.inr (.inr (.inr ij)))))
      (labelShape (.inr (.inr (.inr ij)))).quadratic x = wpair (sv x ij.val.1) (sv x ij.val.2) := by
  simp only [labelShape, quadraticScale, Bool.false_eq_true, ite_false, quadraticValue, List.map_ofFn,
    List.sum_ofFn, Function.comp_def, wpair, sv, one_mul]

theorem pair_bil (ij : Pair 39) (x y : Fin 1053 → R) :
    bil2 (quadraticScale h (labelShape (.inr (.inr (.inr ij)))))
      (labelShape (.inr (.inr (.inr ij)))).quadratic x y =
      wpair (sv x ij.val.1) (sv y ij.val.2) + wpair (sv y ij.val.1) (sv x ij.val.2) := by
  simp only [labelShape, quadraticScale, Bool.false_eq_true, ite_false, bil2, List.map_ofFn,
    List.sum_ofFn, Function.comp_def, wpair, sv, one_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _; ring

theorem pair_lin (ij : Pair 39) (v : Fin 1053 → R) : linPart (labelShape (.inr (.inr (.inr ij)))) v = 0 := by
  simp [labelShape, linPart]

end Rows

/-! ## Row identities E1, E2 -/

section E
variable {h t : R} {D : Fin 27 → Fin 27 → R} {X v : Fin 1053 → R}

/-- Linearised row of a shape at `X` in direction `y`. -/
def Lin (h : R) (s : RowShape) (X y : Fin 1053 → R) : R := bil2 (quadraticScale h s) s.quadratic X y + linPart s y

theorem derSq {D : Fin 27 → Fin 27 → R} (hD : IsDer D) (k : Fin 27) (y : Fin 27 → R) :
    ∑ p, D k p * ∑ q, D p q * tb q y y = 2 * (tb k (mv D (mv D y)) y + tb k (mv D y) (mv D y)) := by
  have h1 : ∀ p, ∑ q, D p q * tb q y y = 2 * tb p (mv D y) y := by
    intro p; rw [hD p y y, tb_comm p y (mv D y)]; ring
  simp only [h1]
  have h2 : ∑ p, D k p * (2 * tb p (mv D y) y) = 2 * ∑ p, D k p * tb p (mv D y) y := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  rw [h2, hD k (mv D y) y]

theorem E1 (h2 : (2 : R) * h = 1) (hD : IsDer D) (hS : IsSkew D) (hU : KillsUnit D) (hT : TraceFree D)
    (hF : ∀ q : FLabel, shapeValue h t (labelShape q) X = 0) (q : FLabel) :
    2 * quadraticValue (quadraticScale h (labelShape q)) (labelShape q).quadratic (opApply D X) +
      Lin h (labelShape q) X (opApply D (opApply D X)) = 0 := by
  rcases q with ⟨i, k⟩ | i | ⟨f, k⟩ | ij
  · rw [Lin, idem_quad, idem_bil, idem_lin, sv_opApply, sv_opApply, sv_opApply]
    set x := sv X i
    have hx : ∀ p, h * tq p x = x p := by
      intro p; have := hF (.inl (i, p)); rw [idem_value] at this; exact sub_eq_zero.mp this
    -- h · (D² (tb x x))_k = 2 (D² x)_k
    have inner : ∀ p, h * ∑ q, D p q * tb q x x = 2 * mv D x p := by
      intro p; simp only [mv, Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _
      rw [tb_self, ← hx q]; ring
    have hl : h * (∑ p, D k p * ∑ q, D p q * tb q x x) = 2 * mv D (mv D x) k := by
      have e1 : h * (∑ p, D k p * ∑ q, D p q * tb q x x) =
          ∑ p, D k p * (h * ∑ q, D p q * tb q x x) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
      rw [e1]; simp only [inner]
      show _ = 2 * ∑ p, D k p * mv D x p
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    have hd := derSq hD k x
    rw [tb_self] at hd
    apply two_cancel h2
    rw [tb_comm k x]
    linear_combination hl - h * hd
  · simp only [Lin, trace_quad, trace_bil, trace_lin, sv_opApply, trace_mv hT]; ring
  · simp only [Lin, frame_quad, frame_bil, frame_lin, sv_opApply]
    have he : ∀ m : Fin 27, sv X (framePointIndex f 0) m + sv X (framePointIndex f 1) m +
        sv X (framePointIndex f 2) m = if m.val < 3 then 1 else 0 := by
      intro m; have := hF (.inr (.inr (.inl (f, m)))); rw [frame_value] at this
      exact sub_eq_zero.mp this
    rw [mv_add3, show (fun n => mv D (sv X (framePointIndex f 0)) n + mv D (sv X (framePointIndex f 1)) n +
        mv D (sv X (framePointIndex f 2)) n) = mv D (fun n => sv X (framePointIndex f 0) n +
        sv X (framePointIndex f 1) n + sv X (framePointIndex f 2) n) from funext fun n => mv_add3 D _ _ _ n,
      mv_unit hU _ he]
    simp [mv]
  · simp only [Lin, pair_quad, pair_bil, pair_lin, sv_opApply]
    have a1 := wpair_skew hS (sv X ij.val.1) (mv D (sv X ij.val.2))
    have a2 := wpair_skew hS (mv D (sv X ij.val.1)) (sv X ij.val.2)
    linear_combination a1 + a2

theorem E2 (h2 : (2 : R) * h = 1) (hD : IsDer D) (hS : IsSkew D) (hT : TraceFree D)
    (hv : ∀ q : FLabel, Lin h (labelShape q) X v = 0) (q : FLabel) :
    bil2 (quadraticScale h (labelShape q)) (labelShape q).quadratic (opApply D X) v +
      Lin h (labelShape q) X (opApply D v) = 0 := by
  rcases q with ⟨i, k⟩ | i | ⟨f, k⟩ | ij
  · simp only [Lin, idem_bil, idem_lin, sv_opApply]
    have hvi : ∀ p, h * tb p (sv X i) (sv v i) = sv v i p := by
      intro p; have := hv (.inl (i, p)); rw [Lin, idem_bil, idem_lin] at this; linear_combination this
    have hd := hD k (sv X i) (sv v i)
    have hl : h * ∑ p, D k p * tb p (sv X i) (sv v i) = mv D (sv v i) k := by
      simp only [mv, Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; rw [← hvi p]; ring
    linear_combination hl - h * hd
  · simp only [Lin, trace_bil, trace_lin, sv_opApply, trace_mv hT]; ring
  · simp only [Lin, frame_bil, frame_lin, sv_opApply]
    have hz : ∀ m : Fin 27, sv v (framePointIndex f 0) m + sv v (framePointIndex f 1) m +
        sv v (framePointIndex f 2) m = 0 := by
      intro m; have := hv (.inr (.inr (.inl (f, m)))); rw [Lin, frame_bil, frame_lin] at this
      linear_combination this
    simp only [mv, ← Finset.sum_add_distrib, zero_add]
    exact Finset.sum_eq_zero fun n _ => by linear_combination (D k n) * hz n
  · simp only [Lin, pair_bil, pair_lin, sv_opApply]
    have a1 := wpair_skew hS (sv X ij.val.1) (sv v ij.val.2)
    have a2 := wpair_skew hS (sv v ij.val.1) (sv X ij.val.2)
    linear_combination a1 + a2

end E

/-! ## The gauge lemma over the numbered rows -/

theorem lin_eq_jac (h t : R) (r : Fin 2184) (X y : Fin 1053 → R) :
    Lin h (rowShape r) X y = ∑ c, jacobianEntry h t r X c * y c := by
  show _ = ∑ c, shapeJacobianEntry h (rowShape r) X c * y c
  rw [jac_sum]; rfl

/-- **Gauge lemma.** -/
theorem gauge (h t : R) (h2 : (2 : R) * h = 1) (D : Fin 27 → Fin 27 → R)
    (hD : IsDer D) (hS : IsSkew D) (hU : KillsUnit D) (hT : TraceFree D)
    (X v : Fin 1053 → R) (ℓ : Fin 2184 → R)
    (hF : ∀ r, rowValue h t r X = 0)
    (hℓ : ∀ c, ∑ r, ℓ r * jacobianEntry h t r X c = 0)
    (hv : ∀ r, ∑ c, jacobianEntry h t r X c * v c = 0) :
    ∑ r, ℓ r * quadraticPartValue h r (opApply D X - v) = ∑ r, ℓ r * quadraticPartValue h r v := by
  have hF' : ∀ q : FLabel, shapeValue h t (labelShape q) X = 0 := by
    intro q; have := hF (fNumber q); simpa [rowValue, rowShape] using this
  have hv' : ∀ q : FLabel, Lin h (labelShape q) X v = 0 := by
    intro q; have := hv (fNumber q); rw [← lin_eq_jac] at this; simpa [rowShape] using this
  -- annihilation of linearised rows
  have hann : ∀ y : Fin 1053 → R, ∑ r, ℓ r * Lin h (rowShape r) X y = 0 := by
    intro y
    have hc : ∀ c, ∑ r, ℓ r * (jacobianEntry h t r X c * y c) = 0 := by
      intro c
      rw [show ∑ r, ℓ r * (jacobianEntry h t r X c * y c) = (∑ r, ℓ r * jacobianEntry h t r X c) * y c by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro r _; ring, hℓ c, zero_mul]
    rw [show ∑ r, ℓ r * Lin h (rowShape r) X y = ∑ c, ∑ r, ℓ r * (jacobianEntry h t r X c * y c) by
      simp only [lin_eq_jac h t, Finset.mul_sum]; exact Finset.sum_comm]
    exact Finset.sum_eq_zero fun c _ => hc c
  have row : ∀ r : Fin 2184, 2 * (quadraticPartValue h r (opApply D X - v) - quadraticPartValue h r v) =
      Lin h (rowShape r) X (fun c => 2 * opApply D v c - opApply D (opApply D X) c) := by
    intro r
    have e1 := E1 (t := t) h2 hD hS hU hT hF' (fNumber.symm r)
    have e2 := E2 h2 hD hS hT hv' (fNumber.symm r)
    have hlin : ∀ (s : RowShape) (a b : Fin 1053 → R),
        Lin h s X (fun c => 2 * a c - b c) = 2 * Lin h s X a - Lin h s X b := by
      intro s a b
      unfold Lin bil2 linPart
      have e : ∀ (l : List (Fin 1053 × Fin 1053 × ℤ)) (c : R), (l.map fun e => c * (e.2.2 : R) *
          (X e.1 * (2 * a e.2.1 - b e.2.1) + (2 * a e.1 - b e.1) * X e.2.1)).sum =
          2 * (l.map fun e => c * (e.2.2 : R) * (X e.1 * a e.2.1 + a e.1 * X e.2.1)).sum -
          (l.map fun e => c * (e.2.2 : R) * (X e.1 * b e.2.1 + b e.1 * X e.2.1)).sum := by
        intro l c; induction l with
        | nil => simp
        | cons e l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
      have f : ∀ (l : List (Fin 1053 × ℤ)), (l.map fun e => (e.2 : R) * (2 * a e.1 - b e.1)).sum =
          2 * (l.map fun e => (e.2 : R) * a e.1).sum - (l.map fun e => (e.2 : R) * b e.1).sum := by
        intro l; induction l with
        | nil => simp
        | cons e l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
      simp only [e, f]; ring
    rw [hlin]
    simp only [quadraticPartValue, quadTable, rowShape, quadraticValue_sub'] at e1 e2 ⊢
    simp only [Lin] at e1 e2 ⊢
    linear_combination e1 - 2 * e2
  have tot : 2 * (∑ r, ℓ r * quadraticPartValue h r (opApply D X - v) - ∑ r, ℓ r * quadraticPartValue h r v) = 0 := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    have : ∀ r, 2 * (ℓ r * quadraticPartValue h r (opApply D X - v) - ℓ r * quadraticPartValue h r v) =
        ℓ r * Lin h (rowShape r) X (fun c => 2 * opApply D v c - opApply D (opApply D X) c) := by
      intro r; rw [← row r]; ring
    simp only [this]; exact hann _
  have : ∑ r, ℓ r * quadraticPartValue h r (opApply D X - v) - ∑ r, ℓ r * quadraticPartValue h r v =
      h * (2 * (∑ r, ℓ r * quadraticPartValue h r (opApply D X - v) - ∑ r, ℓ r * quadraticPartValue h r v)) := by
    linear_combination (-(∑ r, ℓ r * quadraticPartValue h r (opApply D X - v) -
      ∑ r, ℓ r * quadraticPartValue h r v)) * h2
  rw [tot, mul_zero] at this
  exact sub_eq_zero.mp this

end Option2.NativeStress.HTPhaseComplete

#print axioms Option2.NativeStress.HTPhaseComplete.gauge

module

public import HTPCValAData
public import HTKronExact

@[expose] public section

/-!
# Derivation, skewness, unit and trace checks for integer 27 × 27 matrices (first-party)

`IsDer D` (of `HTPhaseCompleteGauge`) is a bilinear identity. For an integer matrix it is decided by ONE
exact evaluation (Kronecker): with `X = 2^32`, `y_m = X^m`, `z_n = X^(27 n)`, `w_k = X^(729 k)`,
`∑_k w_k · defect D y z k = ∑_{k,m,n} defect D e_m e_n k · X^(729k + 27n + m)`, and every basis
defect is bounded by `derBound D < X` (`defect_basis_abs_le`), so the vanishing of that single
integer forces every coefficient to vanish (`HTKron.digits_eq_zero`), hence `IsDer` over every
commutative ring (`isDer_of_kron`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace Option2.NativeStress.HTPhaseComplete

open scoped BigOperators
open QuarticCertificate.RowBridge NativePolynomial.IntegralStructureConstants

/-! ## Sparse integer matrices -/

/-- Entry `(k, c)` of a sparse integer matrix (repeated positions are added). -/
def iAt (l : List IEnt) (k c : Fin 27) : ℤ := (l.map fun e => if e.1 = k ∧ e.2.1 = c then e.2.2 else 0).sum

/-- The matrix over a commutative ring. -/
def iMat {R : Type*} [CommRing R] (l : List IEnt) : Fin 27 → Fin 27 → R := fun k c => (iAt l k c : R)

section Bilinear
variable {R : Type*} [CommRing R]

/-- Basis vector. -/
def eb (m : Fin 27) : Fin 27 → R := fun a => if a = m then 1 else 0

theorem tb_add_left (k : Fin 27) (u u' v : Fin 27 → R) : tb k (u + u') v = tb k u v + tb k u' v := by
  unfold tb; rw [← List.sum_map_add]; congr 1; apply List.map_congr_left; intro e _
  simp only [Pi.add_apply]; ring

theorem tb_smul_left (k : Fin 27) (a : R) (u v : Fin 27 → R) : tb k (a • u) v = a * tb k u v := by
  unfold tb; rw [← List.sum_map_mul_left]; congr 1; apply List.map_congr_left; intro e _
  simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem tb_zero_left (k : Fin 27) (v : Fin 27 → R) : tb k 0 v = 0 := by
  have := tb_smul_left k (0 : R) 0 v; simpa using this

theorem tb_sum_left (k : Fin 27) (s : Finset (Fin 27)) (u : Fin 27 → Fin 27 → R) (v : Fin 27 → R) :
    tb k (∑ m ∈ s, u m) v = ∑ m ∈ s, tb k (u m) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tb_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tb_add_left, ih]

theorem vec_eq_sum (y : Fin 27 → R) : y = ∑ m, y m • (eb m : Fin 27 → R) := by
  funext a; simp [eb, Finset.sum_apply]

theorem mv_eq_sum (D : Fin 27 → Fin 27 → R) (y : Fin 27 → R) :
    mv D y = ∑ m, y m • mv D (eb m) := by
  funext k; simp only [mv, eb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]; apply Finset.sum_congr rfl; intro m _; ring

/-- The derivation defect. -/
def defect (D : Fin 27 → Fin 27 → R) (y z : Fin 27 → R) (k : Fin 27) : R :=
  ∑ p, D k p * tb p y z - tb k (mv D y) z - tb k y (mv D z)

theorem defect_left (D : Fin 27 → Fin 27 → R) (y z : Fin 27 → R) (k : Fin 27) :
    defect D y z k = ∑ m, y m * defect D (eb m) z k := by
  have h1 : ∀ p, tb p y z = ∑ m, y m * tb p (eb m) z := by
    intro p; conv_lhs => rw [vec_eq_sum y]
    rw [tb_sum_left]; simp only [tb_smul_left]
  have h2 : tb k (mv D y) z = ∑ m, y m * tb k (mv D (eb m)) z := by
    rw [mv_eq_sum D y, tb_sum_left]; simp only [tb_smul_left]
  have h3 : tb k y (mv D z) = ∑ m, y m * tb k (eb m) (mv D z) := by
    conv_lhs => rw [vec_eq_sum y]
    rw [tb_sum_left]; simp only [tb_smul_left]
  unfold defect
  rw [h2, h3]; simp only [h1, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro m _
  have e : ∑ x, D k x * (y m * tb x (eb m) z) = y m * ∑ p, D k p * tb p (eb m) z := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  rw [e]; ring

theorem defect_comm (D : Fin 27 → Fin 27 → R) (y z : Fin 27 → R) (k : Fin 27) :
    defect D y z k = defect D z y k := by
  unfold defect; simp only [tb_comm _ y z, tb_comm k (mv D y) z, tb_comm k y (mv D z)]; ring

theorem defect_expand (D : Fin 27 → Fin 27 → R) (y z : Fin 27 → R) (k : Fin 27) :
    defect D y z k = ∑ m, ∑ n, y m * z n * defect D (eb m) (eb n) k := by
  rw [defect_left]; apply Finset.sum_congr rfl; intro m _
  rw [defect_comm, defect_left, Finset.mul_sum]; apply Finset.sum_congr rfl; intro n _
  rw [defect_comm]; ring

theorem isDer_of_basis (D : Fin 27 → Fin 27 → R) (h : ∀ k m n, defect D (eb m) (eb n) k = 0) : IsDer D := by
  intro k y z
  have := defect_expand D y z k
  simp only [h, mul_zero, Finset.sum_const_zero] at this
  unfold defect at this; exact by linear_combination this

end Bilinear

/-! ## Transfer of integer basis defects to any ring -/

section Cast
variable {R : Type*} [CommRing R]

theorem cast_tb (k : Fin 27) (y z : Fin 27 → ℤ) : ((tb k y z : ℤ) : R) = tb k (fun a => (y a : R)) (fun a => (z a : R)) := by
  unfold tb; simp [List.map_map, Function.comp_def]

theorem cast_mv (D : Fin 27 → Fin 27 → ℤ) (y : Fin 27 → ℤ) :
    (fun a => ((mv D y a : ℤ) : R)) = mv (fun k c => (D k c : R)) (fun a => (y a : R)) := by
  funext a; simp [mv]

theorem cast_eb (m : Fin 27) : (fun a => ((eb m a : ℤ) : R)) = eb m := by
  funext a; simp only [eb]; split_ifs <;> simp

theorem cast_defect (D : Fin 27 → Fin 27 → ℤ) (m n k : Fin 27) :
    ((defect D (eb m) (eb n) k : ℤ) : R) = defect (fun k c => (D k c : R)) (eb m) (eb n) k := by
  unfold defect
  push_cast
  rw [cast_tb, cast_tb, cast_mv, cast_mv, cast_eb, cast_eb]
  congr 1; congr 1
  apply Finset.sum_congr rfl; intro p _; rw [cast_tb, cast_eb, cast_eb]

end Cast

/-! ## Bounds -/

/-- Absolute coefficient mass of a product table row. -/
def tabMass (k : Fin 27) : ℤ := ((productTable k).map fun e => 2 * |e.2.2|).sum

theorem tb_abs_le (k : Fin 27) (u v : Fin 27 → ℤ) (U V : ℤ) (hu : ∀ a, |u a| ≤ U) (hv : ∀ a, |v a| ≤ V)
    (hU : 0 ≤ U) (hV : 0 ≤ V) : |tb k u v| ≤ tabMass k * (U * V) := by
  unfold tb tabMass
  generalize productTable k = l
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : |(e.2.2 : ℤ) * (u e.1 * v e.2.1 + v e.1 * u e.2.1)| ≤ 2 * |e.2.2| * (U * V) := by
      rw [abs_mul]
      have a1 : |u e.1 * v e.2.1| ≤ U * V := by
        rw [abs_mul]; exact mul_le_mul (hu _) (hv _) (abs_nonneg _) hU
      have a2 : |v e.1 * u e.2.1| ≤ U * V := by
        rw [abs_mul, mul_comm U V]; exact mul_le_mul (hv _) (hu _) (abs_nonneg _) hV
      have := abs_add_le (u e.1 * v e.2.1) (v e.1 * u e.2.1)
      nlinarith [abs_nonneg (e.2.2 : ℤ)]
    calc |(e.2.2 : ℤ) * (u e.1 * v e.2.1 + v e.1 * u e.2.1) +
          (l.map fun e => (e.2.2 : ℤ) * (u e.1 * v e.2.1 + v e.1 * u e.2.1)).sum|
        ≤ _ := abs_add_le _ _
      _ ≤ 2 * |e.2.2| * (U * V) + (l.map fun e => 2 * |e.2.2|).sum * (U * V) := add_le_add h1 ih
      _ = _ := by ring

theorem eb_abs_le (m a : Fin 27) : |(eb m a : ℤ)| ≤ 1 := by unfold eb; split_ifs <;> simp

/-- Maximal absolute entry bound (a sum, so a crude but valid bound). -/
def entryMass (l : List IEnt) : ℤ := (l.map fun e => |e.2.2|).sum

theorem iAt_abs_le (l : List IEnt) (k c : Fin 27) : |iAt l k c| ≤ entryMass l := by
  unfold iAt entryMass
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    split_ifs <;> simp

theorem entryMass_nonneg (l : List IEnt) : 0 ≤ entryMass l := by
  unfold entryMass; induction l with
  | nil => simp
  | cons e l ih => simp only [List.map_cons, List.sum_cons]; exact add_nonneg (abs_nonneg _) ih

theorem tabMass_nonneg (k : Fin 27) : 0 ≤ tabMass k := by
  unfold tabMass; generalize productTable k = l
  induction l with
  | nil => simp
  | cons e l ih => simp only [List.map_cons, List.sum_cons]; exact add_nonneg (by positivity) ih

/-- Total table mass. -/
def tabTotal : ℤ := ((List.finRange 27).map tabMass).sum

theorem tabMass_le_total (k : Fin 27) : tabMass k ≤ tabTotal := by
  unfold tabTotal
  have hmem : k ∈ List.finRange 27 := List.mem_finRange k
  have hnn : ∀ x ∈ (List.finRange 27).map tabMass, 0 ≤ x := by
    intro x hx; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx; exact tabMass_nonneg j
  exact List.single_le_sum hnn _ (List.mem_map_of_mem hmem)

/-- A bound on every basis defect: `27 E T + 2 · 27 E T` with `E` the entry mass and `T` the table total. -/
def derBound (l : List IEnt) : ℤ := 81 * entryMass l * tabTotal

theorem mv_eb_abs_le (l : List IEnt) (m a : Fin 27) : |mv (iMat (R := ℤ) l) (eb m) a| ≤ entryMass l := by
  simp only [mv, iMat, eb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Int.cast_id]
  exact iAt_abs_le l a m

theorem mv_abs_le (l : List IEnt) (z : Fin 27 → ℤ) (hz : ∀ a, |z a| ≤ 1) (a : Fin 27) :
    |mv (iMat (R := ℤ) l) z a| ≤ 27 * entryMass l := by
  unfold mv
  calc |∑ n, iMat l a n * z n| ≤ ∑ n : Fin 27, |iMat (R := ℤ) l a n * z n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n : Fin 27, entryMass l := by
        apply Finset.sum_le_sum; intro n _
        rw [abs_mul]; simp only [iMat, Int.cast_id]
        nlinarith [iAt_abs_le l a n, hz n, abs_nonneg (iAt l a n), abs_nonneg (z n)]
    _ = 27 * entryMass l := by simp

theorem defect_basis_abs_le (l : List IEnt) (m n k : Fin 27) :
    |defect (iMat (R := ℤ) l) (eb m) (eb n) k| ≤ derBound l := by
  have hE := entryMass_nonneg l
  have hT : 0 ≤ tabTotal := le_trans (tabMass_nonneg 0) (tabMass_le_total 0)
  have b1 : |∑ p, iMat (R := ℤ) l k p * tb p (eb m) (eb n)| ≤ 27 * (entryMass l * tabTotal) := by
    calc |∑ p, iMat (R := ℤ) l k p * tb p (eb m) (eb n)| ≤ ∑ p : Fin 27, |iMat (R := ℤ) l k p * tb p (eb m) (eb n)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p : Fin 27, entryMass l * tabTotal := by
          apply Finset.sum_le_sum; intro p _
          rw [abs_mul]; simp only [iMat, Int.cast_id]
          have t := tb_abs_le p (eb m) (eb n) 1 1 (eb_abs_le m) (eb_abs_le n) (by norm_num) (by norm_num)
          have t2 := tabMass_le_total p
          nlinarith [iAt_abs_le l k p, abs_nonneg (iAt l k p), abs_nonneg (tb p (eb (R := ℤ) m) (eb n))]
      _ = 27 * (entryMass l * tabTotal) := by simp
  have b2 : |tb k (mv (iMat l) (eb m)) (eb n)| ≤ tabTotal * (entryMass l) := by
    have := tb_abs_le k (mv (iMat l) (eb m)) (eb n) (entryMass l) 1 (mv_eb_abs_le l m) (eb_abs_le n) hE (by norm_num)
    have t2 := tabMass_le_total k
    nlinarith [tabMass_nonneg k]
  have b3 : |tb k (eb m) (mv (iMat l) (eb n))| ≤ tabTotal * (entryMass l) := by
    have := tb_abs_le k (eb m) (mv (iMat l) (eb n)) 1 (entryMass l) (eb_abs_le m) (mv_eb_abs_le l n) (by norm_num) hE
    have t2 := tabMass_le_total k
    nlinarith [tabMass_nonneg k]
  unfold defect derBound
  have := abs_sub (∑ p, iMat (R := ℤ) l k p * tb p (eb m) (eb n) - tb k (mv (iMat l) (eb m)) (eb n))
    (tb k (eb m) (mv (iMat l) (eb n)))
  have := abs_sub (∑ p, iMat (R := ℤ) l k p * tb p (eb m) (eb n)) (tb k (mv (iMat l) (eb m)) (eb n))
  nlinarith

/-! ## The Kronecker evaluation -/

def kX : ℤ := 2 ^ 32

def yS (m : Fin 27) : ℤ := kX ^ m.val
def zS (n : Fin 27) : ℤ := kX ^ (27 * n.val)
def wS (k : Fin 27) : ℤ := kX ^ (729 * k.val)

/-- The single integer decided by the kernel. -/
def kron (l : List IEnt) : ℤ := ∑ k, wS k * defect (iMat l) yS zS k

theorem kron_expand (l : List IEnt) :
    kron l = ∑ x : Fin 27 × Fin 27 × Fin 27,
      defect (iMat (R := ℤ) l) (eb x.2.1) (eb x.2.2) x.1 * kX ^ (729 * x.1.val + 27 * x.2.2.val + x.2.1.val) := by
  unfold kron
  rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro k _
  rw [Fintype.sum_prod_type, defect_expand, Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro n _
  simp only [wS, yS, zS, pow_add]; ring

theorem kron_coeff_zero (l : List IEnt) (hb : derBound l < kX) (h : kron l = 0) :
    ∀ k m n, defect (iMat (R := ℤ) l) (eb m) (eb n) k = 0 := by
  classical
  intro k m n
  let f : Fin 27 × Fin 27 × Fin 27 → ℕ := fun x => 729 * x.1.val + 27 * x.2.2.val + x.2.1.val
  have hinj : Function.Injective f := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ hx
    simp only [f] at hx
    have := a.isLt; have := b.isLt; have := c.isLt; have := a'.isLt; have := b'.isLt; have := c'.isLt
    have e1 : b.val = b'.val := by omega
    have e2 : c.val = c'.val := by omega
    have e3 : a.val = a'.val := by omega
    simp only [Prod.mk.injEq]; exact ⟨Fin.ext e3, Fin.ext e1, Fin.ext e2⟩
  let cf : ℕ → ℤ := fun e => ∑ x ∈ Finset.univ.filter (fun x => f x = e),
    defect (iMat (R := ℤ) l) (eb x.2.1) (eb x.2.2) x.1
  have hcf : ∀ x, cf (f x) = defect (iMat (R := ℤ) l) (eb x.2.1) (eb x.2.2) x.1 := by
    intro x
    refine Finset.sum_eq_single_of_mem x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) ?_
    intro q hq hqx; rw [Finset.mem_filter] at hq; exact absurd (hinj hq.2) hqx
  have hsum : ∑ e ∈ Finset.univ.image f, cf e * kX ^ e = 0 := by
    rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy), ← h, kron_expand]
    apply Finset.sum_congr rfl; intro x _; rw [hcf]
  have hbd : ∀ e ∈ Finset.univ.image f, |cf e| < kX := by
    intro e he; obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he
    rw [hcf]; exact lt_of_le_of_lt (defect_basis_abs_le l _ _ _) hb
  have := HTKron.digits_eq_zero kX (by norm_num [kX]) _ cf hbd hsum (f (k, m, n))
    (Finset.mem_image_of_mem f (Finset.mem_univ _))
  rwa [hcf] at this

/-- **Derivation from one exact evaluation.** -/
theorem isDer_of_kron {R : Type*} [CommRing R] (l : List IEnt) (hb : derBound l < kX) (h : kron l = 0) :
    IsDer (iMat (R := R) l) := by
  apply isDer_of_basis
  intro k m n
  have := kron_coeff_zero l hb h k m n
  have hc := cast_defect (R := R) (iMat (R := ℤ) l) m n k
  rw [this, Int.cast_zero] at hc
  have e : (fun k c => ((iMat (R := ℤ) l k c : ℤ) : R)) = iMat l := by
    funext k c; simp [iMat]
  rw [e] at hc; exact hc.symm

/-! ## Skewness, unit, trace from finite checks -/

def skewOK (l : List IEnt) : Bool :=
  (List.finRange 27).all fun m => (List.finRange 27).all fun n =>
    coordinateTraceWeight m * iAt l m n + coordinateTraceWeight n * iAt l n m = 0

def unitOK (l : List IEnt) : Bool :=
  (List.finRange 27).all fun m => iAt l m 0 + iAt l m 1 + iAt l m 2 = 0

def traceOK (l : List IEnt) : Bool :=
  (List.finRange 27).all fun n => iAt l 0 n + iAt l 1 n + iAt l 2 n = 0

theorem isSkew_of {R : Type*} [CommRing R] (l : List IEnt) (h : skewOK l = true) : IsSkew (iMat (R := R) l) := by
  intro m n
  have := h; simp only [skewOK, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] at this
  have e := this m n
  simp only [iMat]; exact_mod_cast congrArg (Int.cast : ℤ → R) e |>.trans Int.cast_zero

theorem killsUnit_of {R : Type*} [CommRing R] (l : List IEnt) (h : unitOK l = true) : KillsUnit (iMat (R := R) l) := by
  intro m
  have := h; simp only [unitOK, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] at this
  simp only [iMat]; exact_mod_cast congrArg (Int.cast : ℤ → R) (this m) |>.trans Int.cast_zero

theorem traceFree_of {R : Type*} [CommRing R] (l : List IEnt) (h : traceOK l = true) : TraceFree (iMat (R := R) l) := by
  intro n
  have := h; simp only [traceOK, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] at this
  simp only [iMat]; exact_mod_cast congrArg (Int.cast : ℤ → R) (this n) |>.trans Int.cast_zero


end Option2.NativeStress.HTPhaseComplete

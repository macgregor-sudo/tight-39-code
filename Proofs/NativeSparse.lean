module

public import NativeCoordinateProductTrace

@[expose] public section

/-!
# Sparse form of the native coordinate product, output by output

For each output coordinate k the integer tensor `numerator i j k` is a literal
sparse table, checked by `decide`, and the contraction `coordinateProduct h x y k`
is written as the corresponding explicit polynomial.  First-party composition over
the imported native definitions; no proof body is copied.
-/

namespace TitsS.Sparse

open NativePolynomial.CoordinateMaps NativePolynomial.IntegralStructureConstants

/-- Sum of the table values at position (i, j). -/
def sumIte (T : List (Fin 27 × Fin 27 × ℤ)) (i j : Fin 27) : ℤ :=
  (T.map fun e => if i = e.1 ∧ j = e.2.1 then e.2.2 else 0).sum

variable {S : Type*} [CommRing S]

theorem sum_sum_ite (h : S) (x y : Fin 27 → S) (e : Fin 27 × Fin 27 × ℤ) :
    (∑ i, ∑ j, x i * y j * (h * ((if i = e.1 ∧ j = e.2.1 then e.2.2 else 0 : ℤ) : S))) =
      h * (e.2.2 : S) * x e.1 * y e.2.1 := by
  have : ∀ i j : Fin 27,
      x i * y j * (h * ((if i = e.1 ∧ j = e.2.1 then e.2.2 else 0 : ℤ) : S)) =
        if j = e.2.1 then (if i = e.1 then h * (e.2.2 : S) * x i * y j else 0) else 0 := by
    intro i j
    by_cases hi : i = e.1 <;> by_cases hj : j = e.2.1 <;> simp [hi, hj] <;> ring
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem contraction_of_table (h : S) (x y : Fin 27 → S)
    (T : List (Fin 27 × Fin 27 × ℤ)) (N : Fin 27 → Fin 27 → ℤ)
    (hT : ∀ i j, N i j = sumIte T i j) :
    (∑ i, ∑ j, x i * y j * (h * (N i j : S))) =
      (T.map fun e => h * (e.2.2 : S) * x e.1 * y e.2.1).sum := by
  induction T generalizing N with
  | nil =>
    simp only [sumIte, List.map_nil, List.sum_nil] at hT
    simp [hT]
  | cons e T ih =>
    have hN : ∀ i j, N i j = (if i = e.1 ∧ j = e.2.1 then e.2.2 else 0) + sumIte T i j := by
      intro i j
      rw [hT]
      simp [sumIte]
    have hsplit : (∑ i, ∑ j, x i * y j * (h * (N i j : S))) =
        (∑ i, ∑ j, x i * y j * (h * ((if i = e.1 ∧ j = e.2.1 then e.2.2 else 0 : ℤ) : S))) +
        (∑ i, ∑ j, x i * y j * (h * (sumIte T i j : S))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [hN]
      push_cast
      ring
    rw [hsplit, sum_sum_ite, ih (sumIte T) (fun _ _ => rfl)]
    simp

theorem coordinateProduct_of_table (h : S) (x y : Fin 27 → S) (k : Fin 27)
    (T : List (Fin 27 × Fin 27 × ℤ)) (hT : ∀ i j, numerator i j k = sumIte T i j) :
    coordinateProduct h x y k = (T.map fun e => h * (e.2.2 : S) * x e.1 * y e.2.1).sum := by
  rw [coordinateProduct_apply]
  exact contraction_of_table h x y T (fun i j => numerator i j k) hT

def tbl0 : List (Fin 27 × Fin 27 × ℤ) := [(0, 0, 2), (3, 3, 2), (4, 4, 2), (5, 5, 2), (6, 6, 2), (7, 7, 2), (8, 8, 2), (9, 9, 2), (10, 10, 2), (11, 11, 2), (12, 12, 2), (13, 13, 2), (14, 14, 2), (15, 15, 2), (16, 16, 2), (17, 17, 2), (18, 18, 2)]
theorem numerator_tbl0 : ∀ i j, numerator i j 0 = sumIte tbl0 i j := by decide
theorem coord0 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 0 = h * (2 * x 0 * y 0 + 2 * x 3 * y 3 + 2 * x 4 * y 4 + 2 * x 5 * y 5 + 2 * x 6 * y 6 + 2 * x 7 * y 7 + 2 * x 8 * y 8 + 2 * x 9 * y 9 + 2 * x 10 * y 10 + 2 * x 11 * y 11 + 2 * x 12 * y 12 + 2 * x 13 * y 13 + 2 * x 14 * y 14 + 2 * x 15 * y 15 + 2 * x 16 * y 16 + 2 * x 17 * y 17 + 2 * x 18 * y 18) := by
  rw [coordinateProduct_of_table h x y 0 tbl0 numerator_tbl0]
  simp only [tbl0, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl1 : List (Fin 27 × Fin 27 × ℤ) := [(1, 1, 2), (3, 3, 2), (4, 4, 2), (5, 5, 2), (6, 6, 2), (7, 7, 2), (8, 8, 2), (9, 9, 2), (10, 10, 2), (19, 19, 2), (20, 20, 2), (21, 21, 2), (22, 22, 2), (23, 23, 2), (24, 24, 2), (25, 25, 2), (26, 26, 2)]
theorem numerator_tbl1 : ∀ i j, numerator i j 1 = sumIte tbl1 i j := by decide
theorem coord1 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 1 = h * (2 * x 1 * y 1 + 2 * x 3 * y 3 + 2 * x 4 * y 4 + 2 * x 5 * y 5 + 2 * x 6 * y 6 + 2 * x 7 * y 7 + 2 * x 8 * y 8 + 2 * x 9 * y 9 + 2 * x 10 * y 10 + 2 * x 19 * y 19 + 2 * x 20 * y 20 + 2 * x 21 * y 21 + 2 * x 22 * y 22 + 2 * x 23 * y 23 + 2 * x 24 * y 24 + 2 * x 25 * y 25 + 2 * x 26 * y 26) := by
  rw [coordinateProduct_of_table h x y 1 tbl1 numerator_tbl1]
  simp only [tbl1, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl2 : List (Fin 27 × Fin 27 × ℤ) := [(2, 2, 2), (11, 11, 2), (12, 12, 2), (13, 13, 2), (14, 14, 2), (15, 15, 2), (16, 16, 2), (17, 17, 2), (18, 18, 2), (19, 19, 2), (20, 20, 2), (21, 21, 2), (22, 22, 2), (23, 23, 2), (24, 24, 2), (25, 25, 2), (26, 26, 2)]
theorem numerator_tbl2 : ∀ i j, numerator i j 2 = sumIte tbl2 i j := by decide
theorem coord2 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 2 = h * (2 * x 2 * y 2 + 2 * x 11 * y 11 + 2 * x 12 * y 12 + 2 * x 13 * y 13 + 2 * x 14 * y 14 + 2 * x 15 * y 15 + 2 * x 16 * y 16 + 2 * x 17 * y 17 + 2 * x 18 * y 18 + 2 * x 19 * y 19 + 2 * x 20 * y 20 + 2 * x 21 * y 21 + 2 * x 22 * y 22 + 2 * x 23 * y 23 + 2 * x 24 * y 24 + 2 * x 25 * y 25 + 2 * x 26 * y 26) := by
  rw [coordinateProduct_of_table h x y 2 tbl2 numerator_tbl2]
  simp only [tbl2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl3 : List (Fin 27 × Fin 27 × ℤ) := [(0, 3, 1), (1, 3, 1), (3, 0, 1), (3, 1, 1), (11, 19, 1), (12, 20, 1), (13, 21, 1), (14, 22, 1), (15, 23, 1), (16, 24, 1), (17, 25, 1), (18, 26, 1), (19, 11, 1), (20, 12, 1), (21, 13, 1), (22, 14, 1), (23, 15, 1), (24, 16, 1), (25, 17, 1), (26, 18, 1)]
theorem numerator_tbl3 : ∀ i j, numerator i j 3 = sumIte tbl3 i j := by decide
theorem coord3 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 3 = h * (x 0 * y 3 + x 1 * y 3 + x 3 * y 0 + x 3 * y 1 + x 11 * y 19 + x 12 * y 20 + x 13 * y 21 + x 14 * y 22 + x 15 * y 23 + x 16 * y 24 + x 17 * y 25 + x 18 * y 26 + x 19 * y 11 + x 20 * y 12 + x 21 * y 13 + x 22 * y 14 + x 23 * y 15 + x 24 * y 16 + x 25 * y 17 + x 26 * y 18) := by
  rw [coordinateProduct_of_table h x y 3 tbl3 numerator_tbl3]
  simp only [tbl3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl4 : List (Fin 27 × Fin 27 × ℤ) := [(0, 4, 1), (1, 4, 1), (4, 0, 1), (4, 1, 1), (11, 20, -1), (12, 19, 1), (13, 22, -1), (14, 21, 1), (15, 24, -1), (16, 23, 1), (17, 26, 1), (18, 25, -1), (19, 12, 1), (20, 11, -1), (21, 14, 1), (22, 13, -1), (23, 16, 1), (24, 15, -1), (25, 18, -1), (26, 17, 1)]
theorem numerator_tbl4 : ∀ i j, numerator i j 4 = sumIte tbl4 i j := by decide
theorem coord4 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 4 = h * (x 0 * y 4 + x 1 * y 4 + x 4 * y 0 + x 4 * y 1 + -(x 11 * y 20) + x 12 * y 19 + -(x 13 * y 22) + x 14 * y 21 + -(x 15 * y 24) + x 16 * y 23 + x 17 * y 26 + -(x 18 * y 25) + x 19 * y 12 + -(x 20 * y 11) + x 21 * y 14 + -(x 22 * y 13) + x 23 * y 16 + -(x 24 * y 15) + -(x 25 * y 18) + x 26 * y 17) := by
  rw [coordinateProduct_of_table h x y 4 tbl4 numerator_tbl4]
  simp only [tbl4, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl5 : List (Fin 27 × Fin 27 × ℤ) := [(0, 5, 1), (1, 5, 1), (5, 0, 1), (5, 1, 1), (11, 21, -1), (12, 22, 1), (13, 19, 1), (14, 20, -1), (15, 25, -1), (16, 26, -1), (17, 23, 1), (18, 24, 1), (19, 13, 1), (20, 14, -1), (21, 11, -1), (22, 12, 1), (23, 17, 1), (24, 18, 1), (25, 15, -1), (26, 16, -1)]
theorem numerator_tbl5 : ∀ i j, numerator i j 5 = sumIte tbl5 i j := by decide
theorem coord5 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 5 = h * (x 0 * y 5 + x 1 * y 5 + x 5 * y 0 + x 5 * y 1 + -(x 11 * y 21) + x 12 * y 22 + x 13 * y 19 + -(x 14 * y 20) + -(x 15 * y 25) + -(x 16 * y 26) + x 17 * y 23 + x 18 * y 24 + x 19 * y 13 + -(x 20 * y 14) + -(x 21 * y 11) + x 22 * y 12 + x 23 * y 17 + x 24 * y 18 + -(x 25 * y 15) + -(x 26 * y 16)) := by
  rw [coordinateProduct_of_table h x y 5 tbl5 numerator_tbl5]
  simp only [tbl5, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl6 : List (Fin 27 × Fin 27 × ℤ) := [(0, 6, 1), (1, 6, 1), (6, 0, 1), (6, 1, 1), (11, 22, -1), (12, 21, -1), (13, 20, 1), (14, 19, 1), (15, 26, -1), (16, 25, 1), (17, 24, -1), (18, 23, 1), (19, 14, 1), (20, 13, 1), (21, 12, -1), (22, 11, -1), (23, 18, 1), (24, 17, -1), (25, 16, 1), (26, 15, -1)]
theorem numerator_tbl6 : ∀ i j, numerator i j 6 = sumIte tbl6 i j := by decide
theorem coord6 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 6 = h * (x 0 * y 6 + x 1 * y 6 + x 6 * y 0 + x 6 * y 1 + -(x 11 * y 22) + -(x 12 * y 21) + x 13 * y 20 + x 14 * y 19 + -(x 15 * y 26) + x 16 * y 25 + -(x 17 * y 24) + x 18 * y 23 + x 19 * y 14 + x 20 * y 13 + -(x 21 * y 12) + -(x 22 * y 11) + x 23 * y 18 + -(x 24 * y 17) + x 25 * y 16 + -(x 26 * y 15)) := by
  rw [coordinateProduct_of_table h x y 6 tbl6 numerator_tbl6]
  simp only [tbl6, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl7 : List (Fin 27 × Fin 27 × ℤ) := [(0, 7, 1), (1, 7, 1), (7, 0, 1), (7, 1, 1), (11, 23, -1), (12, 24, 1), (13, 25, 1), (14, 26, 1), (15, 19, 1), (16, 20, -1), (17, 21, -1), (18, 22, -1), (19, 15, 1), (20, 16, -1), (21, 17, -1), (22, 18, -1), (23, 11, -1), (24, 12, 1), (25, 13, 1), (26, 14, 1)]
theorem numerator_tbl7 : ∀ i j, numerator i j 7 = sumIte tbl7 i j := by decide
theorem coord7 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 7 = h * (x 0 * y 7 + x 1 * y 7 + x 7 * y 0 + x 7 * y 1 + -(x 11 * y 23) + x 12 * y 24 + x 13 * y 25 + x 14 * y 26 + x 15 * y 19 + -(x 16 * y 20) + -(x 17 * y 21) + -(x 18 * y 22) + x 19 * y 15 + -(x 20 * y 16) + -(x 21 * y 17) + -(x 22 * y 18) + -(x 23 * y 11) + x 24 * y 12 + x 25 * y 13 + x 26 * y 14) := by
  rw [coordinateProduct_of_table h x y 7 tbl7 numerator_tbl7]
  simp only [tbl7, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl8 : List (Fin 27 × Fin 27 × ℤ) := [(0, 8, 1), (1, 8, 1), (8, 0, 1), (8, 1, 1), (11, 24, -1), (12, 23, -1), (13, 26, 1), (14, 25, -1), (15, 20, 1), (16, 19, 1), (17, 22, 1), (18, 21, -1), (19, 16, 1), (20, 15, 1), (21, 18, -1), (22, 17, 1), (23, 12, -1), (24, 11, -1), (25, 14, -1), (26, 13, 1)]
theorem numerator_tbl8 : ∀ i j, numerator i j 8 = sumIte tbl8 i j := by decide
theorem coord8 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 8 = h * (x 0 * y 8 + x 1 * y 8 + x 8 * y 0 + x 8 * y 1 + -(x 11 * y 24) + -(x 12 * y 23) + x 13 * y 26 + -(x 14 * y 25) + x 15 * y 20 + x 16 * y 19 + x 17 * y 22 + -(x 18 * y 21) + x 19 * y 16 + x 20 * y 15 + -(x 21 * y 18) + x 22 * y 17 + -(x 23 * y 12) + -(x 24 * y 11) + -(x 25 * y 14) + x 26 * y 13) := by
  rw [coordinateProduct_of_table h x y 8 tbl8 numerator_tbl8]
  simp only [tbl8, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl9 : List (Fin 27 × Fin 27 × ℤ) := [(0, 9, 1), (1, 9, 1), (9, 0, 1), (9, 1, 1), (11, 25, -1), (12, 26, -1), (13, 23, -1), (14, 24, 1), (15, 21, 1), (16, 22, -1), (17, 19, 1), (18, 20, 1), (19, 17, 1), (20, 18, 1), (21, 15, 1), (22, 16, -1), (23, 13, -1), (24, 14, 1), (25, 11, -1), (26, 12, -1)]
theorem numerator_tbl9 : ∀ i j, numerator i j 9 = sumIte tbl9 i j := by decide
theorem coord9 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 9 = h * (x 0 * y 9 + x 1 * y 9 + x 9 * y 0 + x 9 * y 1 + -(x 11 * y 25) + -(x 12 * y 26) + -(x 13 * y 23) + x 14 * y 24 + x 15 * y 21 + -(x 16 * y 22) + x 17 * y 19 + x 18 * y 20 + x 19 * y 17 + x 20 * y 18 + x 21 * y 15 + -(x 22 * y 16) + -(x 23 * y 13) + x 24 * y 14 + -(x 25 * y 11) + -(x 26 * y 12)) := by
  rw [coordinateProduct_of_table h x y 9 tbl9 numerator_tbl9]
  simp only [tbl9, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl10 : List (Fin 27 × Fin 27 × ℤ) := [(0, 10, 1), (1, 10, 1), (10, 0, 1), (10, 1, 1), (11, 26, -1), (12, 25, 1), (13, 24, -1), (14, 23, -1), (15, 22, 1), (16, 21, 1), (17, 20, -1), (18, 19, 1), (19, 18, 1), (20, 17, -1), (21, 16, 1), (22, 15, 1), (23, 14, -1), (24, 13, -1), (25, 12, 1), (26, 11, -1)]
theorem numerator_tbl10 : ∀ i j, numerator i j 10 = sumIte tbl10 i j := by decide
theorem coord10 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 10 = h * (x 0 * y 10 + x 1 * y 10 + x 10 * y 0 + x 10 * y 1 + -(x 11 * y 26) + x 12 * y 25 + -(x 13 * y 24) + -(x 14 * y 23) + x 15 * y 22 + x 16 * y 21 + -(x 17 * y 20) + x 18 * y 19 + x 19 * y 18 + -(x 20 * y 17) + x 21 * y 16 + x 22 * y 15 + -(x 23 * y 14) + -(x 24 * y 13) + x 25 * y 12 + -(x 26 * y 11)) := by
  rw [coordinateProduct_of_table h x y 10 tbl10 numerator_tbl10]
  simp only [tbl10, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl11 : List (Fin 27 × Fin 27 × ℤ) := [(0, 11, 1), (2, 11, 1), (3, 19, 1), (4, 20, -1), (5, 21, -1), (6, 22, -1), (7, 23, -1), (8, 24, -1), (9, 25, -1), (10, 26, -1), (11, 0, 1), (11, 2, 1), (19, 3, 1), (20, 4, -1), (21, 5, -1), (22, 6, -1), (23, 7, -1), (24, 8, -1), (25, 9, -1), (26, 10, -1)]
theorem numerator_tbl11 : ∀ i j, numerator i j 11 = sumIte tbl11 i j := by decide
theorem coord11 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 11 = h * (x 0 * y 11 + x 2 * y 11 + x 3 * y 19 + -(x 4 * y 20) + -(x 5 * y 21) + -(x 6 * y 22) + -(x 7 * y 23) + -(x 8 * y 24) + -(x 9 * y 25) + -(x 10 * y 26) + x 11 * y 0 + x 11 * y 2 + x 19 * y 3 + -(x 20 * y 4) + -(x 21 * y 5) + -(x 22 * y 6) + -(x 23 * y 7) + -(x 24 * y 8) + -(x 25 * y 9) + -(x 26 * y 10)) := by
  rw [coordinateProduct_of_table h x y 11 tbl11 numerator_tbl11]
  simp only [tbl11, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl12 : List (Fin 27 × Fin 27 × ℤ) := [(0, 12, 1), (2, 12, 1), (3, 20, 1), (4, 19, 1), (5, 22, 1), (6, 21, -1), (7, 24, 1), (8, 23, -1), (9, 26, -1), (10, 25, 1), (12, 0, 1), (12, 2, 1), (19, 4, 1), (20, 3, 1), (21, 6, -1), (22, 5, 1), (23, 8, -1), (24, 7, 1), (25, 10, 1), (26, 9, -1)]
theorem numerator_tbl12 : ∀ i j, numerator i j 12 = sumIte tbl12 i j := by decide
theorem coord12 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 12 = h * (x 0 * y 12 + x 2 * y 12 + x 3 * y 20 + x 4 * y 19 + x 5 * y 22 + -(x 6 * y 21) + x 7 * y 24 + -(x 8 * y 23) + -(x 9 * y 26) + x 10 * y 25 + x 12 * y 0 + x 12 * y 2 + x 19 * y 4 + x 20 * y 3 + -(x 21 * y 6) + x 22 * y 5 + -(x 23 * y 8) + x 24 * y 7 + x 25 * y 10 + -(x 26 * y 9)) := by
  rw [coordinateProduct_of_table h x y 12 tbl12 numerator_tbl12]
  simp only [tbl12, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl13 : List (Fin 27 × Fin 27 × ℤ) := [(0, 13, 1), (2, 13, 1), (3, 21, 1), (4, 22, -1), (5, 19, 1), (6, 20, 1), (7, 25, 1), (8, 26, 1), (9, 23, -1), (10, 24, -1), (13, 0, 1), (13, 2, 1), (19, 5, 1), (20, 6, 1), (21, 3, 1), (22, 4, -1), (23, 9, -1), (24, 10, -1), (25, 7, 1), (26, 8, 1)]
theorem numerator_tbl13 : ∀ i j, numerator i j 13 = sumIte tbl13 i j := by decide
theorem coord13 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 13 = h * (x 0 * y 13 + x 2 * y 13 + x 3 * y 21 + -(x 4 * y 22) + x 5 * y 19 + x 6 * y 20 + x 7 * y 25 + x 8 * y 26 + -(x 9 * y 23) + -(x 10 * y 24) + x 13 * y 0 + x 13 * y 2 + x 19 * y 5 + x 20 * y 6 + x 21 * y 3 + -(x 22 * y 4) + -(x 23 * y 9) + -(x 24 * y 10) + x 25 * y 7 + x 26 * y 8) := by
  rw [coordinateProduct_of_table h x y 13 tbl13 numerator_tbl13]
  simp only [tbl13, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl14 : List (Fin 27 × Fin 27 × ℤ) := [(0, 14, 1), (2, 14, 1), (3, 22, 1), (4, 21, 1), (5, 20, -1), (6, 19, 1), (7, 26, 1), (8, 25, -1), (9, 24, 1), (10, 23, -1), (14, 0, 1), (14, 2, 1), (19, 6, 1), (20, 5, -1), (21, 4, 1), (22, 3, 1), (23, 10, -1), (24, 9, 1), (25, 8, -1), (26, 7, 1)]
theorem numerator_tbl14 : ∀ i j, numerator i j 14 = sumIte tbl14 i j := by decide
theorem coord14 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 14 = h * (x 0 * y 14 + x 2 * y 14 + x 3 * y 22 + x 4 * y 21 + -(x 5 * y 20) + x 6 * y 19 + x 7 * y 26 + -(x 8 * y 25) + x 9 * y 24 + -(x 10 * y 23) + x 14 * y 0 + x 14 * y 2 + x 19 * y 6 + -(x 20 * y 5) + x 21 * y 4 + x 22 * y 3 + -(x 23 * y 10) + x 24 * y 9 + -(x 25 * y 8) + x 26 * y 7) := by
  rw [coordinateProduct_of_table h x y 14 tbl14 numerator_tbl14]
  simp only [tbl14, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl15 : List (Fin 27 × Fin 27 × ℤ) := [(0, 15, 1), (2, 15, 1), (3, 23, 1), (4, 24, -1), (5, 25, -1), (6, 26, -1), (7, 19, 1), (8, 20, 1), (9, 21, 1), (10, 22, 1), (15, 0, 1), (15, 2, 1), (19, 7, 1), (20, 8, 1), (21, 9, 1), (22, 10, 1), (23, 3, 1), (24, 4, -1), (25, 5, -1), (26, 6, -1)]
theorem numerator_tbl15 : ∀ i j, numerator i j 15 = sumIte tbl15 i j := by decide
theorem coord15 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 15 = h * (x 0 * y 15 + x 2 * y 15 + x 3 * y 23 + -(x 4 * y 24) + -(x 5 * y 25) + -(x 6 * y 26) + x 7 * y 19 + x 8 * y 20 + x 9 * y 21 + x 10 * y 22 + x 15 * y 0 + x 15 * y 2 + x 19 * y 7 + x 20 * y 8 + x 21 * y 9 + x 22 * y 10 + x 23 * y 3 + -(x 24 * y 4) + -(x 25 * y 5) + -(x 26 * y 6)) := by
  rw [coordinateProduct_of_table h x y 15 tbl15 numerator_tbl15]
  simp only [tbl15, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl16 : List (Fin 27 × Fin 27 × ℤ) := [(0, 16, 1), (2, 16, 1), (3, 24, 1), (4, 23, 1), (5, 26, -1), (6, 25, 1), (7, 20, -1), (8, 19, 1), (9, 22, -1), (10, 21, 1), (16, 0, 1), (16, 2, 1), (19, 8, 1), (20, 7, -1), (21, 10, 1), (22, 9, -1), (23, 4, 1), (24, 3, 1), (25, 6, 1), (26, 5, -1)]
theorem numerator_tbl16 : ∀ i j, numerator i j 16 = sumIte tbl16 i j := by decide
theorem coord16 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 16 = h * (x 0 * y 16 + x 2 * y 16 + x 3 * y 24 + x 4 * y 23 + -(x 5 * y 26) + x 6 * y 25 + -(x 7 * y 20) + x 8 * y 19 + -(x 9 * y 22) + x 10 * y 21 + x 16 * y 0 + x 16 * y 2 + x 19 * y 8 + -(x 20 * y 7) + x 21 * y 10 + -(x 22 * y 9) + x 23 * y 4 + x 24 * y 3 + x 25 * y 6 + -(x 26 * y 5)) := by
  rw [coordinateProduct_of_table h x y 16 tbl16 numerator_tbl16]
  simp only [tbl16, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl17 : List (Fin 27 × Fin 27 × ℤ) := [(0, 17, 1), (2, 17, 1), (3, 25, 1), (4, 26, 1), (5, 23, 1), (6, 24, -1), (7, 21, -1), (8, 22, 1), (9, 19, 1), (10, 20, -1), (17, 0, 1), (17, 2, 1), (19, 9, 1), (20, 10, -1), (21, 7, -1), (22, 8, 1), (23, 5, 1), (24, 6, -1), (25, 3, 1), (26, 4, 1)]
theorem numerator_tbl17 : ∀ i j, numerator i j 17 = sumIte tbl17 i j := by decide
theorem coord17 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 17 = h * (x 0 * y 17 + x 2 * y 17 + x 3 * y 25 + x 4 * y 26 + x 5 * y 23 + -(x 6 * y 24) + -(x 7 * y 21) + x 8 * y 22 + x 9 * y 19 + -(x 10 * y 20) + x 17 * y 0 + x 17 * y 2 + x 19 * y 9 + -(x 20 * y 10) + -(x 21 * y 7) + x 22 * y 8 + x 23 * y 5 + -(x 24 * y 6) + x 25 * y 3 + x 26 * y 4) := by
  rw [coordinateProduct_of_table h x y 17 tbl17 numerator_tbl17]
  simp only [tbl17, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl18 : List (Fin 27 × Fin 27 × ℤ) := [(0, 18, 1), (2, 18, 1), (3, 26, 1), (4, 25, -1), (5, 24, 1), (6, 23, 1), (7, 22, -1), (8, 21, -1), (9, 20, 1), (10, 19, 1), (18, 0, 1), (18, 2, 1), (19, 10, 1), (20, 9, 1), (21, 8, -1), (22, 7, -1), (23, 6, 1), (24, 5, 1), (25, 4, -1), (26, 3, 1)]
theorem numerator_tbl18 : ∀ i j, numerator i j 18 = sumIte tbl18 i j := by decide
theorem coord18 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 18 = h * (x 0 * y 18 + x 2 * y 18 + x 3 * y 26 + -(x 4 * y 25) + x 5 * y 24 + x 6 * y 23 + -(x 7 * y 22) + -(x 8 * y 21) + x 9 * y 20 + x 10 * y 19 + x 18 * y 0 + x 18 * y 2 + x 19 * y 10 + x 20 * y 9 + -(x 21 * y 8) + -(x 22 * y 7) + x 23 * y 6 + x 24 * y 5 + -(x 25 * y 4) + x 26 * y 3) := by
  rw [coordinateProduct_of_table h x y 18 tbl18 numerator_tbl18]
  simp only [tbl18, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl19 : List (Fin 27 × Fin 27 × ℤ) := [(1, 19, 1), (2, 19, 1), (3, 11, 1), (4, 12, 1), (5, 13, 1), (6, 14, 1), (7, 15, 1), (8, 16, 1), (9, 17, 1), (10, 18, 1), (11, 3, 1), (12, 4, 1), (13, 5, 1), (14, 6, 1), (15, 7, 1), (16, 8, 1), (17, 9, 1), (18, 10, 1), (19, 1, 1), (19, 2, 1)]
theorem numerator_tbl19 : ∀ i j, numerator i j 19 = sumIte tbl19 i j := by decide
theorem coord19 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 19 = h * (x 1 * y 19 + x 2 * y 19 + x 3 * y 11 + x 4 * y 12 + x 5 * y 13 + x 6 * y 14 + x 7 * y 15 + x 8 * y 16 + x 9 * y 17 + x 10 * y 18 + x 11 * y 3 + x 12 * y 4 + x 13 * y 5 + x 14 * y 6 + x 15 * y 7 + x 16 * y 8 + x 17 * y 9 + x 18 * y 10 + x 19 * y 1 + x 19 * y 2) := by
  rw [coordinateProduct_of_table h x y 19 tbl19 numerator_tbl19]
  simp only [tbl19, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl20 : List (Fin 27 × Fin 27 × ℤ) := [(1, 20, 1), (2, 20, 1), (3, 12, 1), (4, 11, -1), (5, 14, -1), (6, 13, 1), (7, 16, -1), (8, 15, 1), (9, 18, 1), (10, 17, -1), (11, 4, -1), (12, 3, 1), (13, 6, 1), (14, 5, -1), (15, 8, 1), (16, 7, -1), (17, 10, -1), (18, 9, 1), (20, 1, 1), (20, 2, 1)]
theorem numerator_tbl20 : ∀ i j, numerator i j 20 = sumIte tbl20 i j := by decide
theorem coord20 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 20 = h * (x 1 * y 20 + x 2 * y 20 + x 3 * y 12 + -(x 4 * y 11) + -(x 5 * y 14) + x 6 * y 13 + -(x 7 * y 16) + x 8 * y 15 + x 9 * y 18 + -(x 10 * y 17) + -(x 11 * y 4) + x 12 * y 3 + x 13 * y 6 + -(x 14 * y 5) + x 15 * y 8 + -(x 16 * y 7) + -(x 17 * y 10) + x 18 * y 9 + x 20 * y 1 + x 20 * y 2) := by
  rw [coordinateProduct_of_table h x y 20 tbl20 numerator_tbl20]
  simp only [tbl20, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl21 : List (Fin 27 × Fin 27 × ℤ) := [(1, 21, 1), (2, 21, 1), (3, 13, 1), (4, 14, 1), (5, 11, -1), (6, 12, -1), (7, 17, -1), (8, 18, -1), (9, 15, 1), (10, 16, 1), (11, 5, -1), (12, 6, -1), (13, 3, 1), (14, 4, 1), (15, 9, 1), (16, 10, 1), (17, 7, -1), (18, 8, -1), (21, 1, 1), (21, 2, 1)]
theorem numerator_tbl21 : ∀ i j, numerator i j 21 = sumIte tbl21 i j := by decide
theorem coord21 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 21 = h * (x 1 * y 21 + x 2 * y 21 + x 3 * y 13 + x 4 * y 14 + -(x 5 * y 11) + -(x 6 * y 12) + -(x 7 * y 17) + -(x 8 * y 18) + x 9 * y 15 + x 10 * y 16 + -(x 11 * y 5) + -(x 12 * y 6) + x 13 * y 3 + x 14 * y 4 + x 15 * y 9 + x 16 * y 10 + -(x 17 * y 7) + -(x 18 * y 8) + x 21 * y 1 + x 21 * y 2) := by
  rw [coordinateProduct_of_table h x y 21 tbl21 numerator_tbl21]
  simp only [tbl21, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl22 : List (Fin 27 × Fin 27 × ℤ) := [(1, 22, 1), (2, 22, 1), (3, 14, 1), (4, 13, -1), (5, 12, 1), (6, 11, -1), (7, 18, -1), (8, 17, 1), (9, 16, -1), (10, 15, 1), (11, 6, -1), (12, 5, 1), (13, 4, -1), (14, 3, 1), (15, 10, 1), (16, 9, -1), (17, 8, 1), (18, 7, -1), (22, 1, 1), (22, 2, 1)]
theorem numerator_tbl22 : ∀ i j, numerator i j 22 = sumIte tbl22 i j := by decide
theorem coord22 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 22 = h * (x 1 * y 22 + x 2 * y 22 + x 3 * y 14 + -(x 4 * y 13) + x 5 * y 12 + -(x 6 * y 11) + -(x 7 * y 18) + x 8 * y 17 + -(x 9 * y 16) + x 10 * y 15 + -(x 11 * y 6) + x 12 * y 5 + -(x 13 * y 4) + x 14 * y 3 + x 15 * y 10 + -(x 16 * y 9) + x 17 * y 8 + -(x 18 * y 7) + x 22 * y 1 + x 22 * y 2) := by
  rw [coordinateProduct_of_table h x y 22 tbl22 numerator_tbl22]
  simp only [tbl22, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl23 : List (Fin 27 × Fin 27 × ℤ) := [(1, 23, 1), (2, 23, 1), (3, 15, 1), (4, 16, 1), (5, 17, 1), (6, 18, 1), (7, 11, -1), (8, 12, -1), (9, 13, -1), (10, 14, -1), (11, 7, -1), (12, 8, -1), (13, 9, -1), (14, 10, -1), (15, 3, 1), (16, 4, 1), (17, 5, 1), (18, 6, 1), (23, 1, 1), (23, 2, 1)]
theorem numerator_tbl23 : ∀ i j, numerator i j 23 = sumIte tbl23 i j := by decide
theorem coord23 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 23 = h * (x 1 * y 23 + x 2 * y 23 + x 3 * y 15 + x 4 * y 16 + x 5 * y 17 + x 6 * y 18 + -(x 7 * y 11) + -(x 8 * y 12) + -(x 9 * y 13) + -(x 10 * y 14) + -(x 11 * y 7) + -(x 12 * y 8) + -(x 13 * y 9) + -(x 14 * y 10) + x 15 * y 3 + x 16 * y 4 + x 17 * y 5 + x 18 * y 6 + x 23 * y 1 + x 23 * y 2) := by
  rw [coordinateProduct_of_table h x y 23 tbl23 numerator_tbl23]
  simp only [tbl23, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl24 : List (Fin 27 × Fin 27 × ℤ) := [(1, 24, 1), (2, 24, 1), (3, 16, 1), (4, 15, -1), (5, 18, 1), (6, 17, -1), (7, 12, 1), (8, 11, -1), (9, 14, 1), (10, 13, -1), (11, 8, -1), (12, 7, 1), (13, 10, -1), (14, 9, 1), (15, 4, -1), (16, 3, 1), (17, 6, -1), (18, 5, 1), (24, 1, 1), (24, 2, 1)]
theorem numerator_tbl24 : ∀ i j, numerator i j 24 = sumIte tbl24 i j := by decide
theorem coord24 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 24 = h * (x 1 * y 24 + x 2 * y 24 + x 3 * y 16 + -(x 4 * y 15) + x 5 * y 18 + -(x 6 * y 17) + x 7 * y 12 + -(x 8 * y 11) + x 9 * y 14 + -(x 10 * y 13) + -(x 11 * y 8) + x 12 * y 7 + -(x 13 * y 10) + x 14 * y 9 + -(x 15 * y 4) + x 16 * y 3 + -(x 17 * y 6) + x 18 * y 5 + x 24 * y 1 + x 24 * y 2) := by
  rw [coordinateProduct_of_table h x y 24 tbl24 numerator_tbl24]
  simp only [tbl24, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl25 : List (Fin 27 × Fin 27 × ℤ) := [(1, 25, 1), (2, 25, 1), (3, 17, 1), (4, 18, -1), (5, 15, -1), (6, 16, 1), (7, 13, 1), (8, 14, -1), (9, 11, -1), (10, 12, 1), (11, 9, -1), (12, 10, 1), (13, 7, 1), (14, 8, -1), (15, 5, -1), (16, 6, 1), (17, 3, 1), (18, 4, -1), (25, 1, 1), (25, 2, 1)]
theorem numerator_tbl25 : ∀ i j, numerator i j 25 = sumIte tbl25 i j := by decide
theorem coord25 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 25 = h * (x 1 * y 25 + x 2 * y 25 + x 3 * y 17 + -(x 4 * y 18) + -(x 5 * y 15) + x 6 * y 16 + x 7 * y 13 + -(x 8 * y 14) + -(x 9 * y 11) + x 10 * y 12 + -(x 11 * y 9) + x 12 * y 10 + x 13 * y 7 + -(x 14 * y 8) + -(x 15 * y 5) + x 16 * y 6 + x 17 * y 3 + -(x 18 * y 4) + x 25 * y 1 + x 25 * y 2) := by
  rw [coordinateProduct_of_table h x y 25 tbl25 numerator_tbl25]
  simp only [tbl25, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

def tbl26 : List (Fin 27 × Fin 27 × ℤ) := [(1, 26, 1), (2, 26, 1), (3, 18, 1), (4, 17, 1), (5, 16, -1), (6, 15, -1), (7, 14, 1), (8, 13, 1), (9, 12, -1), (10, 11, -1), (11, 10, -1), (12, 9, -1), (13, 8, 1), (14, 7, 1), (15, 6, -1), (16, 5, -1), (17, 4, 1), (18, 3, 1), (26, 1, 1), (26, 2, 1)]
theorem numerator_tbl26 : ∀ i j, numerator i j 26 = sumIte tbl26 i j := by decide
theorem coord26 (h : S) (x y : Fin 27 → S) :
    coordinateProduct h x y 26 = h * (x 1 * y 26 + x 2 * y 26 + x 3 * y 18 + x 4 * y 17 + -(x 5 * y 16) + -(x 6 * y 15) + x 7 * y 14 + x 8 * y 13 + -(x 9 * y 12) + -(x 10 * y 11) + -(x 11 * y 10) + -(x 12 * y 9) + x 13 * y 8 + x 14 * y 7 + -(x 15 * y 6) + -(x 16 * y 5) + x 17 * y 4 + x 18 * y 3 + x 26 * y 1 + x 26 * y 2) := by
  rw [coordinateProduct_of_table h x y 26 tbl26 numerator_tbl26]
  simp only [tbl26, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  ring

end TitsS.Sparse

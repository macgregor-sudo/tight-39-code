module

public import HTKronEngine
public import Mathlib.Data.List.GetD

@[expose] public section

/-!
# Semantics of the computational evaluators of `HTKronEngine`

First-party code. Every kernel-friendly evaluator of
`HTKronEngine` is identified with the corresponding ring expression in `Z4`:
`sumZ` is `List.sum`, `idVal` is the weighted sum of products over a product table, `pairDot`
is the trace-weighted pairing, and `densePoint` is the dense list of `Σ_j y_j * column_j(r)`
for strictly increasing sparse columns. No native data is evaluated here.
-/

set_option autoImplicit false

namespace Option2.NativeStress.HTRouteKron

open QuarticCertificate.RowBridge BookHT.TangentCoordinates BookHT.Dictionary
open ConfigurationResidualIndices

namespace Z4

@[simp] lemma add_eq (x y : Z4) : Z4.add x y = x + y := rfl
@[simp] lemma mul_eq (x y : Z4) : Z4.mul x y = x * y := rfl
@[simp] lemma neg_eq (x : Z4) : Z4.neg x = -x := rfl
@[simp] lemma zero_eq : Z4.zero = 0 := rfl

lemma smul_eq (n : ℤ) (x : Z4) : Z4.smul n x = (n : Z4) * x := by
  ext <;> simp

lemma isZero_spec (x : Z4) (h : Z4.isZero x = true) : x = 0 := by
  simp only [Z4.isZero, Bool.and_eq_true] at h
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ := h
  ext
  · exact Int.natAbs_eq_zero.1 (Nat.eq_of_beq_eq_true ha)
  · exact Int.natAbs_eq_zero.1 (Nat.eq_of_beq_eq_true hb)
  · exact Int.natAbs_eq_zero.1 (Nat.eq_of_beq_eq_true hc)
  · exact Int.natAbs_eq_zero.1 (Nat.eq_of_beq_eq_true hd)

end Z4

lemma addSkip_eq (x acc : Z4) : addSkip x acc = x + acc := by
  unfold addSkip
  cases h : Z4.isZero x
  · rfl
  · simp [Z4.isZero_spec x h]

lemma sumZ_eq (l : List Z4) : sumZ l = l.sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      show addSkip x (sumZ l) = _
      rw [addSkip_eq, ih, List.sum_cons]

lemma mulAt_eq (l : List Z4) (a b : ℕ) : mulAt l a b = l.getD a 0 * l.getD b 0 := by
  unfold mulAt
  cases Nat.ble a b
  · exact mul_comm _ _
  · rfl

/-- The weighted product-table sum. -/
def tableVal (l : List Z4) (t : List (Fin 27 × Fin 27 × ℤ)) : Z4 :=
  (t.map fun e => (e.2.2 : Z4) * (l.getD e.1.val 0 * l.getD e.2.1.val 0)).sum

lemma idAcc_spec (l : List Z4) (t : List (Fin 27 × Fin 27 × ℤ)) :
    (idAcc l t).1 - (idAcc l t).2 = tableVal l t := by
  induction t with
  | nil => simp [idAcc, tableVal]
  | cons e t ih =>
      have hfold : idAcc l (e :: t) =
          (let x := mulAt l e.1.val e.2.1.val
           cond (Z4.isZero x) (idAcc l t)
            (cond (e.2.2 == 1) (Z4.add x (idAcc l t).1, (idAcc l t).2)
              (cond (e.2.2 == -1) ((idAcc l t).1, Z4.add x (idAcc l t).2)
                (Z4.add (Z4.smul e.2.2 x) (idAcc l t).1, (idAcc l t).2)))) := rfl
      have ht : tableVal l (e :: t) =
          (e.2.2 : Z4) * mulAt l e.1.val e.2.1.val + tableVal l t := by
        simp [tableVal, mulAt_eq]
      rw [hfold, ht, ← ih]
      simp only
      cases hz : Z4.isZero (mulAt l e.1.val e.2.1.val)
      · cases h1 : (e.2.2 == 1)
        · cases h2 : (e.2.2 == -1)
          · simp only [Bool.cond_false, Z4.add_eq, Z4.smul_eq]
            ring
          · have : e.2.2 = -1 := by simpa using h2
            simp only [Bool.cond_false, Bool.cond_true, Z4.add_eq]
            rw [this]
            push_cast
            ring
        · have : e.2.2 = 1 := by simpa using h1
          simp only [Bool.cond_false, Bool.cond_true, Z4.add_eq]
          rw [this]
          push_cast
          ring
      · simp only [Bool.cond_true, Z4.isZero_spec _ hz, mul_zero, zero_add]

lemma idVal_eq (l : List Z4) (t : List (Fin 27 × Fin 27 × ℤ)) : idVal l t = tableVal l t := by
  rw [← idAcc_spec]
  show Z4.add (idAcc l t).1 (Z4.neg (idAcc l t).2) = _
  simp [sub_eq_add_neg]

/-- The native trace weights `1,1,1,2,...,2` (same definition as `coordinateTraceWeight`). -/
def traceW (k : Fin 27) : ℤ := if k.val < 3 then 1 else 2

lemma pairDot_ofFn (f g : Fin 27 → Z4) :
    pairDot (List.ofFn f) (List.ofFn g) = ∑ k : Fin 27, (traceW k : Z4) * (f k * g k) := by
  have hz : List.zipWith Z4.mul (List.ofFn f) (List.ofFn g) = List.ofFn fun k => f k * g k := by
    apply List.ext_getElem
    · simp
    · intro n h1 h2
      simp
  have hsplit : (List.ofFn fun k : Fin 27 => f k * g k) =
      List.ofFn (n := 3 + 24) fun k => f k * g k := rfl
  unfold pairDot
  simp only [hz, hsplit, List.ofFn_add, Z4.add_eq, Z4.smul_eq, sumZ_eq]
  simp only [List.length_ofFn, List.take_left', List.drop_left', List.sum_ofFn]
  rw [show (∑ k : Fin 27, (traceW k : Z4) * (f k * g k)) =
      ∑ k : Fin (3 + 24), (traceW k : Z4) * (f k * g k) from rfl, Fin.sum_univ_add]
  have hl (i : Fin 3) : traceW (Fin.castAdd 24 i) = 1 := by
    simp [traceW, Fin.coe_castAdd, i.isLt]
  have hr (i : Fin 24) : traceW (Fin.natAdd 3 i) = 2 := by
    simp [traceW, Fin.coe_natAdd]
  simp only [hl, hr, Int.cast_one, one_mul, Int.cast_ofNat, Finset.mul_sum]
  rfl

/-! ## The dense point -/

/-- Sparse value of a list of D6 entries at a natural index, in `Z4`. -/
def sparseZ (es : List Entry) (n : ℕ) : Z4 :=
  (es.map fun e => if e.1.val = n then ofCoeff e.2 else 0).sum

lemma sparseZ_nil (n : ℕ) : sparseZ [] n = 0 := rfl

lemma sparseZ_cons (e : Entry) (es : List Entry) (n : ℕ) :
    sparseZ (e :: es) n = (if e.1.val = n then ofCoeff e.2 else 0) + sparseZ es n := by
  simp [sparseZ]

lemma sparseZ_eq_zero (es : List Entry) (n : ℕ) (h : ∀ f ∈ es, f.1.val ≠ n) : sparseZ es n = 0 := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      rw [sparseZ_cons, if_neg (h e (by simp)), ih (fun f hf => h f (by simp [hf])), add_zero]

/-- Strictly increasing row indices, as a kernel-checkable Boolean. -/
def strictB : List Entry → Bool
  | [] => true
  | [_] => true
  | e :: f :: r => Nat.blt e.1.val f.1.val && strictB (f :: r)

lemma strictB_pairwise : ∀ l : List Entry, strictB l = true →
    l.Pairwise (fun e f => e.1.val < f.1.val)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | e :: f :: r, h => by
      simp only [strictB, Bool.and_eq_true, Nat.blt_eq] at h
      have ih := strictB_pairwise (f :: r) h.2
      refine List.Pairwise.cons ?_ ih
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact h.1
      · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hg)

lemma addCol_nil (y : ℤ) (es : List Entry) (r : ℕ) : addCol y [] es r = [] := rfl

lemma addCol_cons_nil (y : ℤ) (x : Z4) (xs : List Z4) (r : ℕ) :
    addCol y (x :: xs) [] r = x :: xs := rfl

lemma addCol_cons_cons (y : ℤ) (x : Z4) (xs : List Z4) (e : Entry) (es : List Entry) (r : ℕ) :
    addCol y (x :: xs) (e :: es) r =
      if e.1.val = r then (x + (y : Z4) * ofCoeff e.2) :: addCol y xs es (r + 1)
      else x :: addCol y xs (e :: es) (r + 1) := by
  show Bool.rec (motive := fun _ => List Z4) (x :: addCol y xs (e :: es) (Nat.succ r))
    (Z4.add x (Z4.smul y (ofCoeff e.2)) :: addCol y xs es (Nat.succ r)) (Nat.beq e.1.val r) = _
  cases h : Nat.beq e.1.val r
  · rw [if_neg (Nat.ne_of_beq_eq_false h)]
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]
    simp [Z4.smul_eq]

lemma addCol_length (y : ℤ) : ∀ (acc : List Z4) (es : List Entry) (r : ℕ),
    (addCol y acc es r).length = acc.length
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | x :: xs, e :: es, r => by
      rw [addCol_cons_cons]
      split_ifs
      · simp [addCol_length y xs es (r + 1)]
      · simp [addCol_length y xs (e :: es) (r + 1)]

lemma addCol_getD (y : ℤ) : ∀ (acc : List Z4) (es : List Entry) (r : ℕ),
    es.Pairwise (fun e f => e.1.val < f.1.val) → (∀ e ∈ es, r ≤ e.1.val) →
    ∀ i < acc.length, (addCol y acc es r).getD i 0 = acc.getD i 0 + (y : Z4) * sparseZ es (r + i)
  | [], _, _, _, _, i, hi => by simp at hi
  | x :: xs, [], r, _, _, i, _ => by simp [addCol_cons_nil, sparseZ_nil]
  | x :: xs, e :: es, r, hs, hr, i, hi => by
      have hes : es.Pairwise (fun e f => e.1.val < f.1.val) := List.Pairwise.of_cons hs
      have hgt : ∀ f ∈ es, e.1.val < f.1.val := fun f hf => List.rel_of_pairwise_cons hs hf
      rw [addCol_cons_cons]
      by_cases he : e.1.val = r
      · rw [if_pos he]
        cases i with
        | zero =>
            simp only [List.getD_cons_zero, add_zero]
            rw [sparseZ_cons, if_pos he, sparseZ_eq_zero es r
              (fun f hf => by have := hgt f hf; omega), add_zero]
        | succ i =>
            simp only [List.getD_cons_succ]
            rw [addCol_getD y xs es (r + 1) hes (fun f hf => by have := hgt f hf; omega) i
              (by simpa using hi), sparseZ_cons, if_neg (by omega), zero_add]
            congr 3
            omega
      · rw [if_neg he]
        have hr' : ∀ f ∈ e :: es, r + 1 ≤ f.1.val := by
          intro f hf
          rcases List.mem_cons.1 hf with rfl | hf
          · have := hr f (by simp); omega
          · have := hgt f hf; have := hr e (by simp); omega
        cases i with
        | zero =>
            simp only [List.getD_cons_zero, add_zero]
            rw [sparseZ_eq_zero (e :: es) r (fun f hf => by have := hr' f hf; omega), mul_zero,
              add_zero]
        | succ i =>
            simp only [List.getD_cons_succ]
            rw [addCol_getD y xs (e :: es) (r + 1) hs hr' i (by simpa using hi)]
            congr 3
            omega

/-- After folding a list of columns into a dense accumulator. -/
lemma foldCols_getD (ys : Fin 24 → ℤ) (col : Fin 24 → List Entry)
    (hs : ∀ j, (col j).Pairwise (fun e f => e.1.val < f.1.val)) :
    ∀ (js : List (Fin 24)) (acc : List Z4),
    ((js.foldl (fun acc j => addCol (ys j) acc (col j) 0) acc).length = acc.length) ∧
    ∀ n < acc.length, (js.foldl (fun acc j => addCol (ys j) acc (col j) 0) acc).getD n 0 =
      acc.getD n 0 + (js.map fun j => (ys j : Z4) * sparseZ (col j) n).sum
  | [], acc => by simp
  | j :: js, acc => by
      obtain ⟨hl, hg⟩ := foldCols_getD ys col hs js (addCol (ys j) acc (col j) 0)
      rw [addCol_length] at hl hg
      refine ⟨by simpa using hl, fun n hn => ?_⟩
      simp only [List.foldl_cons]
      rw [hg n hn, addCol_getD (ys j) acc (col j) 0 (hs j) (fun _ _ => Nat.zero_le _) n hn,
        zero_add, List.map_cons, List.sum_cons, add_assoc]

lemma densePoint_spec (ys : Fin 24 → ℤ)
    (hs : ∀ j, (d6Entries (eigenIndex j)).Pairwise (fun e f => e.1.val < f.1.val)) :
    (densePoint ys).length = 1053 ∧ ∀ n < 1053, (densePoint ys).getD n 0 =
      ∑ j : Fin 24, (ys j : Z4) * sparseZ (d6Entries (eigenIndex j)) n := by
  obtain ⟨hl, hg⟩ := foldCols_getD ys (fun j => d6Entries (eigenIndex j)) hs (List.finRange 24)
    (List.replicate 1053 Z4.zero)
  rw [List.length_replicate] at hl hg
  refine ⟨hl, fun n hn => ?_⟩
  unfold densePoint
  have h0 : (List.replicate 1053 Z4.zero).getD n 0 = 0 := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact hn), List.getElem_replicate]
    rfl
  rw [hg n hn, Fin.sum_univ_def, h0, zero_add]

/-! ## Native point blocks -/

lemma blocks_aux : ∀ (m : ℕ) (l : List Z4) (p : ℕ), p < m →
    (Nat.rec (motive := fun _ => List Z4 → List (List Z4)) (fun _ => [])
      (fun _ ih l => l.take 27 :: ih (l.drop 27)) m l).getD p [] = (l.drop (27 * p)).take 27
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, l, 0, _ => by simp
  | m + 1, l, p + 1, h => by
      show (List.getD (_ :: _) (p + 1) []) = _
      rw [List.getD_cons_succ, blocks_aux m (l.drop 27) p (by omega), List.drop_drop]
      congr 2
      omega

lemma blocks_getD (l : List Z4) (p : ℕ) (hp : p < 39) :
    (blocks l).getD p [] = (l.drop (27 * p)).take 27 :=
  blocks_aux 39 l p hp

lemma stateList_spec (ys : Fin 24 → ℤ)
    (hs : ∀ j, (d6Entries (eigenIndex j)).Pairwise (fun e f => e.1.val < f.1.val)) (p : Fin 39) :
    stateList ys p = List.ofFn fun k : Fin 27 =>
      ∑ j : Fin 24, (ys j : Z4) * sparseZ (d6Entries (eigenIndex j)) (27 * p.val + k.val) := by
  obtain ⟨hl, hg⟩ := densePoint_spec ys hs
  unfold stateList
  rw [blocks_getD _ _ p.isLt]
  apply List.ext_getElem
  · simp [hl]; omega
  · intro n h1 h2
    have hn : n < 27 := by simpa using h2
    have hlt : 27 * p.val + n < 1053 := by omega
    rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop]
    have := hg (27 * p.val + n) hlt
    rw [List.getD_eq_getElem _ _ (by omega)] at this
    exact this

lemma getD_ofFn27 (f : Fin 27 → Z4) (k : Fin 27) : (List.ofFn f).getD k.val 0 = f k := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact k.isLt), List.getElem_ofFn]

/-! ## Chunked evaluation -/

lemma engine_append (d : ℕ) (s : NativeH.HSpec) (A B : List NativeH.Entry) (S : Fin 39 → List Z4) :
    engine d s (A ++ B) S = engine d s A S + engine d s B S := by
  simp [engine, sumZ_eq, List.map_append, List.sum_append]

lemma engine_split (d : ℕ) (s : NativeH.HSpec) (es : List NativeH.Entry) (S : Fin 39 → List Z4)
    (o n : ℕ) : engine d s (es.drop o) S =
      engine d s ((es.drop o).take n) S + engine d s (es.drop (o + n)) S := by
  rw [← engine_append, ← List.drop_drop, List.take_append_drop]

lemma engine_split' (d : ℕ) (s : NativeH.HSpec) (es : List NativeH.Entry) (S : Fin 39 → List Z4)
    (o n o' : ℕ) (h : o + n = o') : engine d s (es.drop o) S =
      engine d s ((es.drop o).take n) S + engine d s (es.drop o') S := by
  rw [← h]; exact engine_split d s es S o n

lemma engine_drop_length (d : ℕ) (s : NativeH.HSpec) (es : List NativeH.Entry)
    (S : Fin 39 → List Z4) (o : ℕ) (h : es.length ≤ o) : engine d s (es.drop o) S = 0 := by
  rw [List.drop_eq_nil_of_le h]
  rfl

end Option2.NativeStress.HTRouteKron

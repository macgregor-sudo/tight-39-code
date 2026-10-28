module

public import A6SpecLin
public import RankBridge
public import A6LinTie
public import A6LinRunValid
public import A6LinRunD1
public import A6LinRunD3
public import A6LinRunD4
public import A6LinRunTie0
public import A6LinRunTie1
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-!
# Lane LIN: the linear data theorems D1–D4 (top module)

`lin_annihilates : StmtD1`, `lin_pivot : StmtD2`, `lin_vanish : StmtD3`, `lin_dim : StmtD4` (statements of
`W2/interface/A6SpecLin.lean`), for `g = translatedRowModP`, `E = id`, from
* the row tie `equationLinearMatrix translatedRowModP r a = lRow r [a]` (Q's lane-B2 `equationLinearMatrix_translate_fRow`
  + the kernel checks `A6LinRunTie*`),
* the packed-slot checks of `A6LinRunD1/D3/D4/Valid` (sound by `A6LinEngine`, `A6LinChecks`),
* CHAINMID `RankBridge` (`cutLinearSpace_nil_le_linearAnnihilator`, `le_finrank_cutLinearSpace_nil_of_det`) and Mathlib's
  triangular determinant (`Matrix.det_of_isUpperTriangular`).
No kernel evaluation in this module. First-party code.
-/

open MvPolynomial Module PolynomialJets SliceLemmas QuarticCertificate.PipelineNaturality Finset

namespace A6Compact

open LinEngine LinCheck LinTie LinRun

/-! ## Unpacked validity facts -/

theorem wRow_keys (s : ℕ) (hs : s < 48) : ∀ e ∈ wRow s, e.1 < 2184 :=
  keysBelow_iff.mp (all_range_of validW_ok s hs)

theorem bRow_keys (j : ℕ) (hj : j < 1053) : ∀ e ∈ bRow j, e.1 < 80 :=
  keysBelow_iff.mp (all_range_of validB_ok j hj)

theorem lRow_valid (r : ℕ) (hr : r < 2184) :
    keysBelow (lRow r) 1053 = true ∧ valsLe (lRow r) P = true := by
  have := all_range_of validL_ok r hr
  simpa only [Bool.and_eq_true] using this

theorem lRow_keys (r : ℕ) (hr : r < 2184) : ∀ e ∈ lRow r, e.1 < 1053 :=
  keysBelow_iff.mp (lRow_valid r hr).1

theorem lu_valid (a : ℕ) (ha : a < 973) :
    (∀ e ∈ loRow a, e.1 < a) ∧ (∀ e ∈ uRow a, a ≤ e.1 ∧ e.1 < 973) ∧ natSlot (uRow a) a % P ≠ 0 ∧
      rowSelN a < 2184 ∧ colSelN a < 1053 ∧ colPosN (colSelN a) = a := by
  have := all_range_of validLU_ok a ha
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq, Nat.beq_eq, keysBelow_iff,
    List.all_eq_true, Nat.ble_eq] at this
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := this
  refine ⟨h1, h2, ?_, h4, h5, h6⟩
  intro h; rw [h] at h3; exact absurd h3 (by decide)

theorem colPos_valid (j : ℕ) (hj : j < 1053) (h : colPosN j < 973) : colSelN (colPosN j) = j := by
  have := all_range_of validColPos_ok j hj
  simp only [Bool.or_eq_true, Bool.not_eq_true', Nat.beq_eq] at this
  rcases this with h' | h'
  · rw [Nat.blt_eq.mpr h] at h'; exact absurd h' (by decide)
  · exact h'

/-! ## The row tie -/

theorem tie_all (r : Fin 2184) : tieCheck r = true := by
  have h : tieCheckN r.val = true := by
    by_cases h0 : r.val < 1120
    · exact tie_range0 r.val (Nat.zero_le _) h0
    · exact tie_range1 r.val (by omega) r.isLt
  simpa [tieCheckN, Nat.mod_eq_of_lt r.isLt] using h

/-- **Tie.** The Jacobian of the reduced rows is the literal `L_p`. -/
theorem equationLinearMatrix_eq_lRow (r : Fin 2184) (a : Fin 1053) :
    equationLinearMatrix translatedRowModP r a = ((natSlot (lRow r.val) a.val : ℕ) : F) :=
  (equationLinearMatrix_eq_jacobianRow r a).trans
    (sparseLookup_eq_of_tieCheck r (tie_all r) (lRow_valid r.val r.isLt).2 (lRow_valid r.val r.isLt).1 a)

/-! ## D1 -/

theorem cast_eq_zero_of_mod {x : ℕ} (h : x % P = 0) : ((x : ℕ) : F) = 0 :=
  (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero h)

theorem lin_annihilates : StmtD1 := by
  intro s j
  have hT := d1_range s.val (Nat.zero_le _) s.isLt
  rw [d1CheckT_eq (keysBelow_iff.mpr (wRow_keys s.val s.isLt))] at hT
  have h0 := combCheck_sound (by norm_num) (by norm_num)
    (fun e he => lRow_keys e.1 (wRow_keys s.val s.isLt e he)) hT j.val
  simp only [equationLinearMatrix_eq_lRow, wLin]
  rw [sum_fin_natSlot 2184 (wRow s.val) (wRow_keys s.val s.isLt)
    (fun r => ((natSlot (lRow r) j.val : ℕ) : F)), ← cast_comb_sum]
  exact cast_eq_zero_of_mod h0

/-! ## D2 -/

theorem lin_pivot : StmtD2 := by
  intro t t'
  have h1 := all_range_of pivotOK_ok t.val t.isLt
  have h2 := all_range_of h1 t'.val t'.isLt
  have h3 : natSlot (bRow (tab 12 pivPacked t.val % 1053)) t'.val = cond (Nat.beq t.val t'.val) 1 0 :=
    Nat.eq_of_beq_eq_true h2
  show ((natSlot (bRow (tab 12 pivPacked t.val % 1053)) t'.val : ℕ) : F) = if t = t' then 1 else 0
  rw [h3]
  by_cases htt : t = t'
  · subst htt; simp [Nat.beq_refl]
  · have : Nat.beq t.val t'.val = false := by
      cases hb : Nat.beq t.val t'.val
      · rfl
      · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true hb)) htt
    simp [this, htt]

/-! ## D3 -/

theorem lin_vanish : StmtD3 := by
  refine ChainMid.cutLinearSpace_nil_le_linearAnnihilator translatedRowModP id Bsl ?_
  intro e t
  have hT := d3_range e.val (Nat.zero_le _) e.isLt
  rw [d3CheckT_eq (lRow_valid e.val e.isLt).1] at hT
  have h0 := combCheck_sound (by norm_num) (by norm_num)
    (fun x hx => bRow_keys x.1 (lRow_keys e.val e.isLt x hx)) hT t.val
  simp only [id, equationLinearMatrix_eq_lRow, Bsl]
  rw [sum_fin_natSlot 1053 (lRow e.val) (lRow_keys e.val e.isLt)
    (fun j => ((natSlot (bRow j) t.val : ℕ) : F)), ← cast_comb_sum]
  exact cast_eq_zero_of_mod h0

/-! ## D4 -/

/-- Minor rows and columns. -/
def rowSelF (a : Fin 973) : Fin 2184 := ⟨rowSelN a.val % 2184, Nat.mod_lt _ (by decide)⟩
def colSelF (b : Fin 973) : Fin 1053 := ⟨colSelN b.val % 1053, Nat.mod_lt _ (by decide)⟩

/-- The unit lower LU factor. -/
def LoM : Matrix (Fin 973) (Fin 973) F :=
  Matrix.of fun a k => ((natSlot (loRow a.val) k.val : ℕ) : F) + if a = k then 1 else 0

/-- The upper LU factor. -/
def UM : Matrix (Fin 973) (Fin 973) F := Matrix.of fun k b => ((natSlot (uRow k.val) b.val : ℕ) : F)

theorem natSlot_filter_map (l : List (ℕ × ℕ)) (q : ℕ × ℕ → Bool) (κ : ℕ → ℕ) (v : ℕ × ℕ → ℕ) (b c : ℕ)
    (h : ∀ e ∈ l, (q e = true ∧ κ e.1 = b) ↔ e.1 = c) :
    natSlot ((l.filter q).map fun e => (κ e.1, v e)) b = natSlot (l.map fun e => (e.1, v e)) c := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    have ih' := ih (fun e' he' => h e' (by simp [he']))
    have he := h e (by simp)
    rw [List.filter_cons]
    by_cases hq : q e = true
    · rw [if_pos hq, List.map_cons, List.map_cons, natSlot_cons, natSlot_cons, ih']
      congr 1
      by_cases hk : κ e.1 = b
      · rw [if_pos hk, if_pos (he.mp ⟨hq, hk⟩)]
      · rw [if_neg hk, if_neg (fun hc => hk (he.mpr hc).2)]
    · rw [if_neg hq, List.map_cons, natSlot_cons, ih', if_neg (fun hc => hq (he.mpr hc).1), Nat.zero_add]

theorem natSlot_negL (a b : ℕ) (ha : a < 973) (hb : b < 973) :
    natSlot (negL a) b = natSlot ((lRow (rowSelN a)).map fun e => (e.1, P - e.2)) (colSelN b) := by
  obtain ⟨-, -, -, hra, -, -⟩ := lu_valid a ha
  obtain ⟨-, -, -, -, hcb, hpb⟩ := lu_valid b hb
  unfold negL
  refine natSlot_filter_map _ _ colPosN (fun e => P - e.2) b (colSelN b) ?_
  intro e he
  have hj := lRow_keys _ hra e he
  constructor
  · rintro ⟨hq, hk⟩
    have hq' : colPosN e.1 < 973 := by simpa using hq
    rw [← hk, colPos_valid e.1 hj hq']
  · intro hc
    rw [hc, hpb]
    exact ⟨by simpa using hb, rfl⟩

theorem minor_eq_LoU :
    (Matrix.of fun a b => equationLinearMatrix translatedRowModP (id (rowSelF a)) (colSelF b)) = LoM * UM := by
  ext a b
  obtain ⟨hLo, hU, -, hra, -, -⟩ := lu_valid a.val a.isLt
  obtain ⟨-, -, -, -, hcb, -⟩ := lu_valid b.val b.isLt
  have hT := d4_range a.val (Nat.zero_le _) a.isLt
  rw [d4CheckT_eq (fun e he => (hLo e he).trans a.isLt)] at hT
  have h0 := d4Check_sound (fun k hk x hx => (lu_valid k hk).2.1 x hx |>.2) a.isLt
    (fun e he => (hLo e he).trans a.isLt) hT b.val
  have hz := cast_eq_zero_of_mod h0
  rw [d4List, natSlot_append, natSlot_append, natSlot_comb, natSlot_negL a.val b.val a.isLt b.isLt,
    Nat.cast_add, Nat.cast_add, cast_comb_sum,
    cast_natSlot_neg _ (lRow_valid _ hra).2] at hz
  simp only [Matrix.of_apply, id, rowSelF, colSelF, Nat.mod_eq_of_lt hra, Nat.mod_eq_of_lt hcb,
    equationLinearMatrix_eq_lRow, Matrix.mul_apply, LoM, UM, add_mul, sum_add_distrib, ite_mul, one_mul,
    zero_mul, sum_ite_eq, mem_univ, if_true]
  rw [sum_fin_natSlot 973 (loRow a.val) (fun e he => (hLo e he).trans a.isLt)
    (fun k => ((natSlot (uRow k) b.val : ℕ) : F))]
  linear_combination -hz

theorem LoM_lower : LoM.IsLowerTriangular := by
  intro a k hak
  have hak' : a < k := hak
  have hv : a.val < k.val := hak'
  obtain ⟨hLo, -⟩ := lu_valid a.val a.isLt
  simp only [LoM, Matrix.of_apply]
  rw [natSlot_eq_zero_of_not_mem _ _ (fun e he hek => by have := hLo e he; omega),
    if_neg (ne_of_lt hak')]
  simp

theorem UM_upper : UM.IsUpperTriangular := by
  intro k b hbk
  have hbk' : b < k := hbk
  have hv : b.val < k.val := hbk'
  obtain ⟨-, hU, -⟩ := lu_valid k.val k.isLt
  simp only [UM, Matrix.of_apply]
  rw [natSlot_eq_zero_of_not_mem _ _ (fun e he hek => by have := (hU e he).1; omega)]
  simp

theorem lin_dim : StmtD4 := by
  have h := ChainMid.le_finrank_cutLinearSpace_nil_of_det translatedRowModP (id : Fin 2184 → Fin 2184)
    rowSelF colSelF (by
      rw [minor_eq_LoU, Matrix.det_mul, Matrix.det_of_isLowerTriangular _ LoM_lower,
        Matrix.det_of_isUpperTriangular UM_upper]
      have hLo : ∀ a : Fin 973, LoM a a = 1 := by
        intro a
        obtain ⟨hLo, -⟩ := lu_valid a.val a.isLt
        simp only [LoM, Matrix.of_apply]
        rw [natSlot_eq_zero_of_not_mem _ _ (fun e he hek => by have := hLo e he; omega)]
        simp
      simp only [hLo, prod_const_one, one_mul]
      rw [prod_ne_zero_iff]
      intro k _
      obtain ⟨-, -, hd, -⟩ := lu_valid k.val k.isLt
      simp only [UM, Matrix.of_apply]
      intro h0
      exact hd (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp h0)))
  exact h

end A6Compact

#print axioms A6Compact.lin_annihilates
#print axioms A6Compact.lin_pivot
#print axioms A6Compact.lin_vanish
#print axioms A6Compact.lin_dim

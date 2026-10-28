module

public import A6LinEngine
public import A6LinLData
public import A6LinLUData

@[expose] public section

/-!
# Lane LIN: the Boolean certificate checks (definitions + soundness; kernel runs are in `A6LinRun*`)

* validity of the packed data (key ranges, residues, LU triangularity, `colPos ∘ colSel = id`);
* `d1Check s` : `w_s · L_p ≡ 0` (all 1053 slots), `d3Check r` : `(L_p · B)_r ≡ 0` (all 80 slots),
  `d4Check a` : row `a` of `U + Lo_strict · U − A` vanishes at every key `< 973` (minor `A = L_p[rowSel, colSel]`),
  `pivotOK` : `B (piv t) t' = δ`.
All pure `ℕ` computations (packed slots, `A6LinEngine`). First-party code.
-/

namespace A6Compact.LinCheck

open A6Compact A6Compact.LinEngine

/-- Slot width of every packed check. -/
abbrev W : ℕ := 64

/-- The prime, as a plain numeral for the checks. -/
abbrev P : ℕ := 1048573

/-! ## Validity of the data -/

def keysBelow (l : List (ℕ × ℕ)) (n : ℕ) : Bool := l.all fun e => Nat.blt e.1 n

def valsLe (l : List (ℕ × ℕ)) (m : ℕ) : Bool := l.all fun e => Nat.ble e.2 m

def validW : Bool := (List.range 48).all fun s => keysBelow (wRow s) 2184

def validB : Bool := (List.range 1053).all fun j => keysBelow (bRow j) 80

def validL : Bool := (List.range 2184).all fun r => keysBelow (lRow r) 1053 && valsLe (lRow r) P

def validLU : Bool := (List.range 973).all fun a =>
  keysBelow (loRow a) a && (uRow a).all (fun e => Nat.ble a e.1 && Nat.blt e.1 973) &&
    !Nat.beq (natSlot (uRow a) a % P) 0 && Nat.blt (rowSelN a) 2184 && Nat.blt (colSelN a) 1053 &&
    Nat.beq (colPosN (colSelN a)) a

def validColPos : Bool := (List.range 1053).all fun j =>
  !Nat.blt (colPosN j) 973 || Nat.beq (colSelN (colPosN j)) j

def pivotOK : Bool := (List.range 80).all fun t => (List.range 80).all fun t' =>
  Nat.beq (natSlot (bRow (tab 12 pivPacked t % 1053)) t') (cond (Nat.beq t t') 1 0)

/-! ## The three linear-algebra checks -/

def d1Check (s : ℕ) : Bool := combCheck P 1053 (wRow s) lRow

def d3Check (r : ℕ) : Bool := combCheck P 80 (lRow r) bRow

/-- Minor row `a`, negated, keyed by column position (non-pivot columns dropped). -/
def negL (a : ℕ) : List (ℕ × ℕ) :=
  ((lRow (rowSelN a)).filter fun e => Nat.blt (colPosN e.1) 973).map fun e => (colPosN e.1, P - e.2)

/-- The flat list whose key sums are `U a b + Σ_k Lo a k · U k b − A a b` (mod `P`). -/
def d4List (a : ℕ) : List (ℕ × ℕ) := (uRow a ++ negL a) ++ comb (loRow a) uRow

def d4Check (a : ℕ) : Bool :=
  Nat.blt (totalN (uRow a) + totalN (negL a) + ((loRow a).map fun e => e.2 * totalN (uRow e.1)).sum) (2 ^ 64) &&
    modCheck P 973 (codeN 64 (uRow a) + codeN 64 (negL a) + ((loRow a).map fun e => e.2 * codeN 64 (uRow e.1)).sum)

theorem keys_negL (a : ℕ) : ∀ x ∈ negL a, x.1 < 973 := by
  intro x hx
  simp only [negL, List.mem_map, List.mem_filter, Nat.blt_eq] at hx
  obtain ⟨e, ⟨_, he⟩, rfl⟩ := hx
  exact he

theorem d4Check_sound {a : ℕ} (hU : ∀ k < 973, ∀ x ∈ uRow k, x.1 < 973) (ha : a < 973)
    (hLo : ∀ e ∈ loRow a, e.1 < 973) (h : d4Check a = true) (b : ℕ) :
    natSlot (d4List a) b % P = 0 := by
  simp only [d4Check, Bool.and_eq_true, Nat.blt_eq] at h
  refine natSlot_mod_of_modCheck P 973 (by norm_num) (by norm_num) _ ?_ ?_ ?_ b
  · rw [d4List, totalN_append, totalN_append, totalN_comb]; exact h.1
  · intro x hx
    simp only [d4List, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact hU a ha x hx
    · exact keys_negL a x hx
    · exact keys_comb (fun e he y hy => hU e.1 (hLo e he) y hy) x hx
  · rw [d4List, codeN_append, codeN_append, codeN_comb]; exact h.2


/-! ## Kernel-run forms through memo trees (each packed row decoded once per declaration) -/

def treeL : LTree := buildT (fun r => (codeN 64 (lRow r), totalN (lRow r))) 12 0 2184
def treeB : LTree := buildT (fun j => (codeN 64 (bRow j), totalN (bRow j))) 11 0 1053
def treeU : LTree := buildT (fun k => (codeN 64 (uRow k), totalN (uRow k))) 10 0 973

noncomputable def d1CheckT (s : ℕ) : Bool := combCheckT P 1053 (wRow s) treeL

noncomputable def d3CheckT (r : ℕ) : Bool := combCheckT P 80 (lRow r) treeB

noncomputable def d4CheckT (a : ℕ) : Bool :=
  Nat.blt (totalN (uRow a) + totalN (negL a) + ((loRow a).map fun e => e.2 * (treeU.find e.1).2).sum) (2 ^ 64) &&
    modCheck P 973 (codeN 64 (uRow a) + codeN 64 (negL a) + ((loRow a).map fun e => e.2 * (treeU.find e.1).1).sum)

theorem keysBelow_iff {l : List (ℕ × ℕ)} {n : ℕ} : keysBelow l n = true ↔ ∀ e ∈ l, e.1 < n := by
  simp [keysBelow, List.all_eq_true]

theorem d1CheckT_eq {s : ℕ} (hk : keysBelow (wRow s) 2184 = true) : d1CheckT s = d1Check s :=
  combCheckT_eq fun e he =>
    find_buildT _ 12 0 2184 (by norm_num) (by norm_num) e.1 (Nat.zero_le _) (keysBelow_iff.mp hk e he)

theorem d3CheckT_eq {r : ℕ} (hk : keysBelow (lRow r) 1053 = true) : d3CheckT r = d3Check r :=
  combCheckT_eq fun e he =>
    find_buildT _ 11 0 1053 (by norm_num) (by norm_num) e.1 (Nat.zero_le _) (keysBelow_iff.mp hk e he)

theorem d4CheckT_eq {a : ℕ} (hk : ∀ e ∈ loRow a, e.1 < 973) : d4CheckT a = d4Check a := by
  have hT : ∀ e ∈ loRow a, treeU.find e.1 = (codeN 64 (uRow e.1), totalN (uRow e.1)) := fun e he =>
    find_buildT _ 10 0 973 (by norm_num) (by norm_num) e.1 (Nat.zero_le _) (hk e he)
  unfold d4CheckT d4Check
  rw [List.map_congr_left (fun e he => by rw [hT e he]),
    List.map_congr_left (l := loRow a) (f := fun e => e.2 * (treeU.find e.1).1) (fun e he => by rw [hT e he])]

/-! ## Collecting `List.all` over ranges -/

theorem all_range_of {f : ℕ → Bool} {n : ℕ} (h : (List.range n).all f = true) (i : ℕ) (hi : i < n) :
    f i = true :=
  List.all_eq_true.mp h i (List.mem_range.mpr hi)

theorem all_range'_of {f : ℕ → Bool} {a n : ℕ} (h : (List.range' a n).all f = true) (i : ℕ)
    (hi1 : a ≤ i) (hi2 : i < a + n) : f i = true :=
  List.all_eq_true.mp h i (List.mem_range'_1.mpr ⟨hi1, hi2⟩)

end A6Compact.LinCheck

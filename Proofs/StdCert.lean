module

public import StdCount

@[expose] public section

/-!
# Kernel-checkable cone-partition certificate for `cnt` 

Computable data: monomials as `List ℕ` (exponent lists), the active variable set as `List ℕ`.  A certificate is a binary
tree; a split on variable `x` carries two bitmasks selecting which generators are kept (weakening) in the kill child
(`x ∉` support) and in the colon child (`x ∣ e`, generators divided by `x`).  Leaves: `zero` (some kept generator is `1`)
or `leaf` (all generators dropped; at most 6 active variables).  `check` is a `Bool` evaluated by `decide +kernel`;
`counts` returns (#leaves with 6 active variables, #leaves with ≤ 5).
-/

open Finset

namespace StdCount

variable {n : ℕ}

/-- exponent list → exponent vector -/
def den (l : List ℕ) : Fin n → ℕ := fun i => l.getD i.val 0

/-- variable list → finset -/
def toS (V : List ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => i.val ∈ V)

def colonL : ℕ → List ℕ → List ℕ
  | _, [] => []
  | 0, a :: l => (a - 1) :: l
  | k + 1, a :: l => a :: colonL k l

def isZeroL (l : List ℕ) : Bool := l.all (· == 0)

def filterMask {α : Type} : ℕ → List α → List α
  | _, [] => []
  | b, a :: l => if b % 2 = 1 then a :: filterMask (b / 2) l else filterMask (b / 2) l

inductive Cert where
  | zero : Cert
  | leaf : Cert
  | split (x bk bc : ℕ) (k c : Cert) : Cert

def check (n : ℕ) : List (List ℕ) → List ℕ → Cert → Bool
  | L, _, .zero => L.any isZeroL
  | _, V, .leaf => decide (V.length ≤ 6)
  | L, V, .split x bk bc k c =>
      decide (x < n) && V.contains x && check n (filterMask bk L) (V.filter (· != x)) k &&
        check n (filterMask bc (L.map (colonL x))) V c

def counts : List ℕ → Cert → ℕ × ℕ
  | _, .zero => (0, 0)
  | V, .leaf => if V.length ≤ 5 then (0, 1) else (1, 0)
  | V, .split x _ _ k c => counts (V.filter (· != x)) k + counts V c

/-! ### denotation lemmas -/

theorem getD_colonL : ∀ (x : ℕ) (l : List ℕ) (i : ℕ),
    (colonL x l).getD i 0 = l.getD i 0 - (if i = x then 1 else 0)
  | _, [], i => by simp [colonL]
  | 0, a :: l, 0 => by simp [colonL]
  | 0, a :: l, i + 1 => by simp [colonL]
  | k + 1, a :: l, 0 => by simp [colonL]
  | k + 1, a :: l, i + 1 => by
    simp only [colonL, List.getD_cons_succ, getD_colonL k l i, Nat.add_right_cancel_iff]

theorem den_colonL (x : Fin n) (l : List ℕ) : den (colonL x.val l) = colon x (den l) := by
  funext i
  simp only [den, colon, getD_colonL, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]

theorem getD_of_all_zero : ∀ (l : List ℕ) (i : ℕ), l.all (· == 0) = true → l.getD i 0 = 0
  | [], i, _ => by simp
  | a :: l, 0, h => by simp_all
  | a :: l, i + 1, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.getD_cons_succ]; exact getD_of_all_zero l i h.2

theorem den_zero_of_isZeroL {l : List ℕ} (h : isZeroL l = true) : (den l : Fin n → ℕ) = 0 := by
  funext i
  exact getD_of_all_zero l i.val h

theorem mem_of_mem_filterMask {α : Type} : ∀ (b : ℕ) (l : List α) (a : α), a ∈ filterMask b l → a ∈ l
  | _, [], a, h => by simp [filterMask] at h
  | b, c :: l, a, h => by
    unfold filterMask at h
    split_ifs at h with hb
    · rcases List.mem_cons.mp h with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_of_mem_filterMask _ _ _ h)
    · exact List.mem_cons_of_mem _ (mem_of_mem_filterMask _ _ _ h)

theorem toS_filter (V : List ℕ) (x : Fin n) : (toS (V.filter (· != x.val)) : Finset (Fin n)) = (toS V).erase x := by
  ext i
  simp only [toS, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_filter, Finset.mem_erase, bne_iff_ne,
    ne_eq, decide_eq_true_eq, Fin.ext_iff]
  tauto

theorem card_toS_le (V : List ℕ) : (toS V : Finset (Fin n)).card ≤ V.length := by
  calc (toS V : Finset (Fin n)).card ≤ V.toFinset.card := by
        apply Finset.card_le_card_of_injOn (fun i => i.val)
        · intro i hi
          simp only [toS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
          simpa using hi
        · intro i _ j _ h; exact Fin.ext h
    _ ≤ V.length := List.toFinset_card_le V

/-! ### soundness -/

theorem cnt_le_succ_bound (a b m : ℕ) :
    a * (m + 5).choose 5 + b * (m + 4).choose 4 ≤ a * (m + 1 + 5).choose 5 + b * (m + 1 + 4).choose 4 := by
  apply Nat.add_le_add <;> apply Nat.mul_le_mul_left <;> apply Nat.choose_le_choose <;> omega

theorem check_sound : ∀ (c : Cert) (L : List (List ℕ)) (V : List ℕ), check n L V c = true → ∀ m,
    cnt (L.map den) (toS V : Finset (Fin n)) m ≤
      (counts V c).1 * (m + 5).choose 5 + (counts V c).2 * (m + 4).choose 4
  | .zero, L, V, h, m => by
    simp only [check, List.any_eq_true] at h
    obtain ⟨l, hl, hz⟩ := h
    rw [cnt_zero_of_mem m (List.mem_map.mpr ⟨l, hl, den_zero_of_isZeroL hz⟩)]
    exact Nat.zero_le _
  | .leaf, L, V, h, m => by
    have h' : V.length ≤ 6 := by simpa [check] using h
    have hw : cnt (L.map den) (toS V : Finset (Fin n)) m ≤ cnt [] (toS V) m :=
      cnt_mono m (by simp)
    have hc := card_toS_le (n := n) V
    simp only [counts]
    split_ifs with h5
    · have := cnt_nil_le 4 (toS V : Finset (Fin n)) (by omega) m
      simp; omega
    · have := cnt_nil_le 5 (toS V : Finset (Fin n)) (by omega) m
      simp; omega
  | .split x bk bc k c, L, V, h, m => by
    simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at h
    obtain ⟨⟨⟨hxn, hxV⟩, hk⟩, hc⟩ := h
    set X : Fin n := ⟨x, hxn⟩
    have hxS : X ∈ (toS V : Finset (Fin n)) := by simp [toS, X, hxV]
    have ihk := check_sound k _ _ hk
    have ihc := check_sound c _ _ hc
    rw [toS_filter V X] at ihk
    have wk : ∀ m, cnt (L.map den) ((toS V).erase X) m ≤ cnt ((filterMask bk L).map den) ((toS V).erase X) m :=
      fun m => cnt_mono m (by
        intro g' hg'
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg'
        exact ⟨den l, List.mem_map.mpr ⟨l, mem_of_mem_filterMask _ _ _ hl, rfl⟩, le_rfl⟩)
    have wc : ∀ m, cnt ((L.map den).map (colon X)) (toS V) m ≤
        cnt ((filterMask bc (L.map (colonL x))).map den) (toS V) m :=
      fun m => cnt_mono m (by
        intro g' hg'
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg'
        obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp (mem_of_mem_filterMask _ _ _ hl)
        refine ⟨colon X (den l0), ?_, ?_⟩
        · exact List.mem_map.mpr ⟨den l0, List.mem_map.mpr ⟨l0, hl0, rfl⟩, rfl⟩
        · rw [den_colonL X l0])
    simp only [counts, Prod.fst_add, Prod.snd_add]
    cases m with
    | zero =>
      rw [cnt_zero_eq (x := X)]
      have h1 := le_trans (wk 0) (ihk 0)
      rw [Nat.add_mul, Nat.add_mul]
      omega
    | succ m =>
      rw [cnt_split hxS m]
      have h1 := le_trans (wk (m + 1)) (ihk (m + 1))
      have h2 := le_trans (le_trans (wc m) (ihc m)) (cnt_le_succ_bound _ _ m)
      rw [Nat.add_mul, Nat.add_mul]
      omega

/-- the final statement shape used by step 7 -/
theorem bound_of_check (L : List (List ℕ)) (c : Cert) (hc : check 24 L (List.range 24) c = true)
    (h6 : (counts (List.range 24) c).1 ≤ 4) (h5 : (counts (List.range 24) c).2 ≤ 1540) (m : ℕ) :
    cnt (L.map den) (Finset.univ : Finset (Fin 24)) m ≤ 4 * (m + 5).choose 5 + 1540 * (m + 4).choose 4 := by
  have hU : (toS (List.range 24) : Finset (Fin 24)) = Finset.univ := by
    ext i; simp [toS]
  have := check_sound c L (List.range 24) hc m
  rw [hU] at this
  refine le_trans this ?_
  apply Nat.add_le_add <;> apply Nat.mul_le_mul_right <;> assumption

end StdCount

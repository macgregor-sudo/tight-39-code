module

public import A6DataLin
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Lane LIN: the packed-slot engine (generic, no data)

A sparse list `l : List (ℕ × ℕ)` of `(key, value)` pairs is packed as `codeN W l = Σ v · 2^(W·key)`. If the total
`totalN l = Σ v` is `< 2^W`, no slot overflows and slot `k` of the packed number is exactly `natSlot l k`
(`slot_codeN`). Hence "every key-sum is `≡ 0 mod p`" is checked by ONE packed Nat computation and the one-shot
`modCheck` (`p ∣ X` and every 64-bit digit of `X / p` is `< 2^44`). Combination lists `comb outer g` (`Σ_{(i,c) ∈ outer} c · (g i)`) are packed without
flattening (`codeN_comb`); memo trees (`LTree`, `buildT`) make every packed row decoded once per declaration. The `ZMod p` side: `cast_natSlot_eq_zero`, `sum_fin_natSlot`.
First-party code (no borrowed code).
-/

namespace A6Compact.LinEngine

open A6Compact Finset

/-! ## Packing -/

/-- Packed form of a sparse list: `Σ v · 2^(W·key)`. -/
def codeN (W : ℕ) (l : List (ℕ × ℕ)) : ℕ := (l.map fun e => e.2 <<< (W * e.1)).sum

/-- Total of the values. -/
def totalN (l : List (ℕ × ℕ)) : ℕ := (l.map fun e => e.2).sum

/-- Slot `k` of a packed number. -/
def slot (W X k : ℕ) : ℕ := (X >>> (W * k)) % 2 ^ W

@[simp] theorem natSlot_nil (k : ℕ) : natSlot [] k = 0 := rfl

theorem natSlot_cons (e : ℕ × ℕ) (l : List (ℕ × ℕ)) (k : ℕ) :
    natSlot (e :: l) k = (if e.1 = k then e.2 else 0) + natSlot l k := by
  unfold natSlot
  rw [List.map_cons, List.sum_cons]
  congr 1
  by_cases h : e.1 = k
  · simp [h, Nat.beq_refl]
  · have : Nat.beq e.1 k = false := by
      cases hb : Nat.beq e.1 k
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h
    simp [h, this]

theorem natSlot_append (l l' : List (ℕ × ℕ)) (k : ℕ) :
    natSlot (l ++ l') k = natSlot l k + natSlot l' k := by
  induction l with
  | nil => simp
  | cons e l ih => rw [List.cons_append, natSlot_cons, natSlot_cons, ih, Nat.add_assoc]

theorem codeN_cons (W : ℕ) (e : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    codeN W (e :: l) = e.2 * 2 ^ (W * e.1) + codeN W l := by
  unfold codeN
  rw [List.map_cons, List.sum_cons, Nat.shiftLeft_eq]

theorem codeN_append (W : ℕ) (l l' : List (ℕ × ℕ)) :
    codeN W (l ++ l') = codeN W l + codeN W l' := by
  unfold codeN; rw [List.map_append, List.sum_append]

theorem totalN_append (l l' : List (ℕ × ℕ)) : totalN (l ++ l') = totalN l + totalN l' := by
  unfold totalN; rw [List.map_append, List.sum_append]

theorem natSlot_le_totalN (l : List (ℕ × ℕ)) (k : ℕ) : natSlot l k ≤ totalN l := by
  induction l with
  | nil => simp [totalN]
  | cons e l ih =>
    rw [natSlot_cons]
    have : totalN (e :: l) = e.2 + totalN l := by simp [totalN]
    rw [this]
    split_ifs <;> omega

theorem natSlot_eq_zero_of_not_mem (l : List (ℕ × ℕ)) (k : ℕ) (h : ∀ e ∈ l, e.1 ≠ k) :
    natSlot l k = 0 := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [natSlot_cons, if_neg (h e (by simp)), ih (fun e' he' => h e' (by simp [he']))]

/-- The packed number regrouped by key. -/
theorem codeN_eq_sum_range (W : ℕ) (l : List (ℕ × ℕ)) (M : ℕ) (hM : ∀ e ∈ l, e.1 < M) :
    codeN W l = ∑ j ∈ range M, natSlot l j * 2 ^ (W * j) := by
  induction l with
  | nil => simp [codeN]
  | cons e l ih =>
    rw [codeN_cons, ih (fun e' he' => hM e' (by simp [he']))]
    simp only [natSlot_cons, add_mul, sum_add_distrib, ite_mul, zero_mul]
    rw [sum_ite_eq (range M) e.1 (fun j => e.2 * 2 ^ (W * j)), if_pos (mem_range.mpr (hM e (by simp)))]

theorem sum_digits_lt (W : ℕ) (d : ℕ → ℕ) (hd : ∀ j, d j < 2 ^ W) (n : ℕ) :
    ∑ j ∈ range n, d j * 2 ^ (W * j) < 2 ^ (W * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h1 : d n * 2 ^ (W * n) ≤ (2 ^ W - 1) * 2 ^ (W * n) :=
      Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt (hd n))
    have h2 : (2 ^ W - 1) * 2 ^ (W * n) + 2 ^ (W * n) = 2 ^ (W * (n + 1)) := by
      have hpos : 1 ≤ 2 ^ W := Nat.one_le_two_pow
      calc (2 ^ W - 1) * 2 ^ (W * n) + 2 ^ (W * n) = ((2 ^ W - 1) + 1) * 2 ^ (W * n) := by ring
        _ = 2 ^ W * 2 ^ (W * n) := by rw [Nat.sub_add_cancel hpos]
        _ = 2 ^ (W * (n + 1)) := by rw [← pow_add]; congr 1; ring
    omega

theorem sum_digits_split (W : ℕ) (d : ℕ → ℕ) (k : ℕ) :
    ∀ m, ∃ T, ∑ j ∈ range (k + 1 + m), d j * 2 ^ (W * j) =
      ∑ j ∈ range k, d j * 2 ^ (W * j) + 2 ^ (W * k) * (d k + 2 ^ W * T) := by
  intro m
  induction m with
  | zero => exact ⟨0, by rw [Nat.add_zero, sum_range_succ]; ring⟩
  | succ m ih =>
    obtain ⟨T, hT⟩ := ih
    refine ⟨T + d (k + 1 + m) * 2 ^ (W * m), ?_⟩
    rw [show k + 1 + (m + 1) = (k + 1 + m) + 1 by omega, sum_range_succ, hT]
    have : 2 ^ (W * (k + 1 + m)) = 2 ^ (W * k) * 2 ^ W * 2 ^ (W * m) := by
      rw [← pow_add, ← pow_add]; congr 1; ring
    rw [this]; ring

/-- **Digit lemma.** Slot `k` of `Σ_{j<M} d_j 2^(Wj)` is `d_k` when every digit is `< 2^W`. -/
theorem slot_sum_digits (W : ℕ) (d : ℕ → ℕ) (hd : ∀ j, d j < 2 ^ W) (M k : ℕ) (hk : k < M) :
    slot W (∑ j ∈ range M, d j * 2 ^ (W * j)) k = d k := by
  obtain ⟨T, hT⟩ := sum_digits_split W d k (M - (k + 1))
  rw [show k + 1 + (M - (k + 1)) = M by omega] at hT
  unfold slot
  rw [hT, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (sum_digits_lt W d hd k), Nat.zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (hd k)]

/-- **Slot lemma.** Without overflow, slot `k` of the packed list is the key-`k` sum. -/
theorem slot_codeN (W : ℕ) (l : List (ℕ × ℕ)) (h : totalN l < 2 ^ W) (k : ℕ) :
    slot W (codeN W l) k = natSlot l k := by
  have hd : ∀ j, natSlot l j < 2 ^ W := fun j => (natSlot_le_totalN l j).trans_lt h
  set M := k + 1 + (l.map fun e => e.1).sum with hMdef
  have hM : ∀ e ∈ l, e.1 < M := by
    intro e he
    have : e.1 ≤ (l.map fun e => e.1).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨e, he, rfl⟩)
    omega
  rw [codeN_eq_sum_range W l M hM, slot_sum_digits W _ hd M k (by omega)]

/-! ## Combination lists -/

/-- `Σ_{(i, c) ∈ outer} c · (g i)` as a flat sparse list. -/
def comb (outer : List (ℕ × ℕ)) (g : ℕ → List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  outer.flatMap fun e => (g e.1).map fun x => (x.1, e.2 * x.2)

theorem codeN_scale (W c : ℕ) (l : List (ℕ × ℕ)) :
    codeN W (l.map fun x => (x.1, c * x.2)) = c * codeN W l := by
  induction l with
  | nil => simp [codeN]
  | cons e l ih =>
    rw [List.map_cons, codeN_cons, codeN_cons, ih]; ring

theorem totalN_scale (c : ℕ) (l : List (ℕ × ℕ)) :
    totalN (l.map fun x => (x.1, c * x.2)) = c * totalN l := by
  unfold totalN; rw [List.map_map]
  induction l with
  | nil => simp
  | cons e l ih => simp only [List.map_cons, List.sum_cons, Function.comp, ih]; ring

theorem natSlot_scale (c : ℕ) (l : List (ℕ × ℕ)) (k : ℕ) :
    natSlot (l.map fun x => (x.1, c * x.2)) k = c * natSlot l k := by
  induction l with
  | nil => simp
  | cons e l ih =>
    rw [List.map_cons, natSlot_cons, natSlot_cons, ih]; split_ifs <;> ring

theorem codeN_comb (W : ℕ) (outer : List (ℕ × ℕ)) (g : ℕ → List (ℕ × ℕ)) :
    codeN W (comb outer g) = (outer.map fun e => e.2 * codeN W (g e.1)).sum := by
  induction outer with
  | nil => simp [comb, codeN]
  | cons e o ih =>
    simp only [comb, List.flatMap_cons] at ih ⊢
    rw [codeN_append, codeN_scale, ih, List.map_cons, List.sum_cons]

theorem totalN_comb (outer : List (ℕ × ℕ)) (g : ℕ → List (ℕ × ℕ)) :
    totalN (comb outer g) = (outer.map fun e => e.2 * totalN (g e.1)).sum := by
  induction outer with
  | nil => simp [comb, totalN]
  | cons e o ih =>
    simp only [comb, List.flatMap_cons] at ih ⊢
    rw [totalN_append, totalN_scale, ih, List.map_cons, List.sum_cons]

theorem natSlot_comb (outer : List (ℕ × ℕ)) (g : ℕ → List (ℕ × ℕ)) (k : ℕ) :
    natSlot (comb outer g) k = (outer.map fun e => e.2 * natSlot (g e.1) k).sum := by
  induction outer with
  | nil => simp [comb]
  | cons e o ih =>
    simp only [comb, List.flatMap_cons] at ih ⊢
    rw [natSlot_append, natSlot_scale, ih, List.map_cons, List.sum_cons]

theorem mem_comb {outer : List (ℕ × ℕ)} {g : ℕ → List (ℕ × ℕ)} {x : ℕ × ℕ} (hx : x ∈ comb outer g) :
    ∃ e ∈ outer, ∃ y ∈ g e.1, x.1 = y.1 := by
  simp only [comb, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨e, he, y, hy, rfl⟩ := hx
  exact ⟨e, he, y, hy, rfl⟩



/-! ## One-shot divisibility check of all slots (W = 64, residues `< 2^20`)

`X = Σ_{k<n} d_k 2^(64k)` with digits `d_k < 2^64`. If `p ∣ X` and the quotient `Q = X / p` has every 64-bit digit
`< 2^44` (one AND with `maskN n`), then `X = Σ (p·q_k) 2^(64k)` with digits `p·q_k < 2^64`, so `d_k = p·q_k` by
uniqueness of digits: every slot is divisible by `p`, checked by four Nat operations. -/

/-- High 20 bits of a 64-bit digit. -/
def hiMask : ℕ := (2 ^ 20 - 1) <<< 44

/-- `hiMask` in each of the `n` low 64-bit digits. -/
def maskN (n : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) 0 (fun _ m => hiMask + 2 ^ 64 * m) n

theorem maskN_succ (n : ℕ) : maskN (n + 1) = hiMask + 2 ^ 64 * maskN n := rfl

/-- Every slot `k < n` of `X` is `≡ 0 mod p`, by one division and one mask. -/
def modCheck (p n X : ℕ) : Bool := Nat.beq (X % p) 0 && Nat.beq ((X / p) &&& maskN n) 0

theorem hiMask_lt : hiMask < 2 ^ 64 := by decide

theorem lt_of_and_hiMask {q : ℕ} (hq : q < 2 ^ 64) (h : q &&& hiMask = 0) : q < 2 ^ 44 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_cases h64 : i < 64
  · have hb : hiMask.testBit i = true := by
      unfold hiMask
      rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
    have := congrArg (fun x => Nat.testBit x i) h
    simp only [Nat.testBit_and, hb, Bool.and_true, Nat.zero_testBit] at this
    exact this
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem slot_succ (X k : ℕ) : slot 64 X (k + 1) = slot 64 (X / 2 ^ 64) k := by
  unfold slot
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← pow_add]
  congr 3; ring

theorem slot_zero (X : ℕ) : slot 64 X 0 = X % 2 ^ 64 := by simp [slot]

theorem slot_lt_of_and_maskN (n : ℕ) : ∀ Q : ℕ, Q &&& maskN n = 0 → ∀ k < n, slot 64 Q k < 2 ^ 44 := by
  induction n with
  | zero => intro Q _ k hk; omega
  | succ n ih =>
    intro Q h k hk
    have hlo : (Q % 2 ^ 64) &&& hiMask = 0 := by
      have := congrArg (· % 2 ^ 64) h
      simp only [Nat.and_mod_two_pow, Nat.zero_mod] at this
      rwa [maskN_succ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hiMask_lt] at this
    have hhi : (Q / 2 ^ 64) &&& maskN n = 0 := by
      have := congrArg (· / 2 ^ 64) h
      simp only [Nat.and_div_two_pow, Nat.zero_div] at this
      rwa [maskN_succ, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hiMask_lt, Nat.zero_add] at this
    cases k with
    | zero => rw [slot_zero]; exact lt_of_and_hiMask (Nat.mod_lt _ (by positivity)) hlo
    | succ k => rw [slot_succ]; exact ih _ hhi k (by omega)

theorem eq_sum_slots (n : ℕ) : ∀ Q : ℕ, Q < 2 ^ (64 * n) → Q = ∑ k ∈ range n, slot 64 Q k * 2 ^ (64 * k) := by
  induction n with
  | zero => intro Q hQ; simp at hQ; subst hQ; simp
  | succ n ih =>
    intro Q hQ
    have hQ' : Q / 2 ^ 64 < 2 ^ (64 * n) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      convert hQ using 2
    rw [sum_range_succ', slot_zero]
    simp only [slot_succ]
    have e := ih _ hQ'
    have : ∑ k ∈ range n, slot 64 (Q / 2 ^ 64) k * 2 ^ (64 * (k + 1)) =
        2 ^ 64 * ∑ k ∈ range n, slot 64 (Q / 2 ^ 64) k * 2 ^ (64 * k) := by
      rw [mul_sum]; refine sum_congr rfl fun k _ => ?_
      rw [show 64 * (k + 1) = 64 + 64 * k by ring, pow_add]; ring
    rw [this, ← e, pow_zero, mul_one, Nat.mul_comm]
    exact (Nat.div_add_mod' Q (2 ^ 64)).symm.trans (by ring)

/-- **One-shot slot divisibility.** -/
theorem natSlot_mod_of_modCheck (p n : ℕ) (_hp0 : 0 < p) (hp : p ≤ 2 ^ 20) (l : List (ℕ × ℕ))
    (htot : totalN l < 2 ^ 64) (hkeys : ∀ e ∈ l, e.1 < n) (h : modCheck p n (codeN 64 l) = true) (k : ℕ) :
    natSlot l k % p = 0 := by
  by_cases hk : k < n
  · simp only [modCheck, Bool.and_eq_true, Nat.beq_eq] at h
    set X := codeN 64 l with hX
    have hd : ∀ j, natSlot l j < 2 ^ 64 := fun j => (natSlot_le_totalN l j).trans_lt htot
    have hXsum : X = ∑ j ∈ range n, natSlot l j * 2 ^ (64 * j) := codeN_eq_sum_range 64 l n hkeys
    have hXlt : X < 2 ^ (64 * n) := hXsum ▸ sum_digits_lt 64 _ hd n
    set Q := X / p
    have hXQ : X = p * Q := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.1)).symm
    have hQlt : Q < 2 ^ (64 * n) := lt_of_le_of_lt (Nat.div_le_self X p) hXlt
    have hq := slot_lt_of_and_maskN n Q h.2
    have hQsum := eq_sum_slots n Q hQlt
    have hX2 : X = ∑ j ∈ range n, (fun j => if j < n then p * slot 64 Q j else 0) j * 2 ^ (64 * j) := by
      rw [hXQ]
      conv_lhs => rw [hQsum]
      rw [mul_sum]
      refine sum_congr rfl fun j hj => ?_
      simp only [if_pos (mem_range.mp hj)]; ring
    have hd2 : ∀ j, (fun j => if j < n then p * slot 64 Q j else 0) j < 2 ^ 64 := by
      intro j
      simp only
      split_ifs with hj
      · calc p * slot 64 Q j < 2 ^ 20 * 2 ^ 44 :=
              Nat.mul_lt_mul_of_le_of_lt hp (hq j hj) (by positivity)
          _ = 2 ^ 64 := by norm_num
      · positivity
    have e1 := slot_sum_digits 64 _ hd n k hk
    have e2 := slot_sum_digits 64 _ hd2 n k hk
    rw [← hXsum] at e1
    rw [← hX2, e1, if_pos hk] at e2
    rw [e2, Nat.mul_mod_right]
  · rw [natSlot_eq_zero_of_not_mem l k (fun e he hek => hk (hek ▸ hkeys e he))]; rfl

theorem keys_comb {outer : List (ℕ × ℕ)} {g : ℕ → List (ℕ × ℕ)} {n : ℕ}
    (hg : ∀ e ∈ outer, ∀ x ∈ g e.1, x.1 < n) : ∀ x ∈ comb outer g, x.1 < n := by
  intro x hx
  obtain ⟨e, he, y, hy, hxy⟩ := mem_comb hx
  rw [hxy]; exact hg e he y hy

/-! ## The `ZMod p` side -/

variable {p : ℕ}

theorem cast_natSlot_eq_zero {l : List (ℕ × ℕ)} {k : ℕ} (h : natSlot l k % p = 0) :
    ((natSlot l k : ℕ) : ZMod p) = 0 := by
  exact (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero h)

theorem cast_natSlot_cons (e : ℕ × ℕ) (l : List (ℕ × ℕ)) (k : ℕ) :
    ((natSlot (e :: l) k : ℕ) : ZMod p) = (if e.1 = k then (e.2 : ZMod p) else 0) + (natSlot l k : ZMod p) := by
  rw [natSlot_cons]; push_cast; split_ifs <;> simp

/-- A sum over `Fin n` against a sparse vector with keys `< n` is a sum over its entries. -/
theorem sum_fin_natSlot (n : ℕ) (l : List (ℕ × ℕ)) (hl : ∀ e ∈ l, e.1 < n) (f : ℕ → ZMod p) :
    ∑ i : Fin n, ((natSlot l i.val : ℕ) : ZMod p) * f i.val = (l.map fun e => (e.2 : ZMod p) * f e.1).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [cast_natSlot_cons, add_mul, sum_add_distrib, ite_mul, zero_mul, List.map_cons, List.sum_cons]
    rw [ih (fun e' he' => hl e' (by simp [he']))]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun i => if e.1 = i then (e.2 : ZMod p) * f i else 0) n,
      sum_ite_eq (range n) e.1, if_pos (mem_range.mpr (hl e (by simp)))]

/-- The `ZMod p` value of a combination's key sum. -/
theorem cast_comb_sum (outer : List (ℕ × ℕ)) (g : ℕ → List (ℕ × ℕ)) (k : ℕ) :
    (((outer.map fun e => e.2 * natSlot (g e.1) k).sum : ℕ) : ZMod p) =
      (outer.map fun e => (e.2 : ZMod p) * (natSlot (g e.1) k : ZMod p)).sum := by
  induction outer with
  | nil => simp
  | cons e o ih => rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul, ih]

end A6Compact.LinEngine

namespace A6Compact.LinEngine

open Finset

/-- **Combination check** (all slots `< n`, one-shot `modCheck`), kernel-evaluated without flattening. -/
def combCheck (p n : ℕ) (outer : List (ℕ × ℕ)) (g : ℕ → List (ℕ × ℕ)) : Bool :=
  Nat.blt ((outer.map fun e => e.2 * totalN (g e.1)).sum) (2 ^ 64) &&
    modCheck p n ((outer.map fun e => e.2 * codeN 64 (g e.1)).sum)

theorem combCheck_sound {p n : ℕ} (hp0 : 0 < p) (hp : p ≤ 2 ^ 20) {outer : List (ℕ × ℕ)}
    {g : ℕ → List (ℕ × ℕ)} (hg : ∀ e ∈ outer, ∀ x ∈ g e.1, x.1 < n)
    (h : combCheck p n outer g = true) (k : ℕ) :
    (outer.map fun e => e.2 * natSlot (g e.1) k).sum % p = 0 := by
  simp only [combCheck, Bool.and_eq_true, Nat.blt_eq] at h
  rw [← natSlot_comb]
  refine natSlot_mod_of_modCheck p n hp0 hp _ (by rw [totalN_comb]; exact h.1) (keys_comb hg) ?_ k
  rw [codeN_comb]; exact h.2

end A6Compact.LinEngine

/-! ## Memo trees: one decode per declaration -/

namespace A6Compact.LinEngine

/-- A binary search tree over `ℕ` keys with `(code, total)` leaves. -/
inductive LTree : Type
  | leaf (c t : ℕ) : LTree
  | node (mid : ℕ) (l r : LTree) : LTree

/-- Lookup by descent (`j < mid` goes left). -/
noncomputable def LTree.find (T : LTree) (j : ℕ) : ℕ × ℕ :=
  LTree.rec (motive := fun _ => ℕ × ℕ) (fun c t => (c, t))
    (fun mid _ _ fl fr => cond (Nat.blt j mid) fl fr) T

/-- The tree of `f lo, …, f (lo + len - 1)` (`d` levels of fuel). -/
def buildT (f : ℕ → ℕ × ℕ) (d : ℕ) : ℕ → ℕ → LTree :=
  Nat.rec (motive := fun _ => ℕ → ℕ → LTree) (fun lo _ => LTree.leaf (f lo).1 (f lo).2)
    (fun _ ih lo len => cond (Nat.ble len 1) (LTree.leaf (f lo).1 (f lo).2)
      (LTree.node (lo + len / 2) (ih lo (len / 2)) (ih (lo + len / 2) (len - len / 2)))) d

theorem find_leaf (c t j : ℕ) : (LTree.leaf c t).find j = (c, t) := rfl

theorem find_node (mid : ℕ) (l r : LTree) (j : ℕ) :
    (LTree.node mid l r).find j = cond (Nat.blt j mid) (l.find j) (r.find j) := rfl

theorem find_buildT (f : ℕ → ℕ × ℕ) (d : ℕ) :
    ∀ lo len, 0 < len → len ≤ 2 ^ d → ∀ j, lo ≤ j → j < lo + len → (buildT f d lo len).find j = f j := by
  induction d with
  | zero =>
    intro lo len h0 hlen j h1 h2
    have : j = lo := by simp at hlen; omega
    subst this; rfl
  | succ d ih =>
    intro lo len h0 hlen j h1 h2
    show (cond (Nat.ble len 1) (LTree.leaf (f lo).1 (f lo).2)
      (LTree.node (lo + len / 2) (buildT f d lo (len / 2)) (buildT f d (lo + len / 2) (len - len / 2)))).find j = f j
    have hpow : 2 ^ (d + 1) = 2 ^ d * 2 := pow_succ 2 d
    cases hb : Nat.ble len 1
    · have hlen1 : ¬ len ≤ 1 := fun h => by rw [Nat.ble_eq_true_of_le h] at hb; exact Bool.noConfusion hb
      rw [cond_false, find_node]
      cases hj : Nat.blt j (lo + len / 2)
      · rw [cond_false]
        have : ¬ j < lo + len / 2 := fun h => by rw [Nat.blt_eq.mpr h] at hj; exact Bool.noConfusion hj
        apply ih <;> omega
      · rw [cond_true]
        have : j < lo + len / 2 := Nat.blt_eq.mp hj
        apply ih <;> omega
    · have : len ≤ 1 := Nat.le_of_ble_eq_true hb
      have : j = lo := by omega
      subst this; rfl

/-- **Combination check through a memo tree** (`T.find k = (codeN 64 (g k), totalN (g k))` on the keys). -/
noncomputable def combCheckT (p n : ℕ) (outer : List (ℕ × ℕ)) (T : LTree) : Bool :=
  Nat.blt ((outer.map fun e => e.2 * (T.find e.1).2).sum) (2 ^ 64) &&
    modCheck p n ((outer.map fun e => e.2 * (T.find e.1).1).sum)

theorem combCheckT_eq {p n : ℕ} {outer : List (ℕ × ℕ)} {T : LTree} {g : ℕ → List (ℕ × ℕ)}
    (hT : ∀ e ∈ outer, T.find e.1 = (codeN 64 (g e.1), totalN (g e.1))) :
    combCheckT p n outer T = combCheck p n outer g := by
  unfold combCheckT combCheck
  rw [List.map_congr_left (fun e he => by rw [hT e he]),
    List.map_congr_left (l := outer) (f := fun e => e.2 * (T.find e.1).1) (fun e he => by rw [hT e he])]

end A6Compact.LinEngine

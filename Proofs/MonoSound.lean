module

public import A6Field
public import LeadingMonomialBound
public import MonoKV

@[expose] public section

/-!
# MONO: soundness of the kernel checker `MonoKV.checkV` (part 1: keys and digits)
-/

open MvPolynomial

namespace MonoSound
open MonoKV

-- (A6 compact) the primality instance is `A6Compact.fact_prime_p` (A6Field.lean); none declared here.
abbrev F := ZMod P

/-- the exponent key `Σ x_i 8^i` -/
def K (x : Fin 24 →₀ ℕ) : ℕ := ∑ i, x i * 8 ^ (i : ℕ)

theorem K_add (x y : Fin 24 →₀ ℕ) : K (x + y) = K x + K y := by
  simp [K, add_mul, Finset.sum_add_distrib]

theorem K_single (i : Fin 24) : K (Finsupp.single i 1) = 8 ^ (i : ℕ) := by
  rw [K, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Finsupp.single_apply, Ne.symm hj]
  · simp

theorem K_zero : K 0 = 0 := by simp [K]

/-- list form of the key -/
def Kl : List ℕ → ℕ
  | [] => 0
  | a :: l => a + 8 * Kl l

theorem Kl_ofFn : ∀ {n : ℕ} (f : Fin n → ℕ), Kl (List.ofFn f) = ∑ i : Fin n, f i * 8 ^ (i : ℕ)
  | 0, f => by simp [Kl]
  | n + 1, f => by
    rw [List.ofFn_succ, Kl, Kl_ofFn, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring

theorem Kl_digit : ∀ (l : List ℕ), (∀ a ∈ l, a < 8) → ∀ i : ℕ, Kl l / 8 ^ i % 8 = l.getD i 0
  | [], _, i => by simp [Kl]
  | a :: l, h, 0 => by
    simp only [Kl, pow_zero, Nat.div_one, List.getD_cons_zero]
    have := h a (by simp); omega
  | a :: l, h, i + 1 => by
    have ha := h a (by simp)
    have hl : ∀ b ∈ l, b < 8 := fun b hb => h b (by simp [hb])
    rw [Kl, pow_succ', ← Nat.div_div_eq_div_mul, List.getD_cons_succ]
    have : (a + 8 * Kl l) / 8 = Kl l := by omega
    rw [this]; exact Kl_digit l hl i

/-- decoding a key into an exponent -/
noncomputable def dec (k : ℕ) : Fin 24 →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => k / 8 ^ (i : ℕ) % 8

theorem dec_K (x : Fin 24 →₀ ℕ) (hx : ∀ i, x i < 8) : dec (K x) = x := by
  ext i
  have h1 : K x = Kl (List.ofFn fun j => x j) := (Kl_ofFn _).symm
  change K x / 8 ^ (i : ℕ) % 8 = x i
  have hall : ∀ a ∈ List.ofFn (fun j => x j), a < 8 := by
    intro a ha; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha; exact hx j
  rw [h1, Kl_digit _ hall, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

theorem K_injOn {x y : Fin 24 →₀ ℕ} (hx : ∀ i, x i < 8) (hy : ∀ i, y i < 8) (h : K x = K y) : x = y := by
  rw [← dec_K x hx, ← dec_K y hy, h]

theorem lt8_of_degree {x : Fin 24 →₀ ℕ} (h : x.degree ≤ 7) (i : Fin 24) : x i < 8 := by
  have : x i ≤ x.degree := by
    rw [Finsupp.degree_eq_sum]; exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-! ## The accumulator -/

noncomputable def accDen (l : Acc) : ℕ →₀ F := (l.map fun e => Finsupp.single e.1 (e.2 : F)).sum

@[simp] theorem accDen_nil : accDen [] = 0 := rfl
@[simp] theorem accDen_cons (e : ℕ × ℕ) (l : Acc) :
    accDen (e :: l) = Finsupp.single e.1 (e.2 : F) + accDen l := by simp [accDen]

theorem insAddR_nil (k c : ℕ) : insAddR k c [] = (bif Nat.beq c 0 then [] else [(k, c)]) := rfl
theorem insAddR_cons (k c : ℕ) (g : ℕ × ℕ) (l : Acc) : insAddR k c (g :: l) =
    (bif Nat.blt k g.1 then (bif Nat.beq c 0 then g :: l else (k, c) :: g :: l)
      else bif Nat.beq k g.1 then
        (bif Nat.beq ((g.2 + c) % P) 0 then l else (k, (g.2 + c) % P) :: l)
      else g :: insAddR k c l) := rfl

theorem accDen_insAddR (k c : ℕ) : ∀ l : Acc, accDen (insAddR k c l) = Finsupp.single k (c : F) + accDen l
  | [] => by
    rw [insAddR_nil]
    cases h : Nat.beq c 0
    · simp
    · rw [Nat.beq_eq] at h; subst h; simp
  | g :: l => by
    rw [insAddR_cons]
    cases h1 : Nat.blt k g.1
    · cases h2 : Nat.beq k g.1
      · simp only [Bool.cond_false, accDen_cons, accDen_insAddR k c l]; abel
      · rw [Nat.beq_eq] at h2
        cases h3 : Nat.beq ((g.2 + c) % P) 0
        · simp only [Bool.cond_true, Bool.cond_false, accDen_cons, ZMod.natCast_mod, Nat.cast_add, h2,
            Finsupp.single_add]; abel
        · rw [Nat.beq_eq] at h3
          have h4 : ((g.2 + c : ℕ) : F) = 0 := by rw [← ZMod.natCast_mod, h3]; simp
          simp only [Bool.cond_true, accDen_cons, ← add_assoc, h2, ← Finsupp.single_add]
          rw [Nat.cast_add] at h4
          rw [add_comm (c : F), h4]; simp
    · cases h2 : Nat.beq c 0
      · simp
      · rw [Nat.beq_eq] at h2; subst h2; simp

/-- accumulator invariant: strictly increasing keys, nonzero coefficients -/
def Good (l : Acc) : Prop := l.Pairwise (fun a b => a.1 < b.1) ∧ ∀ e ∈ l, (e.2 : F) ≠ 0

theorem natCast_ne_zero {c : ℕ} (h0 : c ≠ 0) (hc : c < P) : (c : F) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; exact h0 (Nat.eq_zero_of_dvd_of_lt hd hc)

theorem mem_insAddR (k c : ℕ) : ∀ (l : Acc) (e : ℕ × ℕ), e ∈ insAddR k c l → e.1 = k ∨ e ∈ l
  | [], e, he => by
    rw [insAddR_nil] at he
    cases h : Nat.beq c 0 <;> simp_all
  | g :: l, e, he => by
    have ih := mem_insAddR k c l e
    rw [insAddR_cons] at he
    cases h1 : Nat.blt k g.1 <;> cases h2 : Nat.beq k g.1 <;> cases h3 : Nat.beq ((g.2 + c) % P) 0 <;>
      cases h4 : Nat.beq c 0 <;> simp only [h1, h2, h3, h4, Bool.cond_true, Bool.cond_false, List.mem_cons] at he ⊢ <;>
      aesop

theorem ne_of_beq_false {a b : ℕ} (h : Nat.beq a b = false) : a ≠ b := Nat.ne_of_beq_eq_false h
theorem not_lt_of_blt_false {a b : ℕ} (h : Nat.blt a b = false) : ¬ a < b := by
  intro h'; have : Nat.blt a b = true := by rw [Nat.blt_eq]; exact h'
  rw [h] at this; exact Bool.false_ne_true this
theorem lt_of_blt_true {a b : ℕ} (h : Nat.blt a b = true) : a < b := by rwa [Nat.blt_eq] at h
theorem eq_of_beq_true {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem good_insAddR (k c : ℕ) (hc : c < P) : ∀ l : Acc, Good l → Good (insAddR k c l)
  | [], _ => by
    rw [insAddR_nil]
    cases h : Nat.beq c 0
    · have h0 : c ≠ 0 := ne_of_beq_false h
      simp only [Bool.cond_false]
      exact ⟨List.pairwise_singleton _ _, by simpa using natCast_ne_zero h0 hc⟩
    · exact ⟨List.Pairwise.nil, by simp⟩
  | g :: l, ⟨hp, hnz⟩ => by
    rw [List.pairwise_cons] at hp
    obtain ⟨hgl, hpl⟩ := hp
    have hgood : Good l := ⟨hpl, fun e he => hnz e (List.mem_cons_of_mem _ he)⟩
    rw [insAddR_cons]
    cases h1 : Nat.blt k g.1
    · have hk1 : ¬ k < g.1 := not_lt_of_blt_false h1
      cases h2 : Nat.beq k g.1
      · have hk2 : k ≠ g.1 := ne_of_beq_false h2
        have hgk : g.1 < k := by omega
        obtain ⟨ihp, ihnz⟩ := good_insAddR k c hc l hgood
        refine ⟨List.pairwise_cons.mpr ⟨fun e he => ?_, ihp⟩, ?_⟩
        · rcases mem_insAddR k c l e he with h | h
          · rw [h]; exact hgk
          · exact hgl e h
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact hnz _ List.mem_cons_self
          · exact ihnz e he
      · have hk2 : k = g.1 := eq_of_beq_true h2
        cases h3 : Nat.beq ((g.2 + c) % P) 0
        · have h0 : (g.2 + c) % P ≠ 0 := ne_of_beq_false h3
          simp only [Bool.cond_true, Bool.cond_false]
          refine ⟨List.pairwise_cons.mpr ⟨fun e he => ?_, hpl⟩, ?_⟩
          · rw [hk2]; exact hgl e he
          · intro e he
            rcases List.mem_cons.mp he with rfl | he
            · exact natCast_ne_zero h0 (Nat.mod_lt _ (by norm_num))
            · exact hgood.2 e he
        · simpa using hgood
    · have hk1 : k < g.1 := lt_of_blt_true h1
      cases h4 : Nat.beq c 0
      · have h0 : c ≠ 0 := ne_of_beq_false h4
        simp only [Bool.cond_true, Bool.cond_false]
        refine ⟨List.pairwise_cons.mpr ⟨fun e he => ?_, List.pairwise_cons.mpr ⟨hgl, hpl⟩⟩, ?_⟩
        · rcases List.mem_cons.mp he with rfl | he
          · exact hk1
          · exact hk1.trans (hgl e he)
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact natCast_ne_zero h0 hc
          · exact hnz e he
      · simp only [Bool.cond_true]; exact ⟨List.pairwise_cons.mpr ⟨hgl, hpl⟩, hnz⟩

/-! ## Unfolding the recursor definitions -/

theorem addRowR_eq (a : Acc) (s km c : ℕ) :
    addRowR a s km c = (triKR s).foldl (fun a e => insAddR (km + e.1) (c * e.2 % P) a) a := by
  unfold addRowR
  generalize triKR s = L
  induction L generalizing a with
  | nil => rfl
  | cons e L ih => exact ih _

theorem accDen_foldl (km c : ℕ) : ∀ (L : List (ℕ × ℕ)) (a : Acc),
    accDen (L.foldl (fun a e => insAddR (km + e.1) (c * e.2 % P) a) a) =
      accDen a + (L.map fun e => Finsupp.single (km + e.1) ((c : F) * (e.2 : F))).sum
  | [], a => by simp
  | e :: L, a => by
    rw [List.foldl_cons, accDen_foldl km c L, accDen_insAddR, List.map_cons, List.sum_cons,
      ZMod.natCast_mod, Nat.cast_mul]
    abel

theorem good_foldl (km c : ℕ) : ∀ (L : List (ℕ × ℕ)) (a : Acc), Good a →
    Good (L.foldl (fun a e => insAddR (km + e.1) (c * e.2 % P) a) a)
  | [], a, h => h
  | e :: L, a, h => good_foldl km c L _ (good_insAddR _ _ (Nat.mod_lt _ (by norm_num)) a h)

def slots : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, N => (N % 18446744073709551616) :: slots n (N >>> 64)

theorem decodeR_eq : ∀ (n N : ℕ) (a : Acc), decodeR n N a =
    (slots n N).foldl (fun a w => addRowR a (w % 64) (mkey w) (w >>> 21)) a
  | 0, N, a => rfl
  | n + 1, N, a => decodeR_eq n (N >>> 64) _

theorem validR_eq (d : ℕ) : ∀ (n N : ℕ), validR d n N = (slots n N).all (slotOk d)
  | 0, N => rfl
  | n + 1, N => by
    show (slotOk d (N % 18446744073709551616) && validR d n (N >>> 64)) = _
    rw [validR_eq d n, slots, List.all_cons]

theorem checkV_spec {d kμ n N : ℕ} (h : checkV d kμ n N = true) :
    (∀ w ∈ slots n N, slotOk d w = true) ∧ ∃ c rest, decodeR n N [] = (kμ, c) :: rest := by
  unfold checkV at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hv, hh⟩ := h
  refine ⟨fun w hw => ?_, ?_⟩
  · rw [validR_eq, List.all_eq_true] at hv; exact hv w hw
  · revert hh
    generalize decodeR n N [] = L
    cases L with
    | nil => intro hh; exact absurd hh Bool.false_ne_true
    | cons g rest =>
      intro hh
      have : g.1 = kμ := eq_of_beq_true hh
      exact ⟨g.2, rest, by rw [← this]⟩

/-! ## Exponents, rows and trinomials as polynomials -/

noncomputable def vfin (v : ℕ) : Fin 24 →₀ ℕ := if h : v < 24 then Finsupp.single ⟨v, h⟩ 1 else 0

theorem vfin_of_lt {v : ℕ} (h : v < 24) : vfin v = Finsupp.single ⟨v, h⟩ 1 := dif_pos h

theorem vkey_eq {v : ℕ} (h : vOk v = true) : vkey v = K (vfin v) ∧ vcnt v = (vfin v).degree := by
  unfold vOk at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · have hv := lt_of_blt_true h
    have h31 : Nat.beq v 31 = false := by
      cases hb : Nat.beq v 31
      · rfl
      · have := eq_of_beq_true hb; omega
    rw [vfin_of_lt hv, K_single]
    simp [vkey, vcnt, h31, Finsupp.degree_single]
  · have hv := eq_of_beq_true h
    subst hv
    simp [vkey, vcnt, vfin, K_zero]

noncomputable def mexp (w : ℕ) : Fin 24 →₀ ℕ := vfin ((w >>> 6) % 32) + vfin ((w >>> 11) % 32) + vfin ((w >>> 16) % 32)

theorem slotOk_spec {d w : ℕ} (h : slotOk d w = true) :
    w % 64 < 48 ∧ mkey w = K (mexp w) ∧ (mexp w).degree + 2 = d := by
  unfold slotOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hs, h1⟩, h2⟩, h3⟩, hdeg⟩ := h
  obtain ⟨k1, c1⟩ := vkey_eq h1
  obtain ⟨k2, c2⟩ := vkey_eq h2
  obtain ⟨k3, c3⟩ := vkey_eq h3
  refine ⟨lt_of_blt_true hs, ?_, ?_⟩
  · simp only [mkey, mexp, K_add]; rw [← k1, ← k2, ← k3]
  · have := eq_of_beq_true hdeg
    simp only [mexp, map_add]
    rw [← c1, ← c2, ← c3]; exact this

/-- the trinomial `s` as a polynomial, read off the checker's own table -/
noncomputable def tpoly (s : ℕ) : MvPolynomial (Fin 24) F :=
  ((tri s).map fun e => monomial (vfin e.1 + vfin e.2.1) (e.2.2 : F)).sum

noncomputable def t : Fin 48 → MvPolynomial (Fin 24) F := fun s => tpoly s

theorem triKR_spec : ∀ s < 48, triKR s = (tri s).map (fun e => (8 ^ e.1 + 8 ^ e.2.1, e.2.2)) := by
  decide +kernel

theorem tri_lt : ∀ s < 48, ∀ e ∈ tri s, e.1 < 24 ∧ e.2.1 < 24 := by
  decide +kernel

/-- the polynomial denoted by one slot: `c · x^m · t_s` -/
noncomputable def rowPoly (w : ℕ) : MvPolynomial (Fin 24) F :=
  monomial (mexp w) ((w >>> 21 : ℕ) : F) * tpoly (w % 64)

/-- the univariate Kronecker image `x^e ↦ y^(K e)` -/
noncomputable def kron (p : MvPolynomial (Fin 24) F) : ℕ →₀ F := Finsupp.mapDomain K (AddMonoidAlgebra.coeff p)

theorem kron_add (p q : MvPolynomial (Fin 24) F) : kron (p + q) = kron p + kron q :=
  Finsupp.mapDomain_add

theorem kron_zero : kron 0 = 0 := Finsupp.mapDomain_zero

theorem kron_monomial (x : Fin 24 →₀ ℕ) (c : F) : kron (monomial x c) = Finsupp.single (K x) c := by
  rw [kron, ← single_eq_monomial, AddMonoidAlgebra.coeff_single, Finsupp.mapDomain_single]

theorem kron_list_sum (L : List (MvPolynomial (Fin 24) F)) : kron L.sum = (L.map kron).sum := by
  induction L with
  | nil => simp [kron_zero]
  | cons p L ih => simp [kron_add, ih]

theorem kron_rowPoly {d w : ℕ} (h : slotOk d w = true) :
    kron (rowPoly w) = ((triKR (w % 64)).map
      fun e => Finsupp.single (mkey w + e.1) (((w >>> 21 : ℕ) : F) * (e.2 : F))).sum := by
  obtain ⟨hs, hk, -⟩ := slotOk_spec h
  rw [triKR_spec _ hs, List.map_map, rowPoly, tpoly, ← List.sum_map_mul_left, kron_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  obtain ⟨ha, hb⟩ := tri_lt _ hs e he
  simp only [Function.comp, monomial_mul_monomial, kron_monomial, K_add, hk, vfin_of_lt ha, vfin_of_lt hb, K_single]

/-! ## Assembly -/

theorem decode_spec {d : ℕ} : ∀ (L : List ℕ) (a : Acc), (∀ w ∈ L, slotOk d w = true) →
    accDen (L.foldl (fun a w => addRowR a (w % 64) (mkey w) (w >>> 21)) a) =
        accDen a + kron (L.map rowPoly).sum ∧
      (Good a → Good (L.foldl (fun a w => addRowR a (w % 64) (mkey w) (w >>> 21)) a))
  | [], a, _ => by simp [kron_zero]
  | w :: L, a, hv => by
    have hw := hv w List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := decode_spec L (addRowR a (w % 64) (mkey w) (w >>> 21))
      (fun w' hw' => hv w' (List.mem_cons_of_mem _ hw'))
    refine ⟨?_, fun hg => ih2 ?_⟩
    · rw [List.foldl_cons, ih1, addRowR_eq, accDen_foldl, List.map_cons, List.sum_cons, kron_add,
        kron_rowPoly hw]
      abel
    · rw [addRowR_eq]; exact good_foldl _ _ _ _ hg

theorem accDen_ne_zero {l : Acc} {k : ℕ} (h : accDen l k ≠ 0) : ∃ e ∈ l, e.1 = k := by
  induction l with
  | nil => simp at h
  | cons e l ih =>
    rw [accDen_cons, Finsupp.add_apply] at h
    by_cases he : e.1 = k
    · exact ⟨e, List.mem_cons_self, he⟩
    · rw [Finsupp.single_eq_of_ne (Ne.symm he), zero_add] at h
      obtain ⟨e', h1, h2⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ h1, h2⟩

theorem isHomogeneous_list_sum {L : List (MvPolynomial (Fin 24) F)} {n : ℕ}
    (h : ∀ p ∈ L, p.IsHomogeneous n) : L.sum.IsHomogeneous n := by
  induction L with
  | nil => exact isHomogeneous_zero _ _ _
  | cons p L ih =>
    rw [List.sum_cons]
    exact (h p List.mem_cons_self).add (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem tpoly_isHomogeneous {s : ℕ} (hs : s < 48) : (tpoly s).IsHomogeneous 2 := by
  apply isHomogeneous_list_sum
  intro p hp
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
  obtain ⟨ha, hb⟩ := tri_lt _ hs e he
  apply isHomogeneous_monomial
  rw [map_add, vfin_of_lt ha, vfin_of_lt hb, Finsupp.degree_single, Finsupp.degree_single]

theorem rowPoly_spec {d w : ℕ} (h : slotOk d w = true) :
    (rowPoly w).IsHomogeneous d ∧ rowPoly w ∈ Mono.relSpan t d := by
  obtain ⟨hs, -, hdeg⟩ := slotOk_spec h
  constructor
  · rw [← hdeg]
    exact (isHomogeneous_monomial _ rfl).mul (tpoly_isHomogeneous hs)
  · have : rowPoly w = ((w >>> 21 : ℕ) : F) • (monomial (mexp w) 1 * t ⟨w % 64, hs⟩) := by
      rw [rowPoly, ← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨mexp w, ⟨w % 64, hs⟩, hdeg, rfl⟩)

/-- the order used: `a` is below `b` iff `key b < key a` (grevlex on monomials of degree < 8) -/
def rK (a b : Fin 24 →₀ ℕ) : Prop := K b < K a

instance : IsStrictOrder (Fin 24 →₀ ℕ) rK where
  irrefl a := lt_irrefl (K a)
  trans _ _ _ h1 h2 := lt_trans h2 h1

theorem rK_add (a b c : Fin 24 →₀ ℕ) (h : rK a b) : rK (a + c) (b + c) := by
  unfold rK at *; rw [K_add, K_add]; omega

/-- **Soundness of the kernel checker.** -/
theorem leadCert_of_checkV {d kμ n N : ℕ} (hd : d ≤ 7) (h : checkV d kμ n N = true) :
    Mono.LeadCert t rK (dec kμ) := by
  classical
  obtain ⟨hvalid, c0, rest, hdec⟩ := checkV_spec h
  set g := ((slots n N).map rowPoly).sum with hgdef
  obtain ⟨hden, hgood⟩ := decode_spec (slots n N) [] hvalid
  rw [← decodeR_eq, hdec, accDen_nil, zero_add] at hden
  have hgood' := hgood ⟨List.Pairwise.nil, by simp⟩
  rw [← decodeR_eq, hdec] at hgood'
  obtain ⟨hpw, hnz⟩ := hgood'
  rw [List.pairwise_cons] at hpw
  -- homogeneity and membership
  have hhom : g.IsHomogeneous d := isHomogeneous_list_sum fun p hp => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp; exact (rowPoly_spec (hvalid w hw)).1
  have hmem : g ∈ Mono.relSpan t d := by
    refine list_sum_mem fun p hp => ?_
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp; exact (rowPoly_spec (hvalid w hw)).2
  have hsdeg : ∀ s ∈ g.support, s.degree = d := fun s hs => by
    have := hhom (mem_support_iff.mp hs); rw [Finsupp.degree_eq_weight_one]; exact this
  have hlt8 : ∀ s ∈ g.support, ∀ i, s i < 8 := fun s hs => lt8_of_degree (by rw [hsdeg s hs]; exact hd)
  have hinj : Set.InjOn K (g.support : Set (Fin 24 →₀ ℕ)) := fun x hx y hy hxy =>
    K_injOn (hlt8 x hx) (hlt8 y hy) hxy
  have hcoeff : ∀ s ∈ g.support, kron g (K s) = g.coeff s := fun s hs =>
    Finsupp.mapDomain_apply' _ _ (by rw [finsupp_support_eq_support]) hinj hs
  -- the head
  have hrest0 : accDen rest kμ = 0 := by
    by_contra hne
    obtain ⟨e, he, hek⟩ := accDen_ne_zero hne
    have := hpw.1 e he; rw [hek] at this; exact lt_irrefl _ this
  have hk0 : kron g kμ = (c0 : F) := by
    rw [← hden, accDen_cons, Finsupp.add_apply, hrest0, add_zero, Finsupp.single_eq_same]
  have hc0 : (c0 : F) ≠ 0 := hnz _ List.mem_cons_self
  obtain ⟨μ, hμ, hKμ⟩ : ∃ μ ∈ g.support, K μ = kμ := by
    have : kμ ∈ (kron g).support := by rw [Finsupp.mem_support_iff, hk0]; exact hc0
    have := Finsupp.mapDomain_support this
    rw [finsupp_support_eq_support] at this
    exact Finset.mem_image.mp this
  have hdecμ : dec kμ = μ := by rw [← hKμ]; exact dec_K μ (hlt8 μ hμ)
  rw [hdecμ]
  refine ⟨g, by rw [hsdeg μ hμ]; exact hmem, ?_, fun s hs hne => ⟨?_, by rw [hsdeg s hs, hsdeg μ hμ]⟩⟩
  · rw [← hcoeff μ hμ, hKμ, hk0]; exact hc0
  · have hgs : kron g (K s) ≠ 0 := by rw [hcoeff s hs]; exact mem_support_iff.mp hs
    rw [← hden] at hgs
    obtain ⟨e, he, hek⟩ := accDen_ne_zero hgs
    rcases List.mem_cons.mp he with rfl | he
    · exact absurd (hinj hs hμ (by rw [hKμ]; exact hek.symm)) hne
    · unfold rK; rw [hKμ, ← hek]; exact hpw.1 e he

end MonoSound

module

public import HTPCValEng
public import HTPCValReduce

@[expose] public section

/-!
# Semantics of the value engine (first-party)

Part A: the integer phased point (adapted from `HTPCovEngineSound`, first-party team code, renamed
into `ValEng`), exact collection, exponent keys, sparse semantics of the certificate entries `nEnt`, and the
diagonal Laurent lists `dPoly`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace Option2.NativeStress.HTPhaseComplete.ValEng

open scoped BigOperators
open HTPhaseKron HTRouteKron NativeH NativeH.Equilibrium ConfigurationResidualIndices QuarticCertificate.RowBridge
open NativePolynomial.ConfigurationResiduals NativePolynomial.IntegralStructureConstants

/-! ## `ℤ[i,√3] → Q12` -/

def zq : Z4 →+* Q12 where
  toFun x := ⟨x.a, x.b, x.c, x.d⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp <;> push_cast <;> ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp] lemma zq_a (x : Z4) : (zq x).a = x.a := rfl
@[simp] lemma zq_b (x : Z4) : (zq x).b = x.b := rfl
@[simp] lemma zq_c (x : Z4) : (zq x).c = x.c := rfl
@[simp] lemma zq_d (x : Z4) : (zq x).d = x.d := rfl

lemma zq_z4I : zq z4I = Q12.I := by ext <;> simp [z4I, Q12.I]

lemma mulI_eq (x : Z4) : mulI x = z4I * x := by ext <;> simp [mulI, z4I]

lemma isZ_spec (x : Z4) (h : isZ x = true) : x = 0 := by
  simp only [isZ, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ := h
  ext <;> simp [ha, hb, hc, hd]

/-! ## The integer base point -/

def ratOK (q : ℚ) : Bool := ((bD : ℚ) * q).den == 1

def baseCheck : Bool :=
  (List.finRange 1053).all fun v =>
    let x := baseQ12 v
    ratOK x.a && ratOK x.b && ratOK x.c && ratOK x.d

theorem baseCheck_eq : baseCheck = true := by decide +kernel

lemma ratZ_cast (q : ℚ) (h : ratOK q = true) : ((ratZ q : ℤ) : ℚ) = (bD : ℚ) * q := by
  simp only [ratOK, beq_iff_eq] at h
  exact Rat.coe_int_num_of_den_eq_one h

theorem baseZ_spec (v : Fin 1053) : zq (baseZ v) = (bD : Q12) * baseQ12 v := by
  have h := baseCheck_eq
  simp only [baseCheck, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ := h v (List.mem_finRange v)
  ext <;> simp [baseZ, ratZ_cast _ ha, ratZ_cast _ hb, ratZ_cast _ hc, ratZ_cast _ hd]

lemma getD_blocks {α : Type*} (f : ℕ → α) (d : α) (n : ℕ) :
    (((List.range 39).map fun p => (List.range 27).map fun k => f (27 * p + k)).getD (n / 27) []).getD
      (n % 27) d = if n < 1053 then f n else d := by
  by_cases hn : n < 1053
  · have h1 : n / 27 < 39 := by omega
    have h2 : n % 27 < 27 := Nat.mod_lt _ (by omega)
    have e : 27 * (n / 27) + n % 27 = n := by omega
    simp [List.getD_eq_getElem?_getD, h1, h2, hn, e]
  · have h1 : ¬ n / 27 < 39 := by omega
    simp [List.getD_eq_getElem?_getD, h1, hn]

lemma bz_eq (n : ℕ) : bz n = baseZn n := by
  unfold bz baseBlocks
  rw [getD_blocks]
  split_ifs with h
  · rfl
  · simp [baseZn, h]

lemma zq_bz (n : ℕ) : zq (bz n) = (bD : Q12) * bq n := by
  rw [bz_eq]
  unfold baseZn bq
  split_ifs with h
  · exact baseZ_spec _
  · simp

lemma phiAtN_eq (m : ℕ) : phiAtN m = phiZn m := by
  unfold phiAtN phiTab
  rw [getD_blocks]
  split_ifs with h
  · rfl
  · simp [phiZn, h]

/-! ## The integer phased point -/

section Sem
variable {R : Type*} [CommRing R] (ι : Q12 →+* R) (U : Fin 4 → Rˣ)

lemma sum_filter_nonzero (l : List (Z4 × Ex)) :
    ((l.filter fun t => !isZ t.1).map fun t => ι (zq t.1) * mono U t.2).sum =
      (l.map fun t => ι (zq t.1) * mono U t.2).sum := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    by_cases h : isZ t.1 = true
    · have h0 := isZ_spec _ h
      have hf : (!isZ t.1) = false := by simp [h]
      rw [List.filter_cons, hf]
      simp only [Bool.false_eq_true, if_false, ih, List.map_cons, List.sum_cons]
      rw [h0, map_zero, map_zero, zero_mul, zero_add]
    · have h' : (!isZ t.1) = true := by simpa using h
      rw [List.filter_cons, h']
      simp only [if_true, List.map_cons, List.sum_cons, ih]

lemma two_half : (2 : Q12) * half = 1 := by decide +kernel

lemma term_eq (z : Z4) (q : Q12) (M : R) (hz : zq z = 2 * bD * q) :
    ι (zq z) * M = ι (2 * bD) * (ι q * M) := by
  rw [hz, map_mul]; ring

lemma zq_bz2 (a : ℕ) : zq ((2 : ℤ) • bz a) = 2 * bD * bq a := by
  rw [map_zsmul, zq_bz]; simp only [zsmul_eq_mul, Int.cast_ofNat]; ring

lemma half_mul (X : Q12) : 2 * (bD : Q12) * (half * X) = bD * X := by
  linear_combination ((bD : Q12) * X) * two_half

theorem phiZ_sem (v : Fin 1053) :
    ((phiZ v).map fun t => ι (zq t.1) * mono U t.2).sum = ι (2 * bD) * PhiR ι U v := by
  unfold phiZ
  rw [sum_filter_nonzero]
  unfold phiZraw PhiR phiTerms
  dsimp only
  by_cases h3 : v.val % 27 < 3
  · simp only [h3, if_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ev]
    exact term_eq ι _ _ _ (zq_bz2 _)
  · simp only [h3, if_false]
    rcases hm : planeExp ((v.val % 27 - 3) / 2) with _ | m
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ev]
      exact term_eq ι _ _ _ (zq_bz2 _)
    · simp only
      generalize 27 * (v.val / 27) + 3 + 2 * ((v.val % 27 - 3) / 2) = a
      by_cases hp : (v.val % 27 - 3) % 2 = 0
      · simp only [hp, if_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ev]
        rw [mul_add, term_eq ι _ (half * (bq a - Q12.I * bq (a + 1))),
          term_eq ι _ (half * (bq a + Q12.I * bq (a + 1)))]
        · rw [half_mul, map_add, mulI_eq, map_mul, zq_z4I, zq_bz, zq_bz]; ring
        · rw [half_mul, map_sub, mulI_eq, map_mul, zq_z4I, zq_bz, zq_bz]; ring
      · simp only [hp, if_false, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ev]
        rw [mul_add, term_eq ι _ (half * (Q12.I * (bq a - Q12.I * bq (a + 1)))),
          term_eq ι _ (-(half * (Q12.I * (bq a + Q12.I * bq (a + 1)))))]
        · rw [show (2 : Q12) * bD * -(half * (Q12.I * (bq a + Q12.I * bq (a + 1)))) =
            -(2 * bD * (half * (Q12.I * (bq a + Q12.I * bq (a + 1))))) by ring, half_mul, map_neg]
          congr 1
          rw [mulI_eq, map_mul, zq_z4I, map_add, mulI_eq, map_mul, zq_z4I, zq_bz, zq_bz]; ring
        · rw [half_mul, mulI_eq, mulI_eq, map_mul, map_sub, map_mul, zq_z4I, zq_bz, zq_bz]; ring

/-- `PhiR` on natural indices (zero outside the 1053 coordinates). -/
noncomputable def PhiN (m : ℕ) : R := if h : m < 1053 then PhiR ι U ⟨m, h⟩ else 0

theorem phiZn_sem (m : ℕ) :
    ((phiZn m).map fun t => ι (zq t.1) * mono U t.2).sum = ι (2 * bD) * PhiN ι U m := by
  unfold phiZn PhiN
  split_ifs with h
  · exact phiZ_sem ι U _
  · simp

end Sem

/-! ## Exponent box -/

lemma eDec_eKey (m : Ex) (h : eBox m = true) : eDec (eKey m) = m := by
  obtain ⟨a, b, c, d⟩ := m
  simp only [eBox, decide_eq_true_eq] at h
  simp only [eDec, eKey, Prod.mk.injEq]
  omega

lemma planeExp_box (j : ℕ) (m : Ex) (h : planeExp j = some m) :
    eBox m = true ∧ eBox (Ex.neg m) = true := by
  unfold planeExp at h
  split at h <;> first | (cases h; decide) | simp at h

lemma phiZn_box (n : ℕ) : ∀ t ∈ phiZn n, eBox t.2 = true := by
  intro t ht
  unfold phiZn at ht
  split_ifs at ht with hn
  · unfold phiZ at ht
    have ht' := (List.mem_filter.mp ht).1
    unfold phiZraw at ht'
    dsimp only at ht'
    by_cases h3 : n % 27 < 3
    · rw [if_pos h3] at ht'
      simp only [List.mem_singleton] at ht'
      rw [ht']; show eBox (0, 0, 0, 0) = true; decide
    · rw [if_neg h3] at ht'
      rcases hm : planeExp ((n % 27 - 3) / 2) with _ | m
      · rw [hm] at ht'
        simp only [List.mem_singleton] at ht'
        rw [ht']; show eBox (0, 0, 0, 0) = true; decide
      · obtain ⟨b1, b2⟩ := planeExp_box _ _ hm
        rw [hm] at ht'
        dsimp only at ht'
        have : t.2 = m ∨ t.2 = Ex.neg m := by
          by_cases hp : (n % 27 - 3) % 2 = 0
          · rw [if_pos hp] at ht'
            rcases List.mem_cons.mp ht' with h | h
            · left; rw [h]
            · right; simp only [List.mem_singleton] at h; rw [h]
          · rw [if_neg hp] at ht'
            rcases List.mem_cons.mp ht' with h | h
            · left; rw [h]
            · right; simp only [List.mem_singleton] at h; rw [h]
        rcases this with h | h <;> rw [h] <;> assumption
  · simp at ht

/-! ## Exact collection -/

section Collect
variable {R : Type*} [CommRing R] (ι : Q12 →+* R)

lemma insZ_sum (G : ℕ → R) (e : ℕ) (c : Z4) (l : List (ℕ × Z4)) :
    ((insZ e c l).map fun p => ι (zq p.2) * G p.1).sum =
      ι (zq c) * G e + (l.map fun p => ι (zq p.2) * G p.1).sum := by
  induction l with
  | nil => simp [insZ]
  | cons hd l ih =>
    obtain ⟨k, s⟩ := hd
    simp only [insZ]
    cases hb : Nat.beq e k
    · simp only [Bool.false_eq_true, if_false, List.map_cons, List.sum_cons, ih]; ring
    · have := Nat.eq_of_beq_eq_true hb
      subst this
      simp only [if_true, List.map_cons, List.sum_cons, map_add]; ring

lemma collZ_sum (G : ℕ → R) (l : List (ℕ × Z4)) :
    ((collZ l).map fun p => ι (zq p.2) * G p.1).sum = (l.map fun p => ι (zq p.2) * G p.1).sum := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    show ((insZ t.1 t.2 (collZ l)).map _).sum = _
    rw [insZ_sum, ih, List.map_cons, List.sum_cons]

lemma sum_filter_nz (G : ℕ → R) (l : List (ℕ × Z4)) :
    ((l.filter fun q => !isZ q.2).map fun p => ι (zq p.2) * G p.1).sum =
      (l.map fun p => ι (zq p.2) * G p.1).sum := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    by_cases h : isZ t.2 = true
    · have hf : (!isZ t.2) = false := by simp [h]
      rw [List.filter_cons, hf]
      simp only [Bool.false_eq_true, if_false, ih, List.map_cons, List.sum_cons]
      rw [isZ_spec _ h, map_zero, map_zero, zero_mul, zero_add]
    · have h' : (!isZ t.2) = true := by simpa using h
      rw [List.filter_cons, h']
      simp only [if_true, List.map_cons, List.sum_cons, ih]

lemma collZ_keys (l : List (ℕ × Z4)) : ∀ q ∈ collZ l, ∃ p ∈ l, p.1 = q.1 := by
  induction l with
  | nil => simp [collZ]
  | cons t l ih =>
    intro q hq
    change q ∈ insZ t.1 t.2 (collZ l) at hq
    have key : ∀ (m : List (ℕ × Z4)), (∀ q ∈ m, ∃ p ∈ l, p.1 = q.1) →
        ∀ q ∈ insZ t.1 t.2 m, ∃ p ∈ t :: l, p.1 = q.1 := by
      intro m
      induction m with
      | nil => intro _ q hq; simp [insZ] at hq; exact ⟨t, by simp, by rw [hq]⟩
      | cons hd m ihm =>
        intro hm q hq
        obtain ⟨k, s⟩ := hd
        simp only [insZ] at hq
        split_ifs at hq with hb
        · rcases List.mem_cons.mp hq with rfl | hq
          · obtain ⟨p, hp, hpk⟩ := hm (k, s) (by simp)
            exact ⟨p, List.mem_cons_of_mem _ hp, hpk⟩
          · obtain ⟨p, hp, hpk⟩ := hm q (List.mem_cons_of_mem _ hq)
            exact ⟨p, List.mem_cons_of_mem _ hp, hpk⟩
        · rcases List.mem_cons.mp hq with rfl | hq
          · obtain ⟨p, hp, hpk⟩ := hm (k, s) (by simp)
            exact ⟨p, List.mem_cons_of_mem _ hp, hpk⟩
          · exact ihm (fun q hq => hm q (List.mem_cons_of_mem _ hq)) q hq
    exact key _ ih q hq

end Collect


/-! ## Sparse semantics of the certificate entries -/

section Sparse
variable {R : Type*} [CommRing R]

lemma iAt_sum (l : List IEnt) (k : Fin 27) (F : Fin 27 → R) :
    ∑ c, ((iAt l k c : ℤ) : R) * F c = (l.map fun e => if e.1 = k then (e.2.2 : R) * F e.2.1 else 0).sum := by
  induction l with
  | nil => simp [iAt]
  | cons e l ih =>
    have : ∀ c, ((iAt (e :: l) k c : ℤ) : R) = (if e.1 = k ∧ e.2.1 = c then (e.2.2 : R) else 0) +
        ((iAt l k c : ℤ) : R) := by
      intro c; simp only [iAt, List.map_cons, List.sum_cons]; push_cast; split_ifs <;> simp
    simp only [this, add_mul, Finset.sum_add_distrib, List.map_cons, List.sum_cons]
    rw [ih]
    congr 1
    by_cases h : e.1 = k
    · simp [h, Finset.sum_ite_eq]
    · simp [h]

lemma litZ_cons (e : KLit) (l : List KLit) (k c : Fin 27) :
    litZ (e :: l) k c = if e.1 = k.val ∧ e.2.1 = c.val then e.2.2.1 else litZ l k c := by
  unfold litZ findLit
  rw [List.find?_cons]
  by_cases h : e.1 = k.val ∧ e.2.1 = c.val
  · have hb : (e.1 == k.val && e.2.1 == c.val) = true := by simp [h.1, h.2]
    rw [hb, if_pos h]; rfl
  · have hb : (e.1 == k.val && e.2.1 == c.val) = false := by
      simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]; tauto
    rw [hb, if_neg h]

lemma litZ_none (l : List KLit) (k c : Fin 27) (h : ∀ e ∈ l, ¬(e.1 = k.val ∧ e.2.1 = c.val)) :
    litZ l k c = 0 := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [litZ_cons, if_neg (h e (by simp))]
    exact ih fun e' he' => h e' (List.mem_cons_of_mem _ he')

lemma litZ_sum (l : List KLit) (hnd : (l.map fun e => (e.1, e.2.1)).Nodup) (hb : ∀ e ∈ l, e.2.1 < 27)
    (k : Fin 27) (F : ℕ → R) :
    ∑ c : Fin 27, ((litZ l k c : ℤ) : R) * F c.val =
      (l.map fun e => if e.1 = k.val then (e.2.2.1 : R) * F e.2.1 else 0).sum := by
  induction l with
  | nil => simp [litZ, findLit]
  | cons e l ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    have hl : ∀ c : Fin 27, ((litZ (e :: l) k c : ℤ) : R) =
        (if e.1 = k.val ∧ e.2.1 = c.val then (e.2.2.1 : R) else 0) + ((litZ l k c : ℤ) : R) := by
      intro c
      rw [litZ_cons]
      by_cases h : e.1 = k.val ∧ e.2.1 = c.val
      · rw [if_pos h, if_pos h]
        have : litZ l k c = 0 := litZ_none l k c fun e' he' h' => hnd.1 (by
          rw [List.mem_map]; exact ⟨e', he', by rw [h'.1, h'.2, h.1, h.2]⟩)
        rw [this]; simp
      · rw [if_neg h, if_neg h, zero_add]
    simp only [hl, add_mul, Finset.sum_add_distrib, List.map_cons, List.sum_cons]
    rw [ih hnd.2 fun e' he' => hb e' (List.mem_cons_of_mem _ he')]
    congr 1
    have he : e.2.1 < 27 := hb e (by simp)
    by_cases h : e.1 = k.val
    · rw [if_pos h]
      have : ∀ c : Fin 27, (if e.1 = k.val ∧ e.2.1 = c.val then (e.2.2.1 : R) else 0) * F c.val =
          if (⟨e.2.1, he⟩ : Fin 27) = c then (e.2.2.1 : R) * F e.2.1 else 0 := by
        intro c
        by_cases hc : e.2.1 = c.val
        · have : (⟨e.2.1, he⟩ : Fin 27) = c := Fin.ext hc
          rw [if_pos ⟨h, hc⟩, if_pos this, hc]
        · have : (⟨e.2.1, he⟩ : Fin 27) ≠ c := fun h' => hc (by rw [← h'])
          rw [if_neg (fun h' => hc h'.2), if_neg this, zero_mul]
      simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    · rw [if_neg h]
      apply Finset.sum_eq_zero; intro c _
      rw [if_neg (fun h' => h h'.1), zero_mul]

lemma gauss_map (φ : GaussianInt →+* R) (a b : ℤ) :
    φ (⟨a, b⟩ : GaussianInt) = (a : R) + (b : R) * φ ⟨0, 1⟩ := by
  have : (⟨a, b⟩ : GaussianInt) = (a : GaussianInt) + (b : GaussianInt) * ⟨0, 1⟩ := by
    ext <;> simp
  rw [this, map_add, map_mul, map_intCast, map_intCast]

lemma beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

lemma sum_filter_beq {α : Type*} (l : List (ℕ × α)) (k : ℕ) (g : ℕ × α → R) :
    ((l.filter fun e => Nat.beq e.1 k).map g).sum = (l.map fun e => if e.1 = k then g e else 0).sum := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    by_cases h : e.1 = k
    · have hb : Nat.beq e.1 k = true := by rw [h]; exact Nat.beq_refl k
      rw [List.filter_cons, if_pos hb]; simp [h, ih]
    · have hb : Nat.beq e.1 k = false := beq_false_of_ne h
      rw [List.filter_cons, hb]; simp [h, ih]

lemma ite_beq {α : Type*} (a b : ℕ) (x y : α) :
    (if Nat.beq a b = true then x else y) = if a = b then x else y := by
  by_cases h : a = b
  · rw [if_pos h, if_pos (by rw [h]; exact Nat.beq_refl b)]
  · rw [if_neg h, if_neg (by rw [beq_false_of_ne h]; simp)]

/-- **Sparse semantics of `nEnt`.** -/
theorem nEnt_sum (hK : kPosOK = true) (j : Fin 24) (k : Fin 27) (φ : GaussianInt →+* R) (F : ℕ → R) :
    (((nEnt j).filter fun e => Nat.beq e.1 k.val).map fun e => φ e.2.2 * F e.2.1).sum =
      ∑ n : Fin 27, φ (nZ j k n) * F n.val := by
  obtain ⟨pr, kp, ha, hk, h2, -, -, -⟩ := nCheck_spec j
  have hkm := kPairOf_mem hk
  have hw := (List.all_eq_true.mp kData_wellFormed.1) kp hkm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨-, -⟩, nd1⟩, nd2⟩ := hw
  have hpos := (List.all_eq_true.mp hK) kp hkm
  simp only [List.all_eq_true, List.mem_append, Bool.and_eq_true, Nat.blt_eq] at hpos
  have b1 : ∀ e ∈ kp.2.2.2.1, e.2.1 < 27 := fun e he => (hpos e (Or.inl he)).2
  have b2 : ∀ e ∈ kp.2.2.2.2, e.2.1 < 27 := fun e he => (hpos e (Or.inr he)).2
  set sA : ℤ := if pr.2.1 = j.val then 1 else -1
  set sK : ℤ := if kp.2.1 = j.val then 1 else -1
  have hz : ∀ n : Fin 27, nZ j k n = ⟨sA * iAt pr.2.2.2.1 k n - sK * litZ kp.2.2.2.1 k n,
      -iAt pr.2.2.2.2 k n + litZ kp.2.2.2.2 k n⟩ := by
    intro n
    unfold nZ aZ kZ
    rw [ha, hk]
    dsimp only
    by_cases h : pr.2.1 = j.val
    · have h' : kp.2.1 = j.val := h2 ▸ h
      simp only [sA, sK, if_pos h, if_pos h']; ext <;> simp
    · have h' : ¬ kp.2.1 = j.val := fun h' => h (h2 ▸ h')
      simp only [sA, sK, if_neg h, if_neg h']; ext <;> simp
  have e1 := iAt_sum (R := R) pr.2.2.2.1 k (fun n => F n.val)
  have e2 := iAt_sum (R := R) pr.2.2.2.2 k (fun n => F n.val)
  have e3 := litZ_sum (R := R) kp.2.2.2.1 nd1 b1 k F
  have e4 := litZ_sum (R := R) kp.2.2.2.2 nd2 b2 k F
  have expand : ∀ n : Fin 27, φ (nZ j k n) * F n.val =
      (sA : R) * (((iAt pr.2.2.2.1 k n : ℤ) : R) * F n.val) - (sK : R) * (((litZ kp.2.2.2.1 k n : ℤ) : R) * F n.val)
      - φ ⟨0, 1⟩ * (((iAt pr.2.2.2.2 k n : ℤ) : R) * F n.val) + φ ⟨0, 1⟩ * (((litZ kp.2.2.2.2 k n : ℤ) : R) * F n.val) := by
    intro n; rw [hz n, gauss_map]; push_cast; ring
  simp only [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [e1, e2, e3, e4]
  unfold nEnt
  rw [ha, hk]
  dsimp only
  rw [sum_filter_beq]
  simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def]
  have hsA : (if Nat.beq pr.2.1 j.val = true then (1 : ℤ) else -1) = sA := ite_beq _ _ _ _
  have hsK : (if Nat.beq kp.2.1 j.val = true then (1 : ℤ) else -1) = sK := ite_beq _ _ _ _
  rw [hsA, hsK]
  have L1 : (pr.2.2.2.1.map fun x => if (x.1 : ℕ) = k.val then φ ⟨sA * x.2.2, 0⟩ * F x.2.1.val else 0).sum =
      (sA : R) * (pr.2.2.2.1.map fun e => if e.1 = k then (e.2.2 : R) * F e.2.1.val else 0).sum := by
    rw [← List.sum_map_mul_left]; congr 1; apply List.map_congr_left; intro e _
    by_cases h : e.1 = k
    · rw [if_pos (congrArg Fin.val h), if_pos h, gauss_map]; push_cast; ring
    · rw [if_neg (fun h' => h (Fin.ext h')), if_neg h, mul_zero]
  have L2 : (pr.2.2.2.2.map fun x => if (x.1 : ℕ) = k.val then φ ⟨0, -x.2.2⟩ * F x.2.1.val else 0).sum =
      (-φ ⟨0, 1⟩) * (pr.2.2.2.2.map fun e => if e.1 = k then (e.2.2 : R) * F e.2.1.val else 0).sum := by
    rw [← List.sum_map_mul_left]; congr 1; apply List.map_congr_left; intro e _
    by_cases h : e.1 = k
    · rw [if_pos (congrArg Fin.val h), if_pos h, gauss_map]; push_cast; ring
    · rw [if_neg (fun h' => h (Fin.ext h')), if_neg h, mul_zero]
  have L3 : (kp.2.2.2.1.map fun x => if x.1 = k.val then φ ⟨-(sK * x.2.2.1), 0⟩ * F x.2.1 else 0).sum =
      (-(sK : R)) * (kp.2.2.2.1.map fun e => if e.1 = k.val then (e.2.2.1 : R) * F e.2.1 else 0).sum := by
    rw [← List.sum_map_mul_left]; congr 1; apply List.map_congr_left; intro e _
    by_cases h : e.1 = k.val
    · rw [if_pos h, if_pos h, gauss_map]; push_cast; ring
    · rw [if_neg h, if_neg h, mul_zero]
  have L4 : (kp.2.2.2.2.map fun x => if x.1 = k.val then φ ⟨0, x.2.2.1⟩ * F x.2.1 else 0).sum =
      φ ⟨0, 1⟩ * (kp.2.2.2.2.map fun e => if e.1 = k.val then (e.2.2.1 : R) * F e.2.1 else 0).sum := by
    rw [← List.sum_map_mul_left]; congr 1; apply List.map_congr_left; intro e _
    by_cases h : e.1 = k.val
    · rw [if_pos h, if_pos h, gauss_map]; push_cast; ring
    · rw [if_neg h, if_neg h, mul_zero]
  rw [L1, L2, L3, L4]
  ring

end Sparse

/-! ## Diagonal lists: semantics and the character -/

lemma zq_gmul (g : GaussianInt) (x : Z4) : zq (gmul g x) = gToQ12 g * zq x := by
  unfold gmul
  rw [map_add, map_zsmul, map_zsmul, mulI_eq, map_mul, zq_z4I, gToQ12_apply]
  simp only [zsmul_eq_mul]; ring

lemma rAt_eq (j : Fin 24) (c : ℕ) (hc : c < 3) : rAt j c = rRow j c := by
  simp [rAt, rTab, List.getD_eq_getElem?_getD, hc]

lemma sjAt_eq (t : ℕ) (ht : t < 4) : sjAt t = sheetJs t := by
  simp [sjAt, sjTab, List.getD_eq_getElem?_getD, ht]

lemma two_kHalf : (2 : Q12) * kHalf = 1 := by decide +kernel

section Diag
variable {R : Type*} [CommRing R] (ι : Q12 →+* R) (U : Fin 4 → Rˣ)

theorem dPoly_sem (hK : kPosOK = true) (p c : ℕ) (hc : c < 3) (j : Fin 24) :
    ((dPoly p c j).map fun q => ι (zq q.2) * mono U (eDec q.1)).sum =
      ι (2 * bD) * ∑ n : Fin 27, ι (gToQ12 (nZ j ⟨c, by omega⟩ n)) * PhiN ι U (27 * p + n.val) := by
  unfold dPoly
  rw [sum_filter_nz ι (fun k => mono U (eDec k)), collZ_sum ι (fun k => mono U (eDec k)), rAt_eq j c hc]
  unfold rRow
  rw [sum_map_flatMap]
  simp only [List.map_map, Function.comp_def]
  have inner : ∀ x : ℕ × ℕ × GaussianInt,
      ((phiAtN (27 * p + x.2.1)).map fun t => ι (zq (gmul x.2.2 t.1)) * mono U (eDec (eKey t.2))).sum =
      ι (gToQ12 x.2.2) * (ι (2 * bD) * PhiN ι U (27 * p + x.2.1)) := by
    intro x
    rw [phiAtN_eq, ← phiZn_sem ι U, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro t ht
    simp only [zq_gmul, map_mul, eDec_eKey _ (phiZn_box _ t ht)]
    ring
  simp only [inner]
  have hn := nEnt_sum hK j ⟨c, by omega⟩ (ι.comp gToQ12) (fun n => ι (2 * bD) * PhiN ι U (27 * p + n))
  simp only [RingHom.comp_apply, Fin.val_mk] at hn
  rw [hn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

lemma zsum_cons (q : ℕ × Z4) (l : List (ℕ × Z4)) : zsum (q :: l) = q.2 + zsum l := rfl

lemma sum_const_key (l : List (ℕ × Z4)) (k : ℕ) (h : ∀ q ∈ l, q.1 = k) (G : ℕ → R) :
    (l.map fun q => ι (zq q.2) * G q.1).sum = ι (zq (zsum l)) * G k := by
  induction l with
  | nil => simp [zsum]
  | cons q l ih =>
    rw [List.map_cons, List.sum_cons, h q (by simp), ih (fun q' hq' => h q' (List.mem_cons_of_mem _ hq')),
      zsum_cons, map_add, map_add]
    ring

lemma mem_winStates (p : ℕ) (hp : 3 ≤ p) : p ∈ winStates (winSt p) := by
  unfold winStates winSt
  rw [List.mem_map]
  exact ⟨(p - 3) % 9, List.mem_range.mpr (Nat.mod_lt _ (by norm_num)), by omega⟩

lemma dPoly_char (p c : ℕ) (hp : 3 ≤ p) (hc : c < 3) (j : Fin 24) (hch : charOK (winSt p) j = true) :
    ∀ q ∈ dPoly p c j, q.1 = ejKey (winSt p) j := by
  intro q hq
  have hmem : q.1 ∈ keysJ (winSt p) j := by
    unfold keysJ
    rw [List.mem_flatMap]
    refine ⟨p, mem_winStates p hp, ?_⟩
    rw [List.mem_flatMap]
    exact ⟨c, List.mem_range.mpr hc, List.mem_map.mpr ⟨q, hq, rfl⟩⟩
  have := (List.all_eq_true.mp hch) _ hmem
  exact Nat.eq_of_beq_eq_true this

/-- **Character form of one generator on a diagonal coordinate.** -/
theorem d0_sem (hK : kPosOK = true) (p c : ℕ) (hp : 3 ≤ p) (hc : c < 3) (j : Fin 24)
    (hch : charOK (winSt p) j = true) :
    ι (zq (d0 p c j)) * mono U (eDec (ejKey (winSt p) j)) =
      ι (2 * bD) * ∑ n : Fin 27, ι (gToQ12 (nZ j ⟨c, by omega⟩ n)) * PhiN ι U (27 * p + n.val) := by
  rw [← dPoly_sem ι U hK p c hc j, sum_const_key ι _ _ (dPoly_char p c hp hc j hch) (fun k => mono U (eDec k))]
  rfl

end Diag

/-! ## The base shape on window states -/

section Base
variable {R : Type*} [CommRing R] (ι : Q12 →+* R) (U : Fin 4 → Rˣ)

lemma baseOK_spec (hB : baseOK = true) (p : ℕ) (hp3 : 3 ≤ p) (hp : p < 39) :
    bq (27 * p) = bq (27 * p + 1) ∧ bq (27 * p) = bq (27 * p + 2) ∧
      ∀ m < 24, winOf (m / 2) = winSt p ∨ bq (27 * p + 3 + m) = 0 := by
  unfold baseOK at hB
  have h := (List.all_eq_true.mp hB) (p - 3) (List.mem_range.mpr (by omega))
  have e : p - 3 + 3 = p := by omega
  rw [e] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun m hm => ?_⟩
  rcases h3 m hm with h | h
  · exact Or.inl (Nat.eq_of_beq_eq_true h)
  · exact Or.inr h

lemma PhiN_diag (p n : ℕ) (hp : p < 39) (hn : n < 3) : PhiN ι U (27 * p + n) = ι (bq (27 * p + n)) := by
  unfold PhiN
  rw [dif_pos (by omega)]
  unfold PhiR phiTerms
  have e2 : (27 * p + n) % 27 = n := by omega
  simp only [e2, hn, if_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ev]
  simp [mono]

lemma PhiN_plane (p n : ℕ) (hp : p < 39) (h3 : 3 ≤ n) (hn : n < 27)
    (h0 : bq (27 * p + 3 + 2 * ((n - 3) / 2)) = 0) (h1 : bq (27 * p + 3 + 2 * ((n - 3) / 2) + 1) = 0) :
    PhiN ι U (27 * p + n) = 0 := by
  unfold PhiN
  rw [dif_pos (by omega)]
  unfold PhiR phiTerms
  have e1 : (27 * p + n) / 27 = p := by omega
  have e2 : (27 * p + n) % 27 = n := by omega
  have hv : bq (27 * p + n) = 0 := by
    rcases Nat.even_or_odd (n - 3) with ⟨r, hr⟩ | ⟨r, hr⟩
    · have : 27 * p + n = 27 * p + 3 + 2 * ((n - 3) / 2) := by omega
      rw [this]; exact h0
    · have : 27 * p + n = 27 * p + 3 + 2 * ((n - 3) / 2) + 1 := by omega
      rw [this]; exact h1
  simp only [e1, e2, show ¬ n < 3 by omega, if_false]
  rcases planeExp ((n - 3) / 2) with _ | m
  · simp [ev, hv]
  · simp only
    split_ifs <;> simp [ev, h0, h1]

/-- Generators of other sheets do not reach a window state. -/
theorem nz_contrib_zero (hB : baseOK = true) (p : ℕ) (hp3 : 3 ≤ p) (hp : p < 39) (j : Fin 24)
    (hj : sheetOf j ≠ winSt p) (k : Fin 27) :
    ∑ n : Fin 27, ι (gToQ12 (nZ j k n)) * PhiN ι U (27 * p + n.val) = 0 := by
  obtain ⟨hd1, hd2, hpl⟩ := baseOK_spec hB p hp3 hp
  have hrest : ∀ n : Fin 27, 3 ≤ n.val → ι (gToQ12 (nZ j k n)) * PhiN ι U (27 * p + n.val) = 0 := by
    intro n hn
    by_cases hz : nZ j k n = 0
    · rw [hz, map_zero, map_zero, zero_mul]
    · have hs := (nZ_support j k n hz).2
      unfold jMem at hs
      simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
      rcases hs with hs | hs
      · omega
      · have hw : winOf ((n.val - 3) / 2) ≠ winSt p := hs ▸ hj
        have a0 := hpl (2 * ((n.val - 3) / 2)) (by omega)
        have a1 := hpl (2 * ((n.val - 3) / 2) + 1) (by omega)
        have q0 : 2 * ((n.val - 3) / 2) / 2 = (n.val - 3) / 2 := by omega
        have q1 : (2 * ((n.val - 3) / 2) + 1) / 2 = (n.val - 3) / 2 := by omega
        rw [q0] at a0; rw [q1] at a1
        have z0 := a0.resolve_left hw
        have z1 := a1.resolve_left hw
        rw [PhiN_plane ι U p n.val hp hn n.isLt (by rw [← z0]) (by rw [← z1]; ring_nf), mul_zero]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hr : ∑ i : Fin 24, ι (gToQ12 (nZ j k i.succ.succ.succ)) * PhiN ι U (27 * p + i.succ.succ.succ.val) = 0 :=
    Finset.sum_eq_zero fun i _ => hrest _ (by simp)
  rw [hr, add_zero]
  have z0 : PhiN ι U (27 * p + (0 : Fin 27).val) = ι (bq (27 * p)) := by
    have := PhiN_diag ι U p 0 hp (by norm_num); simpa using this
  have z1 : PhiN ι U (27 * p + (Fin.succ (0 : Fin 26)).val) = ι (bq (27 * p)) := by
    have := PhiN_diag ι U p 1 hp (by norm_num); rw [← hd1] at this; simpa using this
  have z2 : PhiN ι U (27 * p + (Fin.succ (Fin.succ (0 : Fin 25))).val) = ι (bq (27 * p)) := by
    have := PhiN_diag ι U p 2 hp (by norm_num); rw [← hd2] at this; simpa using this
  rw [z0, z1, z2, ← add_mul, ← add_mul, ← map_add, ← map_add, ← map_add, ← map_add]
  have hu := nZ_unit j k
  have e : nZ j k 0 + (nZ j k (Fin.succ 0) + nZ j k (Fin.succ (Fin.succ 0))) = 0 := by
    rw [← add_assoc]; exact hu
  rw [e, map_zero, map_zero, zero_mul]

end Base

/-! ## `w = N(y)Φ(u)` on window states -/

section W
variable {R : Type*} [CommRing R] (ι : Q12 →+* R) (U : Fin 4 → Rˣ) (y : Fin 24 → R)

/-- The anchor-form displacement `w = N(y) Φ(u)`. -/
noncomputable def Wv : Fin 1053 → R := opApply (nOp ι y) (PhiR ι U)

lemma PhiR_vi (p : Fin 39) (n : Fin 27) : PhiR ι U (variableIndex p n) = PhiN ι U (27 * p.val + n.val) := by
  unfold PhiN
  have h : 27 * p.val + n.val < 1053 := by omega
  rw [dif_pos h]
  congr 1

lemma Wv_vi (p : Fin 39) (k : Fin 27) :
    Wv ι U y (variableIndex p k) =
      ∑ j, y j * ι kHalf * ∑ n : Fin 27, ι (gToQ12 (nZ j k n)) * PhiN ι U (27 * p.val + n.val) := by
  unfold Wv
  rw [opApply_vi]
  unfold mv sv nOp
  simp only [PhiR_vi, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n _ => ?_
  ring

theorem Wv_dead (hB : baseOK = true) (p : Fin 39) (hp3 : 3 ≤ p.val) (k : Fin 27)
    (hk : jMem (winSt p.val) k = false) : Wv ι U y (variableIndex p k) = 0 := by
  rw [Wv_vi]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hs : sheetOf j = winSt p.val
  · have : ∀ n, nZ j k n = 0 := by
      intro n; by_contra hz
      have := (nZ_support j k n hz).1
      rw [hs, hk] at this; exact Bool.false_ne_true this
    simp [this]
  · rw [nz_contrib_zero ι U hB p.val hp3 p.isLt j hs k, mul_zero]

lemma four_kHalf : ι (4 * bD) * ι kHalf = ι (2 * bD) := by
  rw [← map_mul]; congr 1; linear_combination (2 * (bD : Q12)) * two_kHalf

lemma list_sum_filter {α : Type*} (l : List α) (P : α → Bool) (f : α → R)
    (h : ∀ a ∈ l, P a = false → f a = 0) : (l.map f).sum = ((l.filter P).map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    cases hP : P a
    · rw [List.filter_cons, hP]; simp only [Bool.false_eq_true, if_false, List.map_cons, List.sum_cons]
      rw [h a (by simp) hP, zero_add, ih']
    · rw [List.filter_cons, hP]; simp only [if_true, List.map_cons, List.sum_cons, ih']

lemma mem_sheetJs (t : ℕ) (j : Fin 24) : j ∈ sheetJs t ↔ sheetOf j = t := by
  unfold sheetJs
  simp only [List.mem_filter, List.mem_finRange, true_and]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => by rw [h]; exact Nat.beq_refl t⟩

/-- **Character form of `w` on a diagonal coordinate of a window state.** -/
theorem Wv_diag (hB : baseOK = true) (hK : kPosOK = true) (p : Fin 39) (hp3 : 3 ≤ p.val) (c : ℕ) (hc : c < 3)
    (hch : ∀ j ∈ sheetJs (winSt p.val), charOK (winSt p.val) j = true) :
    ι (4 * bD) * Wv ι U y (variableIndex p ⟨c, by omega⟩) =
      ((sheetJs (winSt p.val)).map fun j => y j * ι (zq (d0 p.val c j)) * mono U (eJ j)).sum := by
  rw [Wv_vi, Finset.mul_sum, Fin.sum_univ_def]
  rw [list_sum_filter _ (fun j => Nat.beq (sheetOf j) (winSt p.val))]
  · change (((List.finRange 24).filter fun j => Nat.beq (sheetOf j) (winSt p.val)).map _).sum = _
    rw [show ((List.finRange 24).filter fun j => Nat.beq (sheetOf j) (winSt p.val)) = sheetJs (winSt p.val) from rfl]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j hj
    have hs := (mem_sheetJs _ j).mp hj
    have hd := d0_sem ι U hK p.val c hp3 hc j (hch j hj)
    have he : eJ j = eDec (ejKey (winSt p.val) j) := by unfold eJ; rw [hs]
    rw [he]
    have := four_kHalf ι
    linear_combination (y j * ∑ n : Fin 27, ι (gToQ12 (nZ j ⟨c, by omega⟩ n)) *
      PhiN ι U (27 * p.val + n.val)) * this - y j * hd
  · intro j _ hj
    have hne : sheetOf j ≠ winSt p.val := fun h => by rw [h, Nat.beq_refl] at hj; exact absurd hj (by decide)
    rw [nz_contrib_zero ι U hB p.val hp3 p.isLt j hne, mul_zero, mul_zero]

end W

/-! ## Row reduction (`pairRow_reduction`) -/

section Rows
variable {R : Type*} [CommRing R]

lemma qpv_label (h : R) (q : FLabel) (x : Fin 1053 → R) :
    quadraticPartValue h (fNumber q) x = quadraticValue (quadraticScale h (labelShape q)) (labelShape q).quadratic x := by
  simp only [quadraticPartValue, quadTable, rowShape, Equiv.symm_apply_apply]

/-- The three-diagonal pairing of a pair row (zero for other rows). -/
def pairDiag (pe : PEntry) (x : Fin 1053 → R) : R :=
  match pe.e.label with
  | .inr (.inr (.inr ij)) => ∑ c : Fin 3, x (variableIndex ij.val.1 ⟨c.val, by omega⟩) *
      x (variableIndex ij.val.2 ⟨c.val, by omega⟩)
  | _ => 0

lemma winSt_lt (p : Fin 39) : winSt p.val < 4 := by unfold winSt; omega

lemma closure_spec (hC : closureOK = true) (t : ℕ) (ht : t < 4) (k : Fin 27) (hk : jMem t k = false) :
    ∀ e ∈ productTable k, jMem t e.1 = false ∨ jMem t e.2.1 = false := by
  intro e he
  have h1 := (List.all_eq_true.mp hC) t (List.mem_range.mpr ht)
  have h2 := (List.all_eq_true.mp h1) k (List.mem_finRange k)
  rw [hk, Bool.false_or, List.all_eq_true] at h2
  have h3 := h2 e he
  cases ha : jMem t e.1 <;> cases hb : jMem t e.2.1 <;> simp_all

lemma jMem_plane (s : ℕ) (k : Fin 27) (hk : 3 ≤ k.val) (h : jMem s k = true) : winOf ((k.val - 3) / 2) = s := by
  unfold jMem at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with h | h
  · omega
  · exact h

variable (ι : Q12 →+* R) (U : Fin 4 → Rˣ) (y : Fin 24 → R)

/-- **Row reduction.** For entries satisfying `entryOK`, the quadratic part at `w = N(y)Φ(u)` vanishes on
idempotency (closure of `J_t`), trace and frame rows, and is the three-diagonal pairing on pair rows. -/
theorem pairRow_reduction (hB : baseOK = true) (hC : closureOK = true) (pe : PEntry) (hok : entryOK pe = true) :
    quadraticPartValue (ι half) (fNumber pe.e.label) (Wv ι U y) = pairDiag pe (Wv ι U y) := by
  unfold entryOK at hok
  unfold pairDiag
  rw [qpv_label]
  rcases hl : pe.e.label with ⟨i, k⟩ | i | ⟨f, k⟩ | ij
  · rw [hl] at hok
    simp only [Bool.and_eq_true, Nat.ble_eq, Bool.not_eq_true'] at hok
    dsimp only
    rw [idem_quad]
    unfold tq
    rw [List.sum_eq_zero, mul_zero]
    intro z hz
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz
    rcases closure_spec hC _ (winSt_lt i) k hok.2 e he with h | h
    · simp only [sv, Wv_dead ι U y hB i hok.1 _ h]; ring
    · simp only [sv, Wv_dead ι U y hB i hok.1 _ h]; ring
  · dsimp only; exact trace_quad _ _ _
  · dsimp only; exact frame_quad _ _ _ _
  · rw [hl] at hok
    simp only [Bool.and_eq_true, Nat.ble_eq, Bool.not_eq_true'] at hok
    obtain ⟨⟨hp, hq⟩, hne⟩ := hok
    have hne' : winSt ij.val.1.val ≠ winSt ij.val.2.val := fun h => by
      rw [h, Nat.beq_refl] at hne; exact absurd hne (by decide)
    dsimp only
    rw [pair_quad]
    unfold wpair
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    have hrest : ∀ k : Fin 27, 3 ≤ k.val →
        (coordinateTraceWeight k : R) * sv (Wv ι U y) ij.val.1 k * sv (Wv ι U y) ij.val.2 k = 0 := by
      intro k hk
      cases h1 : jMem (winSt ij.val.1.val) k
      · simp only [sv, Wv_dead ι U y hB _ hp k h1]; ring
      · cases h2 : jMem (winSt ij.val.2.val) k
        · simp only [sv, Wv_dead ι U y hB _ hq k h2]; ring
        · exact absurd ((jMem_plane _ k hk h1).symm.trans (jMem_plane _ k hk h2)) hne'
    rw [Finset.sum_eq_zero fun i _ => hrest _ (by simp), add_zero, Fin.sum_univ_three]
    simp only [sv, coordinateTraceWeight]
    norm_num
    ring

end Rows

/-! ## Generic list/finset bookkeeping -/

section Book
variable {R : Type*} [AddCommMonoid R]

lemma sum_filter_ite' {α : Type*} (l : List α) (P : α → Bool) (f : α → R) :
    ((l.filter P).map f).sum = (l.map fun a => if P a then f a else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : P a <;> simp [List.filter_cons, h, ih]

lemma list_finset_comm {α β : Type*} [Fintype β] (L : List α) (f : α → β → R) :
    (L.map fun a => ∑ x, f a x).sum = ∑ x, (L.map fun a => f a x).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

lemma ite_key_sum (K : List ℕ) (hK : K.Nodup) (k : ℕ) (v : R) :
    (K.map fun b => if Nat.beq k b = true then v else 0).sum = if k ∈ K then v else 0 := by
  induction K with
  | nil => simp
  | cons b K ih =>
    rw [List.nodup_cons] at hK
    rw [List.map_cons, List.sum_cons, ih hK.2]
    by_cases hb : k = b
    · subst hb
      rw [if_pos (Nat.beq_refl k), if_neg hK.1, if_pos (List.mem_cons_self), add_zero]
    · rw [if_neg (by rw [beq_false_of_ne hb]; simp), zero_add]
      by_cases hk : k ∈ K
      · rw [if_pos hk, if_pos (List.mem_cons_of_mem _ hk)]
      · rw [if_neg hk, if_neg (by simp [hb, hk])]

lemma map_add_sum {α : Type*} (K : List α) (f g : α → R) :
    (K.map fun b => f b + g b).sum = (K.map f).sum + (K.map g).sum := by
  induction K with
  | nil => simp
  | cons b K ih => simp only [List.map_cons, List.sum_cons, ih]; abel

lemma partition_sum {α : Type*} (L : List α) (key : α → ℕ) (K : List ℕ) (hK : K.Nodup) (f : α → R)
    (h : ∀ a ∈ L, key a ∉ K → f a = 0) :
    (L.map f).sum = (K.map fun b => ((L.filter fun a => Nat.beq (key a) b).map f).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ih fun b hb => h b (List.mem_cons_of_mem _ hb)]
    have e : ∀ b, ((((a :: L).filter fun x => Nat.beq (key x) b)).map f).sum =
        (if Nat.beq (key a) b = true then f a else 0) + ((L.filter fun x => Nat.beq (key x) b).map f).sum := by
      intro b; rw [List.filter_cons]; split_ifs <;> simp
    simp only [e]
    rw [map_add_sum]
    rw [ite_key_sum K hK]
    by_cases hk : key a ∈ K
    · rw [if_pos hk]
    · rw [if_neg hk, h a (by simp) hk, zero_add]

end Book

/-! ## Packed block integers: expansion, digits and bounds -/

def dd (p c t : ℕ) (j : Fin 24) : Z4 := if sheetOf j = t then d0 p c j else 0

lemma Ypow_add (a b : ℕ) : Ypow a * Ypow b = Ypow (a + b) := by
  unfold Ypow
  rw [← Int.cast_mul]
  congr 1
  simp only [Nat.pow_eq, Int.ofNat_eq_coe, Nat.cast_pow, Nat.cast_ofNat, ← pow_add, mul_add]

lemma winSt_le (p : ℕ) (hp : p < 39) : winSt p < 4 := by unfold winSt; omega

lemma wd_eq (p c sh : ℕ) (hp : p < 39) :
    wd p c sh = ∑ j : Fin 24, dd p c (winSt p) j * Ypow (sh * j.val) := by
  unfold wd
  rw [sjAt_eq _ (winSt_le p hp)]
  unfold sheetJs
  rw [sum_filter_ite', Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro j _
  unfold dd
  rw [ite_beq]
  split_ifs <;> simp

/-- Digit `(j, l)` of a pair entry's packed integer. -/
def bC (K t t' : ℕ) (pe : PEntry) (j l : Fin 24) : Z4 :=
  match pe.e.label with
  | .inr (.inr (.inr ij)) => wz K pe.e.coefficient *
      ∑ c : Fin 3, dd ij.val.1.val c.val t j * dd ij.val.2.val c.val t' l
  | _ => 0

lemma bInt_eq (K t t' : ℕ) (pe : PEntry) (ij : Pair 39) (hl : pe.e.label = .inr (.inr (.inr ij)))
    (ht : winSt ij.val.1.val = t) (ht' : winSt ij.val.2.val = t') :
    bInt K pe = ∑ j : Fin 24, ∑ l : Fin 24, bC K t t' pe j l * Ypow (j.val + 24 * l.val) := by
  unfold bInt bC
  rw [hl]
  dsimp only
  simp only [wd_eq _ _ _ ij.val.1.isLt, wd_eq _ _ _ ij.val.2.isLt, ht, ht']
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [← Ypow_add, one_mul]
  ring

/-- Digit `(j, l)` contribution of Book term `m` to the packed target. -/
def tTerm (sc : ℤ) (i : Fin 4) (a : Fin 3) (t t' : ℕ) (m : Fin 3) (j l : Fin 24) : Z4 :=
  let e := BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m
  if Nat.beq (sheetOf e.1) t && Nat.beq (sheetOf e.2.1) t' then
    (if e.1 = j ∧ e.2.1 = l then ((sc * e.2.2 : ℤ) : Z4) else 0)
  else if Nat.beq (sheetOf e.1) t' && Nat.beq (sheetOf e.2.1) t then
    (if e.2.1 = j ∧ e.1 = l then ((sc * e.2.2 : ℤ) : Z4) else 0)
  else 0

lemma pick2 (v : Z4) (j0 l0 : Fin 24) :
    ∑ j : Fin 24, ∑ l : Fin 24, (if j0 = j ∧ l0 = l then v else 0) * Ypow (j.val + 24 * l.val) =
      v * Ypow (j0.val + 24 * l0.val) := by
  simp only [ite_and]
  rw [Finset.sum_eq_single j0]
  · rw [Finset.sum_eq_single l0]
    · simp
    · intro l _ hl; rw [if_pos rfl, if_neg (Ne.symm hl), zero_mul]
    · simp
  · intro j _ hj
    apply Finset.sum_eq_zero; intro l _; rw [if_neg (Ne.symm hj), zero_mul]
  · simp

lemma tInt_eq (sc : ℤ) (i : Fin 4) (a : Fin 3) (t t' : ℕ) :
    tInt sc i a t t' = ∑ j : Fin 24, ∑ l : Fin 24, (∑ m : Fin 3, tTerm sc i a t t' m j l) * Ypow (j.val + 24 * l.val) := by
  simp only [Finset.sum_mul]
  rw [show (∑ j : Fin 24, ∑ l : Fin 24, ∑ m : Fin 3, tTerm sc i a t t' m j l * Ypow (j.val + 24 * l.val)) =
      ∑ m : Fin 3, ∑ j : Fin 24, ∑ l : Fin 24, tTerm sc i a t t' m j l * Ypow (j.val + 24 * l.val) from
    (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans Finset.sum_comm]
  unfold tInt
  rw [← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold tTerm
  dsimp only
  split_ifs with h1 h2
  · exact (pick2 _ _ _).symm
  · exact (pick2 _ _ _).symm
  · simp

def compA : Z4 →+ ℤ := { toFun := fun x => x.a, map_zero' := rfl, map_add' := fun _ _ => rfl }
def compB : Z4 →+ ℤ := { toFun := fun x => x.b, map_zero' := rfl, map_add' := fun _ _ => rfl }
def compC : Z4 →+ ℤ := { toFun := fun x => x.c, map_zero' := rfl, map_add' := fun _ _ => rfl }
def compD : Z4 →+ ℤ := { toFun := fun x => x.d, map_zero' := rfl, map_add' := fun _ _ => rfl }

lemma Ypow_int (n : ℕ) : Ypow n = (((2 : ℤ) ^ 128) ^ n : ℤ) := by
  unfold Ypow
  congr 1
  simp only [Nat.pow_eq, Int.ofNat_eq_coe, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]

lemma digits_int (c : Fin 24 → Fin 24 → ℤ) (hb : ∀ j l, |c j l| < 2 ^ 128)
    (h : ∑ j : Fin 24, ∑ l : Fin 24, c j l * ((2 : ℤ) ^ 128) ^ (j.val + 24 * l.val) = 0) :
    ∀ j l, c j l = 0 := by
  let f : Fin 24 × Fin 24 → ℕ := fun x => x.1.val + 24 * x.2.val
  have finj : Set.InjOn f (Finset.univ : Finset (Fin 24 × Fin 24)) := by
    intro x _ y _ hxy
    simp only [f] at hxy
    have h1 : x.1.val = y.1.val := by omega
    have h2 : x.2.val = y.2.val := by omega
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  let g : ℕ → ℤ := fun e => if h : e % 24 < 24 ∧ e / 24 < 24 then c ⟨e % 24, h.1⟩ ⟨e / 24, h.2⟩ else 0
  have hg : ∀ x : Fin 24 × Fin 24, g (f x) = c x.1 x.2 := by
    intro x
    have h1 : (x.1.val + 24 * x.2.val) % 24 = x.1.val := by omega
    have h2 : (x.1.val + 24 * x.2.val) / 24 = x.2.val := by omega
    simp only [g, f]
    rw [dif_pos (by omega)]
    congr 1 <;> apply Fin.ext <;> simp [h1, h2]
  have hsum : ∑ e ∈ Finset.univ.image f, g e * ((2 : ℤ) ^ 128) ^ e = 0 := by
    rw [Finset.sum_image finj, Fintype.sum_prod_type]
    simp only [hg]
    exact h
  have hbd : ∀ e ∈ Finset.univ.image f, |g e| < 2 ^ 128 := by
    intro e he
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he
    rw [hg]; exact hb _ _
  have hz := HTKron.digits_eq_zero (2 ^ 128) (by norm_num) _ g hbd hsum
  intro j l
  have := hz (f (j, l)) (Finset.mem_image_of_mem f (Finset.mem_univ _))
  rwa [hg] at this

lemma abs_le_n1 (x : Z4) : |x.a| < 2 ^ 128 ∧ |x.b| < 2 ^ 128 ∧ |x.c| < 2 ^ 128 ∧ |x.d| < 2 ^ 128 ∨ 2 ^ 128 ≤ n1 x := by
  by_cases h : n1 x < 2 ^ 128
  · left
    have hc := n1_cast x
    have hh : (n1 x : ℤ) < 2 ^ 128 := by exact_mod_cast h
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      linarith [abs_nonneg x.a, abs_nonneg x.b, abs_nonneg x.c, abs_nonneg x.d]
  · right; omega

lemma digits_Z4 (D : Fin 24 → Fin 24 → Z4) (hb : ∀ j l, n1 (D j l) < 2 ^ 128)
    (h : ∑ j : Fin 24, ∑ l : Fin 24, D j l * Ypow (j.val + 24 * l.val) = 0) : ∀ j l, D j l = 0 := by
  have comp : ∀ (π : Z4 →+ ℤ), (∀ x n, π (x * ((n : ℤ) : Z4)) = π x * n) →
      ∑ j : Fin 24, ∑ l : Fin 24, π (D j l) * ((2 : ℤ) ^ 128) ^ (j.val + 24 * l.val) = 0 := by
    intro π hπ
    have := congrArg π h
    simp only [map_sum, map_zero, Ypow_int, hπ] at this
    exact this
  have hA := digits_int (fun j l => (D j l).a) (fun j l => by
    rcases abs_le_n1 (D j l) with h' | h'
    · exact h'.1
    · exact absurd (hb j l) (by omega)) (comp compA (fun x n => by show (x * ((n : ℤ) : Z4)).a = x.a * n; simp))
  have hB := digits_int (fun j l => (D j l).b) (fun j l => by
    rcases abs_le_n1 (D j l) with h' | h'
    · exact h'.2.1
    · exact absurd (hb j l) (by omega)) (comp compB (fun x n => by show (x * ((n : ℤ) : Z4)).b = x.b * n; simp))
  have hC := digits_int (fun j l => (D j l).c) (fun j l => by
    rcases abs_le_n1 (D j l) with h' | h'
    · exact h'.2.2.1
    · exact absurd (hb j l) (by omega)) (comp compC (fun x n => by show (x * ((n : ℤ) : Z4)).c = x.c * n; simp))
  have hD := digits_int (fun j l => (D j l).d) (fun j l => by
    rcases abs_le_n1 (D j l) with h' | h'
    · exact h'.2.2.2
    · exact absurd (hb j l) (by omega)) (comp compD (fun x n => by show (x * ((n : ℤ) : Z4)).d = x.d * n; simp))
  intro j l
  ext
  · exact hA j l
  · exact hB j l
  · exact hC j l
  · exact hD j l

/-! ## Bounds -/

lemma le_sum_of_mem_nat {α : Type*} (l : List α) (f : α → ℕ) (a : α) (h : a ∈ l) : f a ≤ (l.map f).sum := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

lemma n1_dd_le (p c : ℕ) (hp : p < 39) (j : Fin 24) : n1 (dd p c (winSt p) j) ≤ rowMass p c := by
  unfold dd rowMass
  split_ifs with h
  · rw [sjAt_eq _ (winSt_le p hp)]
    exact le_sum_of_mem_nat _ (fun j => n1 (d0 p c j)) j ((mem_sheetJs _ j).mpr h)
  · rw [n1_zero]; omega

lemma n1_add3 (x y z : Z4) : n1 (x + y + z) ≤ n1 x + n1 y + n1 z :=
  (n1_add _ _).trans (by have := n1_add x y; omega)

lemma n1_bC_le (K t t' : ℕ) (pe : PEntry) (ij : Pair 39) (hl : pe.e.label = .inr (.inr (.inr ij)))
    (ht : winSt ij.val.1.val = t) (ht' : winSt ij.val.2.val = t') (j l : Fin 24) :
    n1 (bC K t t' pe j l) ≤ bMass K pe := by
  unfold bC bMass
  rw [hl]
  dsimp only
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  have hm : ∀ c : ℕ, n1 (dd ij.val.1.val c t j * dd ij.val.2.val c t' l) ≤
      3 * (rowMass ij.val.1.val c * rowMass ij.val.2.val c) := by
    intro c
    have h1 := n1_mul (dd ij.val.1.val c t j) (dd ij.val.2.val c t' l)
    have h2 := n1_dd_le ij.val.1.val c ij.val.1.isLt j
    have h3 := n1_dd_le ij.val.2.val c ij.val.2.isLt l
    rw [ht] at h2; rw [ht'] at h3
    calc _ ≤ 3 * n1 (dd ij.val.1.val c t j) * n1 (dd ij.val.2.val c t' l) := h1
      _ ≤ 3 * rowMass ij.val.1.val c * rowMass ij.val.2.val c := Nat.mul_le_mul (Nat.mul_le_mul_left _ h2) h3
      _ = _ := by ring
  have hs := n1_add3 (dd ij.val.1.val 0 t j * dd ij.val.2.val 0 t' l) (dd ij.val.1.val 1 t j * dd ij.val.2.val 1 t' l)
    (dd ij.val.1.val 2 t j * dd ij.val.2.val 2 t' l)
  have hw := n1_mul (wz K pe.e.coefficient) (dd ij.val.1.val 0 t j * dd ij.val.2.val 0 t' l +
    dd ij.val.1.val 1 t j * dd ij.val.2.val 1 t' l + dd ij.val.1.val 2 t j * dd ij.val.2.val 2 t' l)
  have h0 := hm 0; have h1 := hm 1; have h2 := hm 2
  calc _ ≤ _ := hw
    _ ≤ 3 * n1 (wz K pe.e.coefficient) * (3 * (rowMass ij.val.1.val 0 * rowMass ij.val.2.val 0) +
          3 * (rowMass ij.val.1.val 1 * rowMass ij.val.2.val 1) + 3 * (rowMass ij.val.1.val 2 * rowMass ij.val.2.val 2)) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

lemma n1_tTerm_le (sc : ℤ) (i : Fin 4) (a : Fin 3) (t t' : ℕ) (m : Fin 3) (j l : Fin 24) :
    n1 (tTerm sc i a t t' m j l) ≤ (sc * (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).2.2).natAbs := by
  unfold tTerm
  dsimp only
  split_ifs <;> first | (rw [n1_intCast]) | (rw [n1_zero]; omega)

lemma n1_T_le (sc : ℤ) (i : Fin 4) (a : Fin 3) (t t' : ℕ) (j l : Fin 24) :
    n1 (∑ m : Fin 3, tTerm sc i a t t' m j l) ≤ tMass sc i a := by
  unfold tMass
  rw [← Fin.sum_univ_def, Fin.sum_univ_three, Fin.sum_univ_three]
  have := n1_add3 (tTerm sc i a t t' 0 j l) (tTerm sc i a t t' 1 j l) (tTerm sc i a t t' 2 j l)
  have h0 := n1_tTerm_le sc i a t t' 0 j l
  have h1 := n1_tTerm_le sc i a t t' 1 j l
  have h2 := n1_tTerm_le sc i a t t' 2 j l
  omega

/-! ## Scaling (adapted from `HTPCovEngineSound`) -/

lemma Kw_dvd (L : List PEntry) : ∀ pe ∈ L, pe.e.coefficient.denominator ∣ Kw L := by
  induction L with
  | nil => simp
  | cons a L ih =>
    intro pe hpe
    show pe.e.coefficient.denominator ∣ Nat.lcm a.e.coefficient.denominator (Kw L)
    rcases List.mem_cons.mp hpe with rfl | h
    · exact Nat.dvd_lcm_left _ _
    · exact dvd_trans (ih pe h) (Nat.dvd_lcm_right _ _)

lemma Kw_pos (L : List PEntry) : 0 < Kw L := by
  induction L with
  | nil => exact Nat.one_pos
  | cons a L ih => exact Nat.lcm_pos a.e.coefficient.denominator_pos ih

lemma wz_spec (K : ℕ) (c : Literal) (h : c.denominator ∣ K) :
    zq (wz K c) = (K : Q12) * c.toQ12 := by
  obtain ⟨m, rfl⟩ := h
  have hN : (c.denominator : ℚ) ≠ 0 := by exact_mod_cast c.denominator_pos.ne'
  rw [wz, Nat.mul_div_cancel_left m c.denominator_pos]
  ext <;> simp [Literal.toQ12, Q12.lit, Rat.mkRat_eq_div] <;> field_simp

lemma cancel_nat {R : Type*} [CommRing R] (ι : Q12 →+* R) (n : ℕ) (hn : n ≠ 0) (S : R)
    (h : ι (n : Q12) * S = 0) : S = 0 := by
  have hinv : ι (Q12.ofRat (1 / n)) * ι (n : Q12) = 1 := by
    rw [← map_natCast Q12.ofRat n, ← map_mul, ← map_mul, one_div,
      inv_mul_cancel₀ (by exact_mod_cast hn), map_one, map_one]
  calc S = (ι (Q12.ofRat (1 / n)) * ι (n : Q12)) * S := by rw [hinv, one_mul]
    _ = ι (Q12.ofRat (1 / n)) * (ι (n : Q12) * S) := by ring
    _ = 0 := by rw [h, mul_zero]

/-! ## One window block -/

lemma blockSpec (L : List PEntry) (i : Fin 4) (a : Fin 3) (t t' : ℕ) (h : blockCheck L i a t t' = true) :
    ∃ m0 : Ex, (∀ pe ∈ L.filter (fun pe => Nat.beq (part pe) (blk t t')), pe.x = m0) ∧
      (∀ j ∈ sjAt t, charOK t j = true) ∧ (∀ j ∈ sjAt t', charOK t' j = true) ∧ tExpOK m0 i a t t' = true ∧
      ((L.filter fun pe => Nat.beq (part pe) (blk t t')).map (bMass (Kw L))).sum + tMass (vScale (Kw L)) i a < 2 ^ 128 ∧
      ((L.filter fun pe => Nat.beq (part pe) (blk t t')).map (bInt (Kw L))).sum - tInt (vScale (Kw L)) i a t t' = 0 := by
  unfold blockCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Nat.blt_eq, Nat.pow_eq] at h
  obtain ⟨⟨⟨⟨⟨hx, hc1⟩, hc2⟩, he⟩, hb⟩, hz⟩ := h
  exact ⟨_, hx, fun j hj => (hc1 j hj).1, fun j hj => (hc2 j hj).1, he, hb, isZ_spec _ hz⟩

lemma winSt_mono (p q : ℕ) (h : p ≤ q) : winSt p ≤ winSt q := by unfold winSt; omega

lemma block_pair (pe : PEntry) (hok : entryOK pe = true) (t t' : ℕ) (hpart : part pe = blk t t')
    (htt : t < t') (ht' : t' < 4) :
    ∃ ij : Pair 39, pe.e.label = .inr (.inr (.inr ij)) ∧ winSt ij.val.1.val = t ∧ winSt ij.val.2.val = t' ∧
      3 ≤ ij.val.1.val ∧ 3 ≤ ij.val.2.val := by
  unfold part at hpart
  unfold entryOK at hok
  rcases hl : pe.e.label with ⟨i, k⟩ | i | ⟨f, k⟩ | ij <;> rw [hl] at hpart hok <;> dsimp only at hpart
  · unfold blk at hpart; omega
  · unfold blk at hpart; omega
  · unfold blk at hpart; omega
  · simp only [Bool.and_eq_true, Nat.ble_eq, Bool.not_eq_true'] at hok
    obtain ⟨⟨hp, hq⟩, hne⟩ := hok
    have hne' : winSt ij.val.1.val ≠ winSt ij.val.2.val := fun h => by
      rw [h, Nat.beq_refl] at hne; exact absurd hne (by decide)
    have hle := winSt_mono _ _ (le_of_lt ij.property)
    have h1 := winSt_lt ij.val.1
    have h2 := winSt_lt ij.val.2
    unfold blk at hpart
    refine ⟨ij, rfl, ?_, ?_, hp, hq⟩ <;> omega

section BlockSem
variable {R : Type*} [CommRing R] (ι : Q12 →+* R) (U : Fin 4 → Rˣ) (y : Fin 24 → R)

theorem Wv_diagF (hB : baseOK = true) (hK : kPosOK = true) (p : Fin 39) (hp3 : 3 ≤ p.val) (c : Fin 3)
    (hch : ∀ j ∈ sjAt (winSt p.val), charOK (winSt p.val) j = true) :
    ι (4 * bD) * Wv ι U y (variableIndex p ⟨c.val, by omega⟩) =
      ∑ j : Fin 24, y j * ι (zq (dd p.val c.val (winSt p.val) j)) * mono U (eJ j) := by
  rw [sjAt_eq _ (winSt_lt p)] at hch
  rw [Wv_diag ι U y hB hK p hp3 c.val c.isLt hch]
  unfold sheetJs
  rw [sum_filter_ite', Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro j _
  unfold dd
  rw [ite_beq]
  split_ifs <;> simp

lemma mono_zero : mono U ((0, 0, 0, 0) : Ex) = 1 := by simp [mono]

lemma beq_and (a b c d : ℕ) : (Nat.beq a b && Nat.beq c d) = true ↔ a = b ∧ c = d := by
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨Nat.beq_refl _, Nat.beq_refl _⟩

lemma pickR (F : Fin 24 → Fin 24 → R) (j0 l0 : Fin 24) (v : Z4) :
    ∑ j : Fin 24, ∑ l : Fin 24, F j l * ι (zq (if j0 = j ∧ l0 = l then v else 0)) = F j0 l0 * ι (zq v) := by
  rw [Finset.sum_eq_single j0]
  · rw [Finset.sum_eq_single l0]
    · simp
    · intro l _ hl; rw [if_neg (fun h => hl h.2.symm), map_zero, map_zero, mul_zero]
    · simp
  · intro j _ hj
    apply Finset.sum_eq_zero; intro l _; rw [if_neg (fun h => hj h.1.symm), map_zero, map_zero, mul_zero]
  · simp

/-- **Block identity.** -/
theorem block_identity (hB : baseOK = true) (hK : kPosOK = true) (L : List PEntry) (i : Fin 4) (a : Fin 3)
    (t t' : ℕ) (htt : t < t') (ht' : t' < 4) (hok : ∀ pe ∈ L, entryOK pe = true)
    (hdat : ∀ m : Fin 3, sheetOf (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).1 < 4 ∧
      sheetOf (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).2.1 < 4 ∧
      sheetOf (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).1 ≠
        sheetOf (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).2.1)
    (hbc : blockCheck L i a t t' = true) :
    ι ((vScale (Kw L) : ℕ) : Q12) * (((L.filter fun pe => Nat.beq (part pe) (blk t t')).map fun pe =>
        ι pe.e.coefficient.toQ12 * mono U pe.x * pairDiag pe (Wv ι U y)).sum) =
      ∑ m : Fin 3, (if blk (sheetOf (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).1)
          (sheetOf (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).2.1) = blk t t' then
        ι ((vScale (Kw L) : ℕ) : Q12) * ((BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).2.2 : R) *
          y (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).1 *
          y (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).2.1 else 0) := by
  obtain ⟨m0, hx, hch, hch', hexp, hbd, hz⟩ := blockSpec L i a t t' hbc
  set K := Kw L
  set Bl := L.filter fun pe => Nat.beq (part pe) (blk t t')
  have hmemB : ∀ pe ∈ Bl, pe ∈ L ∧ part pe = blk t t' := by
    intro pe hpe
    have h := List.mem_filter.mp hpe
    exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩
  set M : Fin 24 → R := fun j => mono U (eJ j)
  have hvS : ι ((vScale K : ℕ) : Q12) = ι (K : Q12) * ι (4 * bD) * ι (4 * bD) := by
    simp only [vScale, Nat.cast_mul, Nat.cast_ofNat, map_mul]
  -- one entry
  have hval : ∀ pe ∈ Bl, ι ((vScale K : ℕ) : Q12) * (ι pe.e.coefficient.toQ12 * mono U pe.x * pairDiag pe (Wv ι U y)) =
      mono U m0 * ∑ j : Fin 24, ∑ l : Fin 24, (y j * M j) * (y l * M l) * ι (zq (bC K t t' pe j l)) := by
    intro pe hpe
    obtain ⟨hL, hpt⟩ := hmemB pe hpe
    obtain ⟨ij, hl, h1, h2, hp3, hq3⟩ := block_pair pe (hok pe hL) t t' hpt htt ht'
    have hKl : ι (K : Q12) * ι pe.e.coefficient.toQ12 = ι (zq (wz K pe.e.coefficient)) := by
      rw [wz_spec _ _ (Kw_dvd L pe hL), map_mul]
    have Dp : ∀ c : Fin 3, ι (4 * bD) * Wv ι U y (variableIndex ij.val.1 ⟨c.val, by omega⟩) =
        ∑ j : Fin 24, y j * ι (zq (dd ij.val.1.val c.val t j)) * M j := by
      intro c; rw [← h1]; exact Wv_diagF ι U y hB hK _ hp3 c (by rw [h1]; exact hch)
    have Dq : ∀ c : Fin 3, ι (4 * bD) * Wv ι U y (variableIndex ij.val.2 ⟨c.val, by omega⟩) =
        ∑ l : Fin 24, y l * ι (zq (dd ij.val.2.val c.val t' l)) * M l := by
      intro c; rw [← h2]; exact Wv_diagF ι U y hB hK _ hq3 c (by rw [h2]; exact hch')
    unfold pairDiag bC
    rw [hl]
    dsimp only
    rw [hx pe hpe, Fin.sum_univ_three]
    calc _ = (ι (K : Q12) * ι pe.e.coefficient.toQ12) * mono U m0 *
          ((ι (4 * bD) * Wv ι U y (variableIndex ij.val.1 ⟨(0 : Fin 3).val, by omega⟩)) *
              (ι (4 * bD) * Wv ι U y (variableIndex ij.val.2 ⟨(0 : Fin 3).val, by omega⟩)) +
            (ι (4 * bD) * Wv ι U y (variableIndex ij.val.1 ⟨(1 : Fin 3).val, by omega⟩)) *
              (ι (4 * bD) * Wv ι U y (variableIndex ij.val.2 ⟨(1 : Fin 3).val, by omega⟩)) +
            (ι (4 * bD) * Wv ι U y (variableIndex ij.val.1 ⟨(2 : Fin 3).val, by omega⟩)) *
              (ι (4 * bD) * Wv ι U y (variableIndex ij.val.2 ⟨(2 : Fin 3).val, by omega⟩))) := by
          rw [hvS]; ring
      _ = _ := by
          rw [Dp 0, Dp 1, Dp 2, Dq 0, Dq 1, Dq 2, hKl, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum,
            ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [← Finset.sum_add_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          simp only [map_mul, map_sum, Fin.sum_univ_three, map_add]
          ring
  -- sum over the block
  set C : Fin 24 → Fin 24 → Z4 := fun j l => (Bl.map fun pe => bC K t t' pe j l).sum
  have hsum : ι ((vScale K : ℕ) : Q12) * (Bl.map fun pe =>
      ι pe.e.coefficient.toQ12 * mono U pe.x * pairDiag pe (Wv ι U y)).sum =
      mono U m0 * ∑ j : Fin 24, ∑ l : Fin 24, (y j * M j) * (y l * M l) * ι (zq (C j l)) := by
    rw [← List.sum_map_mul_left, List.map_congr_left hval, List.sum_map_mul_left]
    congr 1
    rw [list_finset_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [list_finset_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [C, map_list_sum, List.map_map, Function.comp_def, List.sum_map_mul_left]
  -- digits
  set T : Fin 24 → Fin 24 → Z4 := fun j l => ∑ m : Fin 3, tTerm (vScale K) i a t t' m j l
  have hpack : ∀ pe ∈ Bl, bInt K pe = ∑ j : Fin 24, ∑ l : Fin 24, bC K t t' pe j l * Ypow (j.val + 24 * l.val) := by
    intro pe hpe
    obtain ⟨hL, hpt⟩ := hmemB pe hpe
    obtain ⟨ij, hl, h1, h2, -, -⟩ := block_pair pe (hok pe hL) t t' hpt htt ht'
    exact bInt_eq K t t' pe ij hl h1 h2
  have hBsum : (Bl.map (bInt K)).sum = ∑ j : Fin 24, ∑ l : Fin 24, C j l * Ypow (j.val + 24 * l.val) := by
    rw [List.map_congr_left hpack, list_finset_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [list_finset_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [C, List.sum_map_mul_right]
  have hCT : ∀ j l, C j l - T j l = 0 := by
    apply digits_Z4
    · intro j l
      have hC : n1 (C j l) ≤ (Bl.map (bMass K)).sum := by
        refine (n1_list_sum _).trans ?_
        rw [List.map_map]
        apply List.sum_le_sum
        intro pe hpe
        obtain ⟨hL, hpt⟩ := hmemB pe hpe
        obtain ⟨ij, hl, h1, h2, -, -⟩ := block_pair pe (hok pe hL) t t' hpt htt ht'
        exact n1_bC_le K t t' pe ij hl h1 h2 j l
      have hT : n1 (T j l) ≤ tMass (vScale K) i a := n1_T_le (vScale K) i a t t' j l
      have := n1_sub (C j l) (T j l)
      omega
    · rw [tInt_eq, hBsum] at hz
      simp only [sub_mul, Finset.sum_sub_distrib]
      exact hz
  have hCT' : ∀ j l, C j l = T j l := fun j l => sub_eq_zero.mp (hCT j l)
  rw [hsum]
  simp only [hCT', T, map_sum, Finset.mul_sum]
  rw [show (∑ j : Fin 24, ∑ l : Fin 24, ∑ m : Fin 3, mono U m0 * (y j * M j * (y l * M l) *
        ι (zq (tTerm (vScale K) i a t t' m j l)))) =
      ∑ m : Fin 3, ∑ j : Fin 24, ∑ l : Fin 24, mono U m0 * (y j * M j * (y l * M l) *
        ι (zq (tTerm (vScale K) i a t t' m j l))) from
    (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hE := (List.all_eq_true.mp hexp) m (List.mem_finRange m)
  obtain ⟨hs1, hs2, hs12⟩ := hdat m
  simp only [← Finset.mul_sum]
  unfold tTerm
  dsimp only
  set e := BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m with he_def
  have hcast : ι (zq (((vScale K : ℤ) * e.2.2 : ℤ) : Z4)) = ι ((vScale K : ℕ) : Q12) * (e.2.2 : R) := by
    rw [map_intCast, map_intCast, map_natCast]; push_cast; ring
  have hE' : Nat.beq (blk (sheetOf e.1) (sheetOf e.2.1)) (blk t t') = false ∨
      Ex.add m0 (Ex.add (eJ e.1) (eJ e.2.1)) = (0, 0, 0, 0) := by
    have := hE
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
    exact this
  have hm : blk (sheetOf e.1) (sheetOf e.2.1) = blk t t' → mono U m0 * M e.1 * M e.2.1 = 1 := by
    intro hb
    have hb' : Nat.beq (blk (sheetOf e.1) (sheetOf e.2.1)) (blk t t') = true := by rw [hb]; exact Nat.beq_refl _
    have hz0 := hE'.resolve_left (by rw [hb']; decide)
    have : mono U m0 * M e.1 * M e.2.1 = mono U (Ex.add m0 (Ex.add (eJ e.1) (eJ e.2.1))) := by
      simp only [M]; rw [mono_add, mono_add]; ring
    rw [this, hz0]; exact mono_zero U
  by_cases c1 : (Nat.beq (sheetOf e.1) t && Nat.beq (sheetOf e.2.1) t') = true
  · simp only [c1, ite_true]
    rw [pickR ι (fun j l => y j * M j * (y l * M l)) e.1 e.2.1]
    obtain ⟨q1, q2⟩ := (beq_and _ _ _ _).mp c1
    have hb : blk (sheetOf e.1) (sheetOf e.2.1) = blk t t' := by rw [q1, q2]
    rw [if_pos hb, hcast]
    linear_combination (ι ((vScale K : ℕ) : Q12) * (e.2.2 : R) * y e.1 * y e.2.1) * hm hb
  · by_cases c2 : (Nat.beq (sheetOf e.1) t' && Nat.beq (sheetOf e.2.1) t) = true
    · simp only [c1, c2, ite_true, Bool.false_eq_true, ite_false]
      rw [pickR ι (fun j l => y j * M j * (y l * M l)) e.2.1 e.1]
      obtain ⟨q1, q2⟩ := (beq_and _ _ _ _).mp c2
      have hb : blk (sheetOf e.1) (sheetOf e.2.1) = blk t t' := by rw [q1, q2]; unfold blk; omega
      rw [if_pos hb, hcast]
      linear_combination (ι ((vScale K : ℕ) : Q12) * (e.2.2 : R) * y e.1 * y e.2.1) * hm hb
    · simp only [c1, c2, Bool.false_eq_true, ite_false, map_zero, mul_zero, Finset.sum_const_zero]
      have hb : blk (sheetOf e.1) (sheetOf e.2.1) ≠ blk t t' := by
        intro hb
        rw [beq_and] at c1 c2
        unfold blk at hb
        omega
      rw [if_neg hb]

end BlockSem

/-! ## The value theorem of the engine -/

def pairs6 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

def blkList : List ℕ := [1, 2, 3, 6, 7, 11]

lemma blkList_eq : blkList = pairs6.map fun tt => blk tt.1 tt.2 := rfl

lemma blkList_nodup : blkList.Nodup := by decide

lemma blk_mem (w1 w2 : ℕ) (h1 : w1 < 4) (h2 : w2 < 4) (h : w1 ≠ w2) : blk w1 w2 ∈ blkList := by
  interval_cases w1 <;> interval_cases w2 <;> simp_all [blk, blkList]

lemma pairs6_spec (tt : ℕ × ℕ) (h : tt ∈ pairs6) : tt.1 < tt.2 ∧ tt.2 < 4 := by
  simp only [pairs6, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

lemma ite_key_sum' {R : Type*} [AddCommMonoid R] (K : List ℕ) (hK : K.Nodup) (k : ℕ) (v : R) :
    (K.map fun b => if k = b then v else 0).sum = if k ∈ K then v else 0 := by
  rw [← ite_key_sum K hK k v]
  congr 1
  apply List.map_congr_left
  intro b _
  rw [ite_beq]

lemma dataSpec (L : List PEntry) (i : Fin 4) (a : Fin 3) (h : dataCheck L i a = true) :
    (∀ pe ∈ L, entryOK pe = true) ∧
    ∀ m : Fin 3, sheetOf (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).1 < 4 ∧
      sheetOf (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).2.1 < 4 ∧
      sheetOf (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).1 ≠
        sheetOf (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).2.1 := by
  unfold dataCheck at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  refine ⟨h.1, fun m => ?_⟩
  have := h.2 m (List.mem_finRange m)
  simp only [Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  exact ⟨h1, h2, fun e => by rw [e, Nat.beq_refl] at h3; exact absurd h3 (by decide)⟩

section Final
variable {R : Type*} [CommRing R] (ι : Q12 →+* R) (U : Fin 4 → Rˣ) (y : Fin 24 → R)

/-- **Engine value theorem.** If the data checks and the six block checks hold for covector `L` and Book
component `(i, a)`, then for every ring, ring map, units `U` and every `y`, the covector's contraction of the
quadratic row parts at `w = N(y)Φ(U)` is the Book quadric of `(i, a)`. -/
theorem engine_value (hB : baseOK = true) (hK : kPosOK = true) (hC : closureOK = true) (L : List PEntry)
    (i : Fin 4) (a : Fin 3) (hdata : dataCheck L i a = true)
    (hbl : ∀ tt ∈ pairs6, blockCheck L i a tt.1 tt.2 = true) :
    (L.map fun pe => ι pe.e.coefficient.toQ12 * mono U pe.x *
        quadraticPartValue (ι half) (fNumber pe.e.label) (Wv ι U y)).sum =
      ∑ m : Fin 3, ((BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).2.2 : R) *
        y (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).1 *
        y (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).2.1 := by
  obtain ⟨hok, hdat⟩ := dataSpec L i a hdata
  set K := Kw L
  have hred : (L.map fun pe => ι pe.e.coefficient.toQ12 * mono U pe.x *
      quadraticPartValue (ι half) (fNumber pe.e.label) (Wv ι U y)).sum =
      (L.map fun pe => ι pe.e.coefficient.toQ12 * mono U pe.x * pairDiag pe (Wv ι U y)).sum := by
    congr 1; apply List.map_congr_left; intro pe hpe
    rw [pairRow_reduction ι U y hB hC pe (hok pe hpe)]
  rw [hred]
  rw [← sub_eq_zero]
  apply cancel_nat ι (vScale K) (by unfold vScale bD; have := Kw_pos L; positivity)
  rw [mul_sub]
  rw [partition_sum L part blkList blkList_nodup _ (by
    intro pe hpe hnot
    unfold pairDiag
    have hk := hok pe hpe
    unfold entryOK at hk
    unfold part at hnot
    rcases hl : pe.e.label with ⟨i', k⟩ | i' | ⟨f, k⟩ | ij <;> rw [hl] at hk hnot <;> dsimp only <;>
      try simp
    simp only [Bool.and_eq_true, Nat.ble_eq, Bool.not_eq_true'] at hk
    exfalso; apply hnot
    apply blk_mem _ _ (winSt_lt _) (winSt_lt _)
    intro h; rw [h, Nat.beq_refl] at hk; exact absurd hk.2 (by decide))]
  rw [← List.sum_map_mul_left, blkList_eq, List.map_map]
  rw [List.map_congr_left (fun tt htt => by
    obtain ⟨h1, h2⟩ := pairs6_spec tt htt
    exact block_identity ι U y hB hK L i a tt.1 tt.2 h1 h2 hok hdat (hbl tt htt))]
  rw [list_finset_comm, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro m _
  obtain ⟨hs1, hs2, hs12⟩ := hdat m
  have hmem := blk_mem _ _ hs1 hs2 hs12
  rw [blkList_eq] at hmem
  have e1 := ite_key_sum' (pairs6.map fun tt => blk tt.1 tt.2) (by rw [← blkList_eq]; exact blkList_nodup)
    (blk (sheetOf (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).1)
      (sheetOf (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).2.1))
    (ι ((vScale K : ℕ) : Q12) * ((BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).2.2 : R) *
      y (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).1 *
      y (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).2.1)
  rw [List.map_map] at e1
  simp only [Function.comp_def] at e1
  rw [e1, if_pos hmem]
  ring

end Final

end Option2.NativeStress.HTPhaseComplete.ValEng

#print axioms Option2.NativeStress.HTPhaseComplete.ValEng.engine_value
#print axioms Option2.NativeStress.HTPhaseComplete.ValEng.pairRow_reduction
#print axioms Option2.NativeStress.HTPhaseComplete.ValEng.block_identity

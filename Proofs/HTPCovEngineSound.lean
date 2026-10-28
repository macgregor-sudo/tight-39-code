module

public import HTPCovEngine

@[expose] public section

/-! # Soundness of the integer Laurent engine (first-party, generic in the covector data)

`engine_sound`: if every state check of `HTPCovEngine.stateCheck` holds for a covector `L`, then for every
commutative ring `R`, ring map `ι : Q12 →+* R` and units `U`, the phased covector annihilates every original
Jacobian column at `PhiR ι U` — exactly the statement shape of `HTPhaseKron.t00_phased_equilibrium`.
Chain: integer base point (`baseZ_spec`, one kernel check of the 1053 base coordinates) → integer phased
point (`phiZ_sem`) → integer Jacobian rows (`rowZ_sem`, through the original `labelShape`) → exact slot
collection (`collZ_sum`, Kronecker slots `key`, `dec_key`) → cancellation of the unit `ι(Kw · 4 bD)`. -/

set_option autoImplicit false
namespace Option2.NativeStress.HTPhaseComplete
open HTPhaseKron HTRouteKron NativeH NativeH.Equilibrium ConfigurationResidualIndices
open QuarticCertificate.RowBridge

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

lemma zq_zI : zq zI = Q12.I := by ext <;> simp [zI, Q12.I]

lemma mulI_eq (x : Z4) : mulI x = zI * x := by ext <;> simp [mulI, zI]

lemma isZ_spec (x : Z4) (h : isZ x = true) : x = 0 := by
  simp only [isZ, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ := h
  ext <;> simp [ha, hb, hc, hd]

/-! ## The integer base point -/

def ratOK (q : ℚ) : Bool := ((bD : ℚ) * q).den == 1

/-- One kernel check: `bD` clears every denominator of the original `baseQ12`. -/
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

lemma phiAt_eq (v : Fin 1053) : phiAt v = phiZ v := by
  unfold phiAt phiTab
  rw [getD_blocks]
  simp [phiZn, v.isLt]

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
        · rw [half_mul, map_add, mulI_eq, map_mul, zq_zI, zq_bz, zq_bz]; ring
        · rw [half_mul, map_sub, mulI_eq, map_mul, zq_zI, zq_bz, zq_bz]; ring
      · simp only [hp, if_false, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ev]
        rw [mul_add, term_eq ι _ (half * (Q12.I * (bq a - Q12.I * bq (a + 1)))),
          term_eq ι _ (-(half * (Q12.I * (bq a + Q12.I * bq (a + 1)))))]
        · rw [show (2 : Q12) * bD * -(half * (Q12.I * (bq a + Q12.I * bq (a + 1)))) =
            -(2 * bD * (half * (Q12.I * (bq a + Q12.I * bq (a + 1))))) by ring, half_mul, map_neg]
          congr 1
          rw [mulI_eq, map_mul, zq_zI, map_add, mulI_eq, map_mul, zq_zI, zq_bz, zq_bz]; ring
        · rw [half_mul, mulI_eq, mulI_eq, map_mul, map_sub, map_mul, zq_zI, zq_bz, zq_bz]; ring

/-! ## Integer Jacobian rows -/

lemma sum_ite_map (l : List (Z4 × Ex)) (n c : ℕ) (A : Z4) (x : Ex) :
    ((l.map fun t => (n, A * t.1, Ex.add x t.2)).map fun t =>
        if Nat.beq t.1 c then ι (zq t.2.1) * mono U t.2.2 else 0).sum =
      if n = c then ι (zq A) * mono U x * (l.map fun t => ι (zq t.1) * mono U t.2).sum else 0 := by
  by_cases h : n = c
  · subst h
    simp only [List.map_map, Function.comp_def, Nat.beq_refl, if_true]
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [map_mul, mono_add]
    ring
  · have hb : Nat.beq n c = false := by
      cases h' : Nat.beq n c
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h') h
    simp [List.map_map, Function.comp_def, hb, h]

lemma guard_sum (b : Bool) (L : List (ℕ × Z4 × Ex)) (c : ℕ)
    (hb : ∀ t ∈ L, Nat.beq t.1 c = true → b = true) :
    ((if b then L else []).map fun t =>
        if Nat.beq t.1 c then ι (zq t.2.1) * mono U t.2.2 else 0).sum =
      (L.map fun t => if Nat.beq t.1 c then ι (zq t.2.1) * mono U t.2.2 else 0).sum := by
  cases b
  · simp only [Bool.false_eq_true, if_false, List.map_nil, List.sum_nil]
    symm
    apply List.sum_eq_zero
    intro y hy
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
    cases h : Nat.beq t.1 c
    · rfl
    · exact absurd (hb t ht h) (by simp)
  · rfl

lemma sum_filter_ite {α : Type*} (l : List α) (p : α → Bool) (f : α → R) :
    ((l.filter p).map f).sum = (l.map fun t => if p t then f t else 0).sum := by
  induction l with
  | nil => rfl
  | cons t l ih => cases h : p t <;> simp [List.filter_cons, h, ih]

lemma sc_lemma (s : RowShape) :
    (sc2 s : R) * ι (2 * bD) = ι (4 * bD) * quadraticScale (ι half) s := by
  unfold sc2 quadraticScale
  cases s.halfScaled
  · simp only [Bool.false_eq_true, if_false, map_mul, map_ofNat, map_natCast]; push_cast; ring
  · simp only [if_true, Int.cast_one, one_mul]
    rw [← map_mul]; congr 1
    linear_combination (-2 * (bD : Q12)) * two_half

lemma ite_mul_zero (P : Prop) [Decidable P] (a b : R) :
    (if P then a * b else 0) = a * (if P then b else 0) := by
  split_ifs <;> simp

theorem rowZ_sem (K p : ℕ) (pe : PEntry) (c : Fin 1053) (hc : c.val / 27 = p) :
    ((rowZ K p pe).map fun t => if Nat.beq t.1 c.val then ι (zq t.2.1) * mono U t.2.2 else 0).sum =
      ι (zq (wz K pe.e.coefficient)) * mono U pe.x *
        (ι (4 * bD) * shapeJacobianEntry (ι half) (labelShape pe.e.label) (PhiR ι U) c) := by
  have hcol : ∀ n, Nat.beq n c.val = true → Nat.beq (n / 27) p = true := by
    intro n h; rw [Nat.beq_eq] at h ⊢; rw [h, hc]
  unfold rowZ shapeJacobianEntry
  simp only [List.map_append, List.sum_append, sum_map_flatMap]
  rw [mul_add, mul_add]
  congr 1
  · rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro q _
    rw [guard_sum ι U _ _ _ (fun t ht h => by
        obtain ⟨u, _, rfl⟩ := List.mem_map.mp ht; exact hcol _ h)]
    rw [guard_sum ι U _ _ _ (fun t ht h => by
        obtain ⟨u, _, rfl⟩ := List.mem_map.mp ht; exact hcol _ h)]
    rw [sum_ite_map, sum_ite_map, phiAt_eq, phiAt_eq, phiZ_sem, phiZ_sem]
    simp only [Fin.val_inj, ite_mul_zero]
    generalize (if q.1 = c then PhiR ι U q.2.1 else 0) = X
    generalize (if q.2.1 = c then PhiR ι U q.1 else 0) = Y
    have key := sc_lemma ι (labelShape pe.e.label)
    simp only [map_zsmul, zsmul_eq_mul, map_mul, map_intCast, Int.cast_mul] at key ⊢
    linear_combination (ι (zq (wz K pe.e.coefficient)) * mono U pe.x * (q.2.2 : R) * (X + Y)) * key
  · rw [List.map_map, sum_filter_ite, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro l _
    by_cases h : l.1 = c
    · subst h
      simp only [Function.comp_def, Nat.beq_refl, hcol _ (Nat.beq_refl _), if_true, map_zsmul,
        zsmul_eq_mul, map_mul, map_intCast, map_ofNat, map_natCast]
      push_cast; ring
    · have hb : Nat.beq l.1.val c.val = false := by
        cases h' : Nat.beq l.1.val c.val
        · rfl
        · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true h')) h
      simp only [Function.comp_def, hb, Bool.false_eq_true, if_false, ite_self, h, mul_zero]

end Sem

/-! ## Exact slot collection (Kronecker digit positions) -/

/-- Decoding of a slot: base-7 digits minus 3. -/
def dec (e : ℕ) : Ex :=
  (((e % 7 : ℕ) : ℤ) - 3, (((e / 7) % 7 : ℕ) : ℤ) - 3, (((e / 49) % 7 : ℕ) : ℤ) - 3,
    (((e / 343) % 7 : ℕ) : ℤ) - 3)

lemma dec_key (m : Ex) (h : inBox m = true) : dec (key m) = m := by
  obtain ⟨a, b, c, d⟩ := m
  simp only [inBox, decide_eq_true_eq] at h
  simp only [dec, key, Prod.mk.injEq]
  omega

section Collect
variable {R : Type*} [CommRing R] (ι : Q12 →+* R) (U : Fin 4 → Rˣ)

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

theorem colCheck_sound (ts : List (ℕ × Z4 × Ex)) (c : ℕ) (h : colCheck ts c = true) :
    ((ts.filter fun t => Nat.beq t.1 c).map fun t => ι (zq t.2.1) * mono U t.2.2).sum = 0 := by
  unfold colCheck at h
  dsimp only at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  obtain ⟨hbox, hz⟩ := h
  have e : ((ts.filter fun t => Nat.beq t.1 c).map fun t => ι (zq t.2.1) * mono U t.2.2).sum =
      ((((ts.filter fun t => Nat.beq t.1 c).map fun t => (key t.2.2, t.2.1))).map
        fun p => ι (zq p.2) * mono U (dec p.1)).sum := by
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro t ht
    simp only [Function.comp_def, dec_key _ (hbox t ht)]
  have hc := collZ_sum ι (fun e => mono U (dec e))
    ((ts.filter fun t => Nat.beq t.1 c).map fun t => (key t.2.2, t.2.1))
  rw [e, ← hc]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  rw [isZ_spec _ (hz q hq), map_zero, map_zero, zero_mul]

theorem state_col (K p : ℕ) (F : List PEntry) (c : Fin 1053) (hc : c.val / 27 = p) :
    (((F.flatMap (rowZ K p)).filter fun t => Nat.beq t.1 c.val).map
        fun t => ι (zq t.2.1) * mono U t.2.2).sum =
      (F.map fun pe => ι (zq (wz K pe.e.coefficient)) * mono U pe.x *
        (ι (4 * bD) * shapeJacobianEntry (ι half) (labelShape pe.e.label) (PhiR ι U) c)).sum := by
  rw [sum_filter_ite, sum_map_flatMap]
  congr 1
  apply List.map_congr_left
  intro pe _
  exact rowZ_sem ι U K p pe c hc

end Collect

/-! ## Scaling and cancellation -/

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

/-- **Engine soundness.** The per-state integer checks imply the phased equilibrium identity for every
commutative ring, ring map from `Q12` and units, through the original typed rows and `jacobianEntry`. -/
theorem engine_sound (L : List PEntry)
    (h : ∀ p : Fin 39, stateCheck (Kw L) (L.filter (touches p)) p.val = true)
    {R : Type*} [CommRing R] (ι : Q12 →+* R) (U : Fin 4 → Rˣ) (t : R) (c : Fin 1053) :
    (L.map fun pe => ι pe.e.coefficient.toQ12 * mono U pe.x *
        jacobianEntry (ι half) t (fNumber pe.e.label) (PhiR ι U) c).sum = 0 := by
  rw [sum_filter_touches]
  simp only [jacobianEntry, rowShape, Equiv.symm_apply_apply]
  have hs := h (variableSlot c)
  unfold stateCheck at hs
  dsimp only at hs
  rw [List.all_eq_true] at hs
  have hk := hs (c.val % 27) (List.mem_range.mpr (Nat.mod_lt _ (by norm_num)))
  have e : 27 * (variableSlot c).val + c.val % 27 = c.val := by simp only [variableSlot]; omega
  rw [e] at hk
  have h0 := colCheck_sound ι U _ _ hk
  rw [state_col ι U _ _ _ c (by simp [variableSlot])] at h0
  have h1 : ι ((Kw L * (4 * bD) : ℕ) : Q12) *
      ((L.filter (touches (variableSlot c))).map fun pe => ι pe.e.coefficient.toQ12 * mono U pe.x *
        shapeJacobianEntry (ι half) (labelShape pe.e.label) (PhiR ι U) c).sum = 0 := by
    rw [← h0, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro pe hpe
    rw [wz_spec _ _ (Kw_dvd L pe (List.mem_of_mem_filter hpe))]
    push_cast
    simp only [map_mul, map_natCast, map_ofNat]
    ring
  exact cancel_nat ι _ (Nat.mul_ne_zero (Kw_pos L).ne' (by decide)) _ h1

end Option2.NativeStress.HTPhaseComplete
#print axioms Option2.NativeStress.HTPhaseComplete.engine_sound
#print axioms Option2.NativeStress.HTPhaseComplete.baseZ_spec

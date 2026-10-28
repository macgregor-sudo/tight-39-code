module

public import SpanningDescent

/-!
# The `p`-integral subring `A_p ⊂ Q12` and its reduction modulo `p`

Purpose. The exact parameters of the quartic certificate (the constants `1/2`, `1/3`, the point,
the annihilator weights, the slice basis) are elements of `Q12 = ℚ(i, √3)` whose rational
coordinates have denominators coprime to the prime `p = 1048573`. This module builds the ring
that carries them both to `ℂ` and to `ZMod p`:

* `Q12.ratLocalSubring p : Subring ℚ` — rationals whose reduced denominator is coprime to `p`
  (the localisation `ℤ_(p)`), with the reduction `Q12.ratReduceHom p hp : … →+* ZMod p`,
  `q ↦ num(q) · den(q)⁻¹`. The denominators map to units (`Q12.ratLocal_den_isUnit`).
* `Q12.pIntegralSubring p : Subring Q12` — elements of `Q12` all four of whose coordinates are
  `p`-local. For prime `p` this is "no denominator divisible by `p`"
  (`Q12.mem_pIntegralSubring_iff_not_dvd`).
* `Q12.reduceMod p hp ri rs hi hs : pIntegralSubring p →+* ZMod p`,
  `a + b i + c √3 + d i √3 ↦ ā + b̄·ri + c̄·rs + d̄·(ri·rs)`.
* `Q12.pIntegralToComplex p`, the injective inclusion `A_p → Q12 → ℂ`.
* Compatibility with the integer lattice `Z12` of `Q12`, literal membership
  (`Q12.lit_mem_pIntegralSubring`) and kernel-checkable Boolean membership tests
  (`Q12.denominatorsCoprime`, `Q12.allPIntegral`) with soundness lemmas.
* The concrete prime `1048573` (`i ↦ 365259`, `√3 ↦ 1024`) and the constants `1/2`, `1/3`.

The statements use the standard Lean axioms.
What is assumed: nothing beyond Mathlib and the imported `Q12`, `IntegerQ12`, `SpanningDescent`.
The definitions of `ratReduce` and `reduceMod` use only `ZMod`'s own (gcd-based) inverse, so the
kernel can evaluate them on literals; the field structure on `ZMod p`
(`Matrix.zmodField`) is used only inside proofs.

Use: only *nonvanishing* is ever transferred from `ZMod p` (descent of `det ≠ 0`); no equality
over `Q12` or `ℂ` is inferred from a modular computation.

First-party definitions (no borrowed code).
-/

@[expose] public section

set_option linter.style.haveILetI false

namespace Q12

/-! ## The `p`-local rationals -/

/-- The rationals whose reduced denominator is coprime to `p`: the localisation `ℤ_(p)`,
realised as a subring of `ℚ`. Closure uses `(q + r).den ∣ q.den * r.den` and
`(q * r).den ∣ q.den * r.den`. -/
def ratLocalSubring (p : ℕ) : Subring ℚ where
  carrier := {q | Nat.Coprime q.den p}
  mul_mem' {q r} hq hr :=
    Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd q r) (Nat.Coprime.mul_left hq hr)
  one_mem' := by show Nat.Coprime (1 : ℚ).den p; simp
  add_mem' {q r} hq hr :=
    Nat.Coprime.coprime_dvd_left (Rat.add_den_dvd q r) (Nat.Coprime.mul_left hq hr)
  zero_mem' := by show Nat.Coprime (0 : ℚ).den p; simp
  neg_mem' {q} hq := by show Nat.Coprime (-q).den p; rw [Rat.neg_den]; exact hq

theorem mem_ratLocalSubring {p : ℕ} {q : ℚ} :
    q ∈ ratLocalSubring p ↔ Nat.Coprime q.den p := Iff.rfl

/-- For a prime `p`, being `p`-local means that `p` does not divide the denominator. -/
theorem mem_ratLocalSubring_iff_not_dvd {p : ℕ} (hp : p.Prime) {q : ℚ} :
    q ∈ ratLocalSubring p ↔ ¬ p ∣ q.den := by
  rw [mem_ratLocalSubring, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]

/-- **Denominators map to units.** The reduced denominator of a `p`-local rational is a unit
in `ZMod p`. This is the hypothesis that makes reduction of localised coefficients legitimate. -/
theorem ratLocal_den_isUnit {p : ℕ} {q : ℚ} (hq : q ∈ ratLocalSubring p) :
    IsUnit ((q.den : ℕ) : ZMod p) :=
  (ZMod.isUnit_iff_coprime _ _).2 hq

/-- The denominator of `mkRat A N` divides `N`. -/
theorem den_mkRat_dvd (A : ℤ) (N : ℕ) : (mkRat A N).den ∣ N := by
  rw [Rat.den_mkRat]
  split_ifs with h
  · exact one_dvd _
  · exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)

/-- `mkRat A N` is `p`-local whenever `N` is coprime to `p`. -/
theorem mkRat_mem_ratLocalSubring {p : ℕ} (A : ℤ) {N : ℕ} (hN : Nat.Coprime N p) :
    mkRat A N ∈ ratLocalSubring p :=
  Nat.Coprime.coprime_dvd_left (den_mkRat_dvd A N) hN

/-! ## Reduction of `p`-local rationals -/

/-- Reduction of a rational modulo `p`: `num(q) · den(q)⁻¹` in `ZMod p`, with `ZMod`'s own
inverse. Meaningful (a ring homomorphism) on `ratLocalSubring p`, where `den(q)` is a unit
(`ratLocal_den_isUnit`). Kernel-computable. -/
def ratReduce (p : ℕ) (q : ℚ) : ZMod p := (q.num : ZMod p) * ((q.den : ℕ) : ZMod p)⁻¹

/-- Inside proofs, with the field structure `Matrix.zmodField p hp`, `ratReduce` is the
canonical cast `ℚ → ZMod p`. -/
private theorem ratReduce_eq_cast (p : ℕ) (hp : p.Prime) (q : ℚ) :
    ratReduce p q = (@Rat.cast (ZMod p) (Matrix.zmodField p hp).toRatCast q) := by
  letI := Matrix.zmodField p hp
  rw [Rat.cast_def]
  rfl

private theorem den_ne_zero_of_mem {p : ℕ} (hp : p.Prime) {q : ℚ} (hq : q ∈ ratLocalSubring p) :
    ((q.den : ℕ) : ZMod p) ≠ 0 := by
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  exact (ratLocal_den_isUnit hq).ne_zero

/-- Reduction modulo a prime `p` as a ring homomorphism `ℤ_(p) →+* ZMod p`.
Well defined because denominators map to units (`ratLocal_den_isUnit`). -/
def ratReduceHom (p : ℕ) (hp : p.Prime) : ratLocalSubring p →+* ZMod p where
  toFun q := ratReduce p q
  map_one' := by
    letI := Matrix.zmodField p hp
    rw [ratReduce_eq_cast p hp]
    exact Rat.cast_one
  map_zero' := by
    letI := Matrix.zmodField p hp
    rw [ratReduce_eq_cast p hp]
    exact Rat.cast_zero
  map_add' q r := by
    letI := Matrix.zmodField p hp
    simp only [Subring.coe_add, ratReduce_eq_cast p hp]
    exact Rat.cast_add_of_ne_zero (den_ne_zero_of_mem hp q.2) (den_ne_zero_of_mem hp r.2)
  map_mul' q r := by
    letI := Matrix.zmodField p hp
    simp only [Subring.coe_mul, ratReduce_eq_cast p hp]
    exact Rat.cast_mul_of_ne_zero (den_ne_zero_of_mem hp q.2) (den_ne_zero_of_mem hp r.2)

theorem ratReduceHom_apply (p : ℕ) (hp : p.Prime) (q : ratLocalSubring p) :
    ratReduceHom p hp q = ratReduce p q := rfl

/-- Integers reduce to their residues. -/
theorem ratReduce_intCast (p : ℕ) (n : ℤ) : ratReduce p (n : ℚ) = (n : ZMod p) := by
  simp [ratReduce, Rat.num_intCast, Rat.den_intCast]

/-- A literal fraction `A / N` with `N` coprime to the prime `p` reduces to `A · N⁻¹`. -/
theorem ratReduce_mkRat (p : ℕ) (hp : p.Prime) (A : ℤ) {N : ℕ} (hN : Nat.Coprime N p) :
    ratReduce p (mkRat A N) = (A : ZMod p) * ((N : ℕ) : ZMod p)⁻¹ := by
  letI := Matrix.zmodField p hp
  have hN0 : ((N : ℕ) : ZMod p) ≠ 0 := by
    haveI : Fact (1 < p) := ⟨hp.one_lt⟩
    exact ((ZMod.isUnit_iff_coprime _ _).2 hN).ne_zero
  rw [ratReduce_eq_cast p hp, Rat.cast_mkRat_of_ne_zero A hN0, div_eq_mul_inv]

/-! ## The `p`-integral subring of `Q12` -/

/-- `A_p`: elements `a + b i + c √3 + d i √3` of `Q12` whose four rational coordinates are
`p`-local (denominators coprime to `p`). -/
def pIntegralSubring (p : ℕ) : Subring Q12 where
  carrier := {x | x.a ∈ ratLocalSubring p ∧ x.b ∈ ratLocalSubring p ∧
    x.c ∈ ratLocalSubring p ∧ x.d ∈ ratLocalSubring p}
  mul_mem' {x y} hx hy := by
    obtain ⟨ha, hb, hc, hd⟩ := hx
    obtain ⟨ha', hb', hc', hd'⟩ := hy
    have h3 : (3 : ℚ) ∈ ratLocalSubring p := by
      show Nat.Coprime (3 : ℚ).den p
      exact Nat.coprime_one_left p
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mul_a]
      exact sub_mem (add_mem (sub_mem (mul_mem ha ha') (mul_mem hb hb'))
        (mul_mem h3 (mul_mem hc hc'))) (mul_mem h3 (mul_mem hd hd'))
    · rw [mul_b]
      exact add_mem (add_mem (mul_mem ha hb') (mul_mem hb ha'))
        (mul_mem h3 (add_mem (mul_mem hc hd') (mul_mem hd hc')))
    · rw [mul_c]
      exact sub_mem (add_mem (mul_mem ha hc') (mul_mem hc ha'))
        (add_mem (mul_mem hb hd') (mul_mem hd hb'))
    · rw [mul_d]
      exact add_mem (add_mem (add_mem (mul_mem ha hd') (mul_mem hd ha')) (mul_mem hb hc'))
        (mul_mem hc hb')
  one_mem' := ⟨one_mem _, zero_mem _, zero_mem _, zero_mem _⟩
  add_mem' {x y} hx hy := ⟨add_mem hx.1 hy.1, add_mem hx.2.1 hy.2.1,
    add_mem hx.2.2.1 hy.2.2.1, add_mem hx.2.2.2 hy.2.2.2⟩
  zero_mem' := ⟨zero_mem _, zero_mem _, zero_mem _, zero_mem _⟩
  neg_mem' {x} hx := ⟨neg_mem hx.1, neg_mem hx.2.1, neg_mem hx.2.2.1, neg_mem hx.2.2.2⟩

theorem mem_pIntegralSubring {p : ℕ} {x : Q12} :
    x ∈ pIntegralSubring p ↔ Nat.Coprime x.a.den p ∧ Nat.Coprime x.b.den p ∧
      Nat.Coprime x.c.den p ∧ Nat.Coprime x.d.den p := Iff.rfl

/-- For a prime `p`: `x ∈ A_p` iff no coordinate denominator of `x` is divisible by `p`. -/
theorem mem_pIntegralSubring_iff_not_dvd {p : ℕ} (hp : p.Prime) {x : Q12} :
    x ∈ pIntegralSubring p ↔ ¬ p ∣ x.a.den ∧ ¬ p ∣ x.b.den ∧ ¬ p ∣ x.c.den ∧ ¬ p ∣ x.d.den := by
  simp only [pIntegralSubring, Subring.mem_mk, mem_ratLocalSubring_iff_not_dvd hp]
  rfl

/-- **Denominators map to units** (all four coordinates of an element of `A_p`). -/
theorem pIntegral_denominators_isUnit {p : ℕ} {x : Q12} (hx : x ∈ pIntegralSubring p) :
    IsUnit ((x.a.den : ℕ) : ZMod p) ∧ IsUnit ((x.b.den : ℕ) : ZMod p) ∧
      IsUnit ((x.c.den : ℕ) : ZMod p) ∧ IsUnit ((x.d.den : ℕ) : ZMod p) :=
  ⟨ratLocal_den_isUnit hx.1, ratLocal_den_isUnit hx.2.1, ratLocal_den_isUnit hx.2.2.1,
    ratLocal_den_isUnit hx.2.2.2⟩

instance decidableMemPIntegralSubring (p : ℕ) : DecidablePred (· ∈ pIntegralSubring p) :=
  fun x => decidable_of_iff (Nat.Coprime x.a.den p ∧ Nat.Coprime x.b.den p ∧
    Nat.Coprime x.c.den p ∧ Nat.Coprime x.d.den p) mem_pIntegralSubring.symm

/-- A literal `Q12.lit A B C D N = (A + B i + C √3 + D i √3) / N` lies in `A_p` whenever `N` is
coprime to `p`. -/
theorem lit_mem_pIntegralSubring {p : ℕ} (A B C D : ℤ) {N : ℕ} (hN : Nat.Coprime N p) :
    lit A B C D N ∈ pIntegralSubring p :=
  ⟨mkRat_mem_ratLocalSubring A hN, mkRat_mem_ratLocalSubring B hN,
    mkRat_mem_ratLocalSubring C hN, mkRat_mem_ratLocalSubring D hN⟩

/-! ### Kernel-checkable Boolean membership tests -/

/-- `true` iff every number in the list is coprime to `p`. Intended for one `decide +kernel`
per data file over the list of all literal denominators `N` occurring in it. -/
def denominatorsCoprime (p : ℕ) (Ns : List ℕ) : Bool :=
  Ns.all fun N => Nat.gcd N p == 1

/-- Soundness of `denominatorsCoprime`. -/
theorem coprime_of_denominatorsCoprime {p : ℕ} {Ns : List ℕ}
    (h : denominatorsCoprime p Ns = true) {N : ℕ} (hN : N ∈ Ns) : Nat.Coprime N p := by
  unfold denominatorsCoprime at h
  rw [List.all_eq_true] at h
  exact Nat.eq_of_beq_eq_true (h N hN)

/-- Literals with a checked denominator lie in `A_p`. -/
theorem lit_mem_of_denominatorsCoprime {p : ℕ} {Ns : List ℕ}
    (h : denominatorsCoprime p Ns = true) (A B C D : ℤ) {N : ℕ} (hN : N ∈ Ns) :
    lit A B C D N ∈ pIntegralSubring p :=
  lit_mem_pIntegralSubring A B C D (coprime_of_denominatorsCoprime h hN)

/-- `true` iff every element of the list lies in `A_p` (all reduced coordinate denominators
coprime to `p`). -/
def allPIntegral (p : ℕ) (xs : List Q12) : Bool :=
  xs.all fun x => Nat.gcd x.a.den p == 1 && Nat.gcd x.b.den p == 1 &&
    Nat.gcd x.c.den p == 1 && Nat.gcd x.d.den p == 1

/-- Soundness of `allPIntegral`. -/
theorem mem_of_allPIntegral {p : ℕ} {xs : List Q12} (h : allPIntegral p xs = true)
    {x : Q12} (hx : x ∈ xs) : x ∈ pIntegralSubring p := by
  unfold allPIntegral at h
  rw [List.all_eq_true] at h
  have hx' := h x hx
  simp only [Bool.and_eq_true] at hx'
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ := hx'
  exact ⟨Nat.eq_of_beq_eq_true ha, Nat.eq_of_beq_eq_true hb, Nat.eq_of_beq_eq_true hc,
    Nat.eq_of_beq_eq_true hd⟩

/-! ## Coordinates of `A_p` as `p`-local rationals -/

section Coordinates

variable {p : ℕ}

/-- The rational coordinate `a` of an element of `A_p`, as a `p`-local rational. -/
def coordA (x : pIntegralSubring p) : ratLocalSubring p := ⟨x.1.a, x.2.1⟩
/-- The coordinate `b` (coefficient of `i`). -/
def coordB (x : pIntegralSubring p) : ratLocalSubring p := ⟨x.1.b, x.2.2.1⟩
/-- The coordinate `c` (coefficient of `√3`). -/
def coordC (x : pIntegralSubring p) : ratLocalSubring p := ⟨x.1.c, x.2.2.2.1⟩
/-- The coordinate `d` (coefficient of `i√3`). -/
def coordD (x : pIntegralSubring p) : ratLocalSubring p := ⟨x.1.d, x.2.2.2.2⟩

private theorem coe_three : ((3 : ratLocalSubring p) : ℚ) = 3 := rfl

theorem coordA_add (x y : pIntegralSubring p) : coordA (x + y) = coordA x + coordA y :=
  Subtype.ext rfl
theorem coordB_add (x y : pIntegralSubring p) : coordB (x + y) = coordB x + coordB y :=
  Subtype.ext rfl
theorem coordC_add (x y : pIntegralSubring p) : coordC (x + y) = coordC x + coordC y :=
  Subtype.ext rfl
theorem coordD_add (x y : pIntegralSubring p) : coordD (x + y) = coordD x + coordD y :=
  Subtype.ext rfl

theorem coordA_mul (x y : pIntegralSubring p) :
    coordA (x * y) = coordA x * coordA y - coordB x * coordB y
      + 3 * (coordC x * coordC y) - 3 * (coordD x * coordD y) := by
  apply Subtype.ext
  simp only [Subring.coe_add, AddSubgroupClass.coe_sub, Subring.coe_mul, coe_three]
  rfl
theorem coordB_mul (x y : pIntegralSubring p) :
    coordB (x * y) = coordA x * coordB y + coordB x * coordA y
      + 3 * (coordC x * coordD y + coordD x * coordC y) := by
  apply Subtype.ext
  simp only [Subring.coe_add, Subring.coe_mul, coe_three]
  rfl
theorem coordC_mul (x y : pIntegralSubring p) :
    coordC (x * y) = coordA x * coordC y + coordC x * coordA y
      - (coordB x * coordD y + coordD x * coordB y) := by
  apply Subtype.ext
  simp only [Subring.coe_add, AddSubgroupClass.coe_sub, Subring.coe_mul]
  rfl
theorem coordD_mul (x y : pIntegralSubring p) :
    coordD (x * y) = coordA x * coordD y + coordD x * coordA y
      + coordB x * coordC y + coordC x * coordB y := by
  apply Subtype.ext
  simp only [Subring.coe_add, Subring.coe_mul]
  rfl

end Coordinates

/-! ## Reduction of `A_p` modulo `p` -/

/-- **Reduction `A_p →+* ZMod p`** determined by square roots `ri` of `-1` and `rs` of `3` in
`ZMod p`: `a + b i + c √3 + d i √3 ↦ ā + b̄·ri + c̄·rs + d̄·(ri·rs)`, where `q̄ = ratReduce p q`
is `num(q) · den(q)⁻¹`. Legitimate because every coordinate denominator of an element of `A_p`
maps to a unit of `ZMod p` (`pIntegral_denominators_isUnit`, `ratLocal_den_isUnit`).

Hypotheses: `hp` (`p` prime, for the field structure used in the proofs), `hi : ri * ri = -1`,
`hs : rs * rs = 3` (multiplicativity). -/
def reduceMod (p : ℕ) (hp : p.Prime) (ri rs : ZMod p) (hi : ri * ri = -1) (hs : rs * rs = 3) :
    pIntegralSubring p →+* ZMod p where
  toFun x := ratReduce p x.1.a + ratReduce p x.1.b * ri + ratReduce p x.1.c * rs
    + ratReduce p x.1.d * (ri * rs)
  map_one' := by
    have h1 := (ratReduceHom p hp).map_one
    have h0 := (ratReduceHom p hp).map_zero
    simp only [ratReduceHom_apply, OneMemClass.coe_one, ZeroMemClass.coe_zero] at h1 h0
    show ratReduce p 1 + ratReduce p 0 * ri + ratReduce p 0 * rs + ratReduce p 0 * (ri * rs) = 1
    rw [h1, h0]; ring
  map_zero' := by
    have h0 := (ratReduceHom p hp).map_zero
    simp only [ratReduceHom_apply, ZeroMemClass.coe_zero] at h0
    show ratReduce p 0 + ratReduce p 0 * ri + ratReduce p 0 * rs + ratReduce p 0 * (ri * rs) = 0
    rw [h0]; ring
  map_add' x y := by
    have ha := (ratReduceHom p hp).map_add (coordA x) (coordA y)
    have hb := (ratReduceHom p hp).map_add (coordB x) (coordB y)
    have hc := (ratReduceHom p hp).map_add (coordC x) (coordC y)
    have hd := (ratReduceHom p hp).map_add (coordD x) (coordD y)
    rw [← coordA_add] at ha
    rw [← coordB_add] at hb
    rw [← coordC_add] at hc
    rw [← coordD_add] at hd
    change ratReduce p (x + y).1.a + ratReduce p (x + y).1.b * ri + ratReduce p (x + y).1.c * rs
      + ratReduce p (x + y).1.d * (ri * rs) = _
    change ratReduce p (x + y).1.a = ratReduce p x.1.a + ratReduce p y.1.a at ha
    change ratReduce p (x + y).1.b = ratReduce p x.1.b + ratReduce p y.1.b at hb
    change ratReduce p (x + y).1.c = ratReduce p x.1.c + ratReduce p y.1.c at hc
    change ratReduce p (x + y).1.d = ratReduce p x.1.d + ratReduce p y.1.d at hd
    rw [ha, hb, hc, hd]
    ring
  map_mul' x y := by
    have ha := congrArg (ratReduceHom p hp) (coordA_mul x y)
    have hb := congrArg (ratReduceHom p hp) (coordB_mul x y)
    have hc := congrArg (ratReduceHom p hp) (coordC_mul x y)
    have hd := congrArg (ratReduceHom p hp) (coordD_mul x y)
    simp only [map_add, map_sub, map_mul, map_ofNat] at ha hb hc hd
    change ratReduce p (x * y).1.a = ratReduce p x.1.a * ratReduce p y.1.a
      - ratReduce p x.1.b * ratReduce p y.1.b + 3 * (ratReduce p x.1.c * ratReduce p y.1.c)
      - 3 * (ratReduce p x.1.d * ratReduce p y.1.d) at ha
    change ratReduce p (x * y).1.b = ratReduce p x.1.a * ratReduce p y.1.b
      + ratReduce p x.1.b * ratReduce p y.1.a
      + 3 * (ratReduce p x.1.c * ratReduce p y.1.d + ratReduce p x.1.d * ratReduce p y.1.c) at hb
    change ratReduce p (x * y).1.c = ratReduce p x.1.a * ratReduce p y.1.c
      + ratReduce p x.1.c * ratReduce p y.1.a
      - (ratReduce p x.1.b * ratReduce p y.1.d + ratReduce p x.1.d * ratReduce p y.1.b) at hc
    change ratReduce p (x * y).1.d = ratReduce p x.1.a * ratReduce p y.1.d
      + ratReduce p x.1.d * ratReduce p y.1.a + ratReduce p x.1.b * ratReduce p y.1.c
      + ratReduce p x.1.c * ratReduce p y.1.b at hd
    change ratReduce p (x * y).1.a + ratReduce p (x * y).1.b * ri + ratReduce p (x * y).1.c * rs
      + ratReduce p (x * y).1.d * (ri * rs) =
      (ratReduce p x.1.a + ratReduce p x.1.b * ri + ratReduce p x.1.c * rs
        + ratReduce p x.1.d * (ri * rs)) *
      (ratReduce p y.1.a + ratReduce p y.1.b * ri + ratReduce p y.1.c * rs
        + ratReduce p y.1.d * (ri * rs))
    rw [ha, hb, hc, hd]
    generalize ratReduce p x.1.a = xa
    generalize ratReduce p x.1.b = xb
    generalize ratReduce p x.1.c = xc
    generalize ratReduce p x.1.d = xd
    generalize ratReduce p y.1.a = ya
    generalize ratReduce p y.1.b = yb
    generalize ratReduce p y.1.c = yc
    generalize ratReduce p y.1.d = yd
    linear_combination
      (-(xb * yb + (xb * yd + xd * yb) * rs + xd * yd * (rs * rs))) * hi
      + (-(xc * yc + (xc * yd + xd * yc) * ri - xd * yd)) * hs

theorem reduceMod_apply (p : ℕ) (hp : p.Prime) (ri rs : ZMod p) (hi : ri * ri = -1)
    (hs : rs * rs = 3) (x : pIntegralSubring p) :
    reduceMod p hp ri rs hi hs x = ratReduce p x.1.a + ratReduce p x.1.b * ri
      + ratReduce p x.1.c * rs + ratReduce p x.1.d * (ri * rs) := rfl

/-- The reduction of a literal `(A + B i + C √3 + D i √3) / N`, `N` coprime to `p`. -/
theorem reduceMod_lit (p : ℕ) (hp : p.Prime) (ri rs : ZMod p) (hi : ri * ri = -1)
    (hs : rs * rs = 3) (A B C D : ℤ) {N : ℕ} (hN : Nat.Coprime N p) :
    reduceMod p hp ri rs hi hs ⟨lit A B C D N, lit_mem_pIntegralSubring A B C D hN⟩ =
      ((A : ZMod p) + (B : ZMod p) * ri + (C : ZMod p) * rs + (D : ZMod p) * (ri * rs)) *
        ((N : ℕ) : ZMod p)⁻¹ := by
  rw [reduceMod_apply]
  simp only [lit, ratReduce_mkRat p hp _ hN]
  ring

/-! ## Compatibility with the integer lattice `Z12` -/

/-- `Z12 ⊂ A_p`: integer coordinates have denominator `1`. -/
def integerToPIntegral (p : ℕ) : Z12 →+* pIntegralSubring p :=
  Z12.toQ12.codRestrict (pIntegralSubring p) fun z =>
    ⟨intCast_mem _ z.a, intCast_mem _ z.b, intCast_mem _ z.c, intCast_mem _ z.d⟩

theorem integerToPIntegral_val (p : ℕ) (z : Z12) :
    (integerToPIntegral p z : Q12) = Z12.toQ12 z := rfl

/-- Reducing an element of `Z12` through `A_p` agrees with `Z12.toZMod`. -/
theorem reduceMod_integerToPIntegral (p : ℕ) (hp : p.Prime) (ri rs : ZMod p)
    (hi : ri * ri = -1) (hs : rs * rs = 3) (z : Z12) :
    reduceMod p hp ri rs hi hs (integerToPIntegral p z) = Z12.toZMod p ri rs hi hs z := by
  rw [reduceMod_apply, Z12.toZMod_apply]
  simp only [integerToPIntegral_val, Z12.toQ12_apply, ratReduce_intCast]

/-! ## The inclusion into `ℂ` -/

/-- The inclusion `A_p → Q12 → ℂ`. -/
noncomputable def pIntegralToComplex (p : ℕ) : pIntegralSubring p →+* ℂ :=
  toComplex.comp (pIntegralSubring p).subtype

theorem pIntegralToComplex_apply (p : ℕ) (x : pIntegralSubring p) :
    pIntegralToComplex p x = toComplex x.1 := rfl

/-- The inclusion `A_p → ℂ` is injective. -/
theorem pIntegralToComplex_injective (p : ℕ) : Function.Injective (pIntegralToComplex p) :=
  toComplex_injective.comp Subtype.val_injective

/-! ## The concrete prime `1048573 = 2²⁰ - 3` -/

/-- `A_p` for `p = 1048573`. -/
abbrev PIntegral1048573 : Subring Q12 := pIntegralSubring 1048573

/-- Reduction `A_p → ZMod 1048573`, `i ↦ 365259`, `√3 ↦ 1024`. -/
def reduceMod1048573 : PIntegral1048573 →+* ZMod 1048573 :=
  reduceMod 1048573 Matrix.prime_1048573 365259 1024
    Z12.sqrtNegOne_mod_1048573 Z12.sqrtThree_mod_1048573

/-- `reduceMod1048573` restricted to `Z12` is `Z12.toZMod1048573`. -/
theorem reduceMod1048573_integerToPIntegral (z : Z12) :
    reduceMod1048573 (integerToPIntegral 1048573 z) = Z12.toZMod1048573 z :=
  reduceMod_integerToPIntegral _ _ _ _ _ _ z

/-- `1/2 ∈ A_p`. -/
def halfPIntegral : PIntegral1048573 :=
  ⟨lit 1 0 0 0 2, lit_mem_pIntegralSubring 1 0 0 0 (by decide)⟩
/-- `1/3 ∈ A_p`. -/
def thirdPIntegral : PIntegral1048573 :=
  ⟨lit 1 0 0 0 3, lit_mem_pIntegralSubring 1 0 0 0 (by decide)⟩

/-- `2 · (1/2) = 1` in `A_p` (exact, kernel evaluation over `Q12`). -/
theorem two_mul_halfPIntegral : 2 * halfPIntegral = 1 := by
  apply Subtype.ext
  show (2 : Q12) * lit 1 0 0 0 2 = 1
  decide +kernel

/-- `3 · (1/3) = 1` in `A_p` (exact). -/
theorem three_mul_thirdPIntegral : 3 * thirdPIntegral = 1 := by
  apply Subtype.ext
  show (3 : Q12) * lit 1 0 0 0 3 = 1
  decide +kernel

theorem reduceMod1048573_half : reduceMod1048573 halfPIntegral = (2 : ZMod 1048573)⁻¹ := by
  decide +kernel

theorem reduceMod1048573_third : reduceMod1048573 thirdPIntegral = (3 : ZMod 1048573)⁻¹ := by
  decide +kernel

theorem pIntegralToComplex_half : pIntegralToComplex 1048573 halfPIntegral = 1 / 2 := by
  rw [pIntegralToComplex_apply]
  show toComplex (lit 1 0 0 0 2) = 1 / 2
  rw [toComplex_lit]; push_cast; ring

theorem pIntegralToComplex_third : pIntegralToComplex 1048573 thirdPIntegral = 1 / 3 := by
  rw [pIntegralToComplex_apply]
  show toComplex (lit 1 0 0 0 3) = 1 / 3
  rw [toComplex_lit]; push_cast; ring

end Q12

end

#print axioms Q12.ratLocalSubring
#print axioms Q12.ratLocal_den_isUnit
#print axioms Q12.ratReduceHom
#print axioms Q12.ratReduce_mkRat
#print axioms Q12.pIntegralSubring
#print axioms Q12.mem_pIntegralSubring_iff_not_dvd
#print axioms Q12.pIntegral_denominators_isUnit
#print axioms Q12.lit_mem_pIntegralSubring
#print axioms Q12.coprime_of_denominatorsCoprime
#print axioms Q12.lit_mem_of_denominatorsCoprime
#print axioms Q12.mem_of_allPIntegral
#print axioms Q12.reduceMod
#print axioms Q12.reduceMod_lit
#print axioms Q12.reduceMod_integerToPIntegral
#print axioms Q12.pIntegralToComplex_injective
#print axioms Q12.reduceMod1048573_integerToPIntegral
#print axioms Q12.two_mul_halfPIntegral
#print axioms Q12.three_mul_thirdPIntegral
#print axioms Q12.reduceMod1048573_half
#print axioms Q12.reduceMod1048573_third
#print axioms Q12.pIntegralToComplex_half
#print axioms Q12.pIntegralToComplex_third

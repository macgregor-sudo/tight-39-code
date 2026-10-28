module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Matrix.Basic

/-!
# The exact computable ring `Q12 = ℚ(i, √3)`

An element `⟨a, b, c, d⟩` means `a + b·i + c·√3 + d·i·√3`.
All operations are explicit componentwise formulas over core `Rat`, so the kernel can
evaluate them (`decide +kernel`); `DecidableEq` is derived.

First-party definitions (no borrowed code).
-/

@[expose] public section

@[ext]
structure Q12 where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  deriving DecidableEq

namespace Q12

/-- Literal constructor fixed in `briefs/Q12-LITERAL-FORMAT.md`:
`lit A B C D N = (A + B·i + C·√3 + D·i·√3) / N`. Uses core `mkRat` (normalising). -/
def lit (A B C D : ℤ) (N : ℕ) : Q12 := ⟨mkRat A N, mkRat B N, mkRat C N, mkRat D N⟩

/-- Explicit operations (named, so certificate code can call them without instance search). -/
def add (x y : Q12) : Q12 := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
def neg (x : Q12) : Q12 := ⟨-x.a, -x.b, -x.c, -x.d⟩
def sub (x y : Q12) : Q12 := ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩
def mul (x y : Q12) : Q12 :=
  ⟨x.a * y.a - x.b * y.b + 3 * (x.c * y.c) - 3 * (x.d * y.d),
   x.a * y.b + x.b * y.a + 3 * (x.c * y.d + x.d * y.c),
   x.a * y.c + x.c * y.a - (x.b * y.d + x.d * y.b),
   x.a * y.d + x.d * y.a + x.b * y.c + x.c * y.b⟩

instance : Zero Q12 := ⟨⟨0, 0, 0, 0⟩⟩
instance : One Q12 := ⟨⟨1, 0, 0, 0⟩⟩
instance : Add Q12 := ⟨add⟩
instance : Neg Q12 := ⟨neg⟩
instance : Sub Q12 := ⟨sub⟩
instance : Mul Q12 := ⟨mul⟩
instance : SMul ℕ Q12 := ⟨fun n x => ⟨n * x.a, n * x.b, n * x.c, n * x.d⟩⟩
instance : SMul ℤ Q12 := ⟨fun n x => ⟨n * x.a, n * x.b, n * x.c, n * x.d⟩⟩
instance : SMul ℚ Q12 := ⟨fun q x => ⟨q * x.a, q * x.b, q * x.c, q * x.d⟩⟩
instance : NatCast Q12 := ⟨fun n => ⟨n, 0, 0, 0⟩⟩
instance : IntCast Q12 := ⟨fun n => ⟨n, 0, 0, 0⟩⟩

@[simp] lemma zero_a : (0 : Q12).a = 0 := rfl
@[simp] lemma zero_b : (0 : Q12).b = 0 := rfl
@[simp] lemma zero_c : (0 : Q12).c = 0 := rfl
@[simp] lemma zero_d : (0 : Q12).d = 0 := rfl
@[simp] lemma one_a : (1 : Q12).a = 1 := rfl
@[simp] lemma one_b : (1 : Q12).b = 0 := rfl
@[simp] lemma one_c : (1 : Q12).c = 0 := rfl
@[simp] lemma one_d : (1 : Q12).d = 0 := rfl
@[simp] lemma add_a (x y : Q12) : (x + y).a = x.a + y.a := rfl
@[simp] lemma add_b (x y : Q12) : (x + y).b = x.b + y.b := rfl
@[simp] lemma add_c (x y : Q12) : (x + y).c = x.c + y.c := rfl
@[simp] lemma add_d (x y : Q12) : (x + y).d = x.d + y.d := rfl
@[simp] lemma neg_a (x : Q12) : (-x).a = -x.a := rfl
@[simp] lemma neg_b (x : Q12) : (-x).b = -x.b := rfl
@[simp] lemma neg_c (x : Q12) : (-x).c = -x.c := rfl
@[simp] lemma neg_d (x : Q12) : (-x).d = -x.d := rfl
@[simp] lemma sub_a (x y : Q12) : (x - y).a = x.a - y.a := rfl
@[simp] lemma sub_b (x y : Q12) : (x - y).b = x.b - y.b := rfl
@[simp] lemma sub_c (x y : Q12) : (x - y).c = x.c - y.c := rfl
@[simp] lemma sub_d (x y : Q12) : (x - y).d = x.d - y.d := rfl
@[simp] lemma mul_a (x y : Q12) :
    (x * y).a = x.a * y.a - x.b * y.b + 3 * (x.c * y.c) - 3 * (x.d * y.d) := rfl
@[simp] lemma mul_b (x y : Q12) :
    (x * y).b = x.a * y.b + x.b * y.a + 3 * (x.c * y.d + x.d * y.c) := rfl
@[simp] lemma mul_c (x y : Q12) :
    (x * y).c = x.a * y.c + x.c * y.a - (x.b * y.d + x.d * y.b) := rfl
@[simp] lemma mul_d (x y : Q12) :
    (x * y).d = x.a * y.d + x.d * y.a + x.b * y.c + x.c * y.b := rfl
@[simp] lemma nsmul_a (n : ℕ) (x : Q12) : (n • x).a = n * x.a := rfl
@[simp] lemma nsmul_b (n : ℕ) (x : Q12) : (n • x).b = n * x.b := rfl
@[simp] lemma nsmul_c (n : ℕ) (x : Q12) : (n • x).c = n * x.c := rfl
@[simp] lemma nsmul_d (n : ℕ) (x : Q12) : (n • x).d = n * x.d := rfl
@[simp] lemma zsmul_a (n : ℤ) (x : Q12) : (n • x).a = n * x.a := rfl
@[simp] lemma zsmul_b (n : ℤ) (x : Q12) : (n • x).b = n * x.b := rfl
@[simp] lemma zsmul_c (n : ℤ) (x : Q12) : (n • x).c = n * x.c := rfl
@[simp] lemma zsmul_d (n : ℤ) (x : Q12) : (n • x).d = n * x.d := rfl
@[simp] lemma qsmul_a (q : ℚ) (x : Q12) : (q • x).a = q * x.a := rfl
@[simp] lemma qsmul_b (q : ℚ) (x : Q12) : (q • x).b = q * x.b := rfl
@[simp] lemma qsmul_c (q : ℚ) (x : Q12) : (q • x).c = q * x.c := rfl
@[simp] lemma qsmul_d (q : ℚ) (x : Q12) : (q • x).d = q * x.d := rfl
@[simp] lemma natCast_a (n : ℕ) : (n : Q12).a = n := rfl
@[simp] lemma natCast_b (n : ℕ) : (n : Q12).b = 0 := rfl
@[simp] lemma natCast_c (n : ℕ) : (n : Q12).c = 0 := rfl
@[simp] lemma natCast_d (n : ℕ) : (n : Q12).d = 0 := rfl
@[simp] lemma intCast_a (n : ℤ) : (n : Q12).a = n := rfl
@[simp] lemma intCast_b (n : ℤ) : (n : Q12).b = 0 := rfl
@[simp] lemma intCast_c (n : ℤ) : (n : Q12).c = 0 := rfl
@[simp] lemma intCast_d (n : ℤ) : (n : Q12).d = 0 := rfl

lemma add_def (x y : Q12) : x + y = add x y := rfl
lemma mul_def (x y : Q12) : x * y = mul x y := rfl

instance instCommRing : CommRing Q12 where
  add_assoc := by intros; ext <;> simp <;> ring
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  nsmul := (· • ·)
  nsmul_zero := by intros; ext <;> simp
  nsmul_succ := by intros; ext <;> simp <;> ring
  zsmul := (· • ·)
  zsmul_zero' := by intros; ext <;> simp
  zsmul_succ' := by intros; ext <;> simp <;> ring
  zsmul_neg' := by intros; ext <;> simp [Int.negSucc_eq] <;> ring
  add_comm := by intros; ext <;> simp <;> ring
  mul_assoc := by intros; ext <;> simp <;> ring
  one_mul := by intros; ext <;> simp
  mul_one := by intros; ext <;> simp
  zero_mul := by intros; ext <;> simp
  mul_zero := by intros; ext <;> simp
  left_distrib := by intros; ext <;> simp <;> ring
  right_distrib := by intros; ext <;> simp <;> ring
  neg_add_cancel := by intros; ext <;> simp
  sub_eq_add_neg := by intros; ext <;> simp <;> ring
  natCast_zero := by ext <;> simp
  natCast_succ := by intros; ext <;> simp
  intCast_ofNat := by intros; ext <;> simp
  intCast_negSucc := by intros; ext <;> simp [Int.negSucc_eq]
  mul_comm := by intros; ext <;> simp <;> ring

/-- `ℚ ↪ Q12`. -/
def ofRat : ℚ →+* Q12 where
  toFun q := ⟨q, 0, 0, 0⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' := by intros; ext <;> simp
  map_mul' := by intros; ext <;> simp

instance instAlgebraRat : Algebra ℚ Q12 where
  algebraMap := ofRat
  commutes' := by intros; exact mul_comm _ _
  smul_def' := by intros; ext <;> simp [ofRat]

@[simp] lemma algebraMap_rat (q : ℚ) : algebraMap ℚ Q12 q = ⟨q, 0, 0, 0⟩ := rfl

instance : CharZero Q12 where
  cast_injective := by
    intro m n h
    have := congrArg Q12.a h
    simpa using this

/-! ## Named elements -/

def I : Q12 := ⟨0, 1, 0, 0⟩
def sqrt3 : Q12 := ⟨0, 0, 1, 0⟩
def omega : Q12 := ⟨-1/2, 0, 0, 1/2⟩
/-- The four exact rational unit-circle phases (A, B, C, D order). -/
def phase : Fin 4 → Q12 :=
  ![⟨3/5, 4/5, 0, 0⟩, ⟨5/13, 12/13, 0, 0⟩, ⟨15/17, 8/17, 0, 0⟩, ⟨21/29, 20/29, 0, 0⟩]

theorem I_sq : I ^ 2 = -1 := by decide +kernel
theorem sqrt3_sq : sqrt3 ^ 2 = 3 := by decide +kernel
theorem omega_cube : omega ^ 3 = 1 := by decide +kernel
theorem one_add_omega_add_omega_sq : 1 + omega + omega ^ 2 = 0 := by decide +kernel

/-! ## Galois involutions -/

/-- Complex conjugation `i ↦ -i` (fixes `√3`). -/
def conj : Q12 →+* Q12 where
  toFun x := ⟨x.a, -x.b, x.c, -x.d⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' := by intros; ext <;> simp <;> ring
  map_mul' := by intros; ext <;> simp <;> ring

/-- `√3 ↦ -√3` (fixes `i`). -/
def galois : Q12 →+* Q12 where
  toFun x := ⟨x.a, x.b, -x.c, -x.d⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' := by intros; ext <;> simp <;> ring
  map_mul' := by intros; ext <;> simp <;> ring

@[simp] lemma conj_apply (x : Q12) : conj x = ⟨x.a, -x.b, x.c, -x.d⟩ := rfl
@[simp] lemma galois_apply (x : Q12) : galois x = ⟨x.a, x.b, -x.c, -x.d⟩ := rfl

theorem phase_mul_conj (k : Fin 4) : phase k * conj (phase k) = 1 := by
  revert k; decide +kernel

theorem conj_omega : conj omega = omega ^ 2 := by decide +kernel

/-! ## The embedding into `ℂ` -/

/-- `x ↦ a + b i + c √3 + d i √3`. -/
noncomputable def toComplex : Q12 →+* ℂ where
  toFun x := (x.a : ℂ) + (x.b : ℂ) * Complex.I + (x.c : ℂ) * (Real.sqrt 3 : ℂ)
    + (x.d : ℂ) * Complex.I * (Real.sqrt 3 : ℂ)
  map_one' := by simp
  map_zero' := by simp
  map_add' := by intros; simp; ring
  map_mul' := by
    intro x y
    have hs : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    simp only [mul_a, mul_b, mul_c, mul_d]
    push_cast
    linear_combination
      (-((x.c : ℂ) * y.c + ((x.c : ℂ) * y.d + (x.d : ℂ) * y.c) * Complex.I
          + (x.d : ℂ) * y.d * Complex.I ^ 2)) * hs
      + (-((x.b : ℂ) * y.b + ((x.b : ℂ) * y.d + (x.d : ℂ) * y.b) * (Real.sqrt 3 : ℂ)
          + 3 * (x.d : ℂ) * y.d)) * hI

lemma toComplex_apply (x : Q12) : toComplex x = (x.a : ℂ) + (x.b : ℂ) * Complex.I
    + (x.c : ℂ) * (Real.sqrt 3 : ℂ) + (x.d : ℂ) * Complex.I * (Real.sqrt 3 : ℂ) := rfl

theorem toComplex_I : toComplex I = Complex.I := by simp [toComplex_apply, I]
theorem toComplex_sqrt3 : toComplex sqrt3 = (Real.sqrt 3 : ℂ) := by
  simp [toComplex_apply, sqrt3]

/-- Matches `omega` of the native model (NativeIncludedQuartetReadouts.lean line 1923). -/
theorem toComplex_omega :
    toComplex omega = (-1 + Complex.I * (Real.sqrt 3 : ℂ)) / 2 := by
  simp only [toComplex_apply, omega]; push_cast; ring

/-- Matches `exactPhases` (NativeExactCKMConfiguration.lean lines 43–46) entrywise;
`exactPhases k` unfolds to the right-hand side by `rfl`. -/
theorem toComplex_phase (k : Fin 4) :
    toComplex (phase k) = (![(3 + 4 * Complex.I) / 5, (5 + 12 * Complex.I) / 13,
      (15 + 8 * Complex.I) / 17, (21 + 20 * Complex.I) / 29] : Fin 4 → ℂ) k := by
  fin_cases k <;> simp [toComplex_apply, phase] <;> ring

theorem toComplex_phase_fun :
    (fun k => toComplex (phase k)) = (![(3 + 4 * Complex.I) / 5, (5 + 12 * Complex.I) / 13,
      (15 + 8 * Complex.I) / 17, (21 + 20 * Complex.I) / 29] : Fin 4 → ℂ) :=
  funext toComplex_phase

theorem toComplex_conj (x : Q12) : toComplex (conj x) = starRingEnd ℂ (toComplex x) := by
  have hs : starRingEnd ℂ ((Real.sqrt 3 : ℝ) : ℂ) = ((Real.sqrt 3 : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  simp only [toComplex_apply, conj_apply, map_add, map_mul, map_ratCast, hs,
    Complex.conj_I]
  push_cast; ring

theorem toComplex_real (a c : ℚ) :
    toComplex ⟨a, 0, c, 0⟩ = (((a : ℝ) + (c : ℝ) * Real.sqrt 3 : ℝ) : ℂ) := by
  simp [toComplex_apply]

theorem toComplex_ofRat (q : ℚ) : toComplex (ofRat q) = (q : ℂ) := by
  simp [toComplex_apply, ofRat]

theorem toComplex_lit (A B C D : ℤ) (N : ℕ) :
    toComplex (lit A B C D N) = ((A : ℂ) + B * Complex.I + C * (Real.sqrt 3 : ℂ)
      + D * Complex.I * (Real.sqrt 3 : ℂ)) / N := by
  simp only [toComplex_apply, lit, Rat.mkRat_eq_div]
  push_cast; ring

/-- `3` is not a rational square. -/
theorem rat_mul_self_ne_three (q : ℚ) : q * q ≠ 3 := by
  intro h
  have hn : q.num * q.num = 3 := by
    have := Rat.mul_self_num q; rw [h] at this; exact this.symm
  have h3 : q.num.natAbs * q.num.natAbs = 3 := by
    have := congrArg Int.natAbs hn; simpa [Int.natAbs_mul] using this
  rcases Nat.lt_or_ge q.num.natAbs 2 with h2 | h2
  · have := Nat.mul_le_mul (Nat.le_of_lt_succ h2) (Nat.le_of_lt_succ h2); omega
  · have := Nat.mul_le_mul h2 h2; omega

/-- `1, √3` are `ℚ`-linearly independent in `ℝ`. -/
theorem rat_add_rat_mul_sqrt3_eq_zero {a c : ℚ}
    (h : (a : ℝ) + (c : ℝ) * Real.sqrt 3 = 0) : a = 0 ∧ c = 0 := by
  by_cases hc : c = 0
  · subst hc
    simp only [Rat.cast_zero, zero_mul, add_zero, Rat.cast_eq_zero] at h
    exact ⟨h, rfl⟩
  · exfalso
    have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    have hs : Real.sqrt 3 = ((-a / c : ℚ) : ℝ) := by
      push_cast; field_simp; linarith
    have hsq : (Real.sqrt 3) * (Real.sqrt 3) = 3 := Real.mul_self_sqrt (by norm_num)
    rw [hs] at hsq
    apply rat_mul_self_ne_three (-a / c)
    exact_mod_cast hsq

theorem toComplex_eq_zero_iff (x : Q12) : toComplex x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp [toComplex_apply] at hre him
    obtain ⟨ha, hc⟩ := rat_add_rat_mul_sqrt3_eq_zero hre
    obtain ⟨hb, hd⟩ := rat_add_rat_mul_sqrt3_eq_zero him
    ext <;> simp [ha, hb, hc, hd]
  · rintro rfl; exact map_zero _

theorem toComplex_injective : Function.Injective toComplex :=
  (injective_iff_map_eq_zero toComplex).2 fun x hx => (toComplex_eq_zero_iff x).1 hx

theorem toComplex_ne_zero {x : Q12} (hx : x ≠ 0) : toComplex x ≠ 0 :=
  fun h => hx ((toComplex_eq_zero_iff x).1 h)

/-- `ℂ` as a `Q12`-algebra. Scoped: `open Q12` to use it. There is no other
`Algebra Q12 ℂ` in Mathlib, but keep it scoped so that `Algebra ℚ ℂ` (Mathlib's
`algebraRat`) and the tower `ℚ → Q12 → ℂ` are never both found by unification
in files that do not ask for it. -/
noncomputable scoped instance algebraComplex : Algebra Q12 ℂ := toComplex.toAlgebra

end Q12

end

#print axioms Q12.instCommRing
#print axioms Q12.I_sq
#print axioms Q12.sqrt3_sq
#print axioms Q12.omega_cube
#print axioms Q12.one_add_omega_add_omega_sq
#print axioms Q12.phase_mul_conj
#print axioms Q12.conj_omega
#print axioms Q12.toComplex
#print axioms Q12.toComplex_omega
#print axioms Q12.toComplex_phase
#print axioms Q12.toComplex_conj
#print axioms Q12.toComplex_real
#print axioms Q12.toComplex_lit
#print axioms Q12.toComplex_injective
#print axioms Q12.toComplex_eq_zero_iff

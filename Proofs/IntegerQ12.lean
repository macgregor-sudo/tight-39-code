module

public import Q12
public import Mathlib.Data.ZMod.Basic

/-!
# The integer lattice `Z12 ⊂ Q12` and its reductions modulo primes `p ≡ 1 (mod 12)`

An element `⟨a, b, c, d⟩ : Z12` with `a b c d : ℤ` means `a + b·i + c·√3 + d·i·√3`.
Multiplication uses the same componentwise formulas as `Q12` (from `i² = -1`, `√3² = 3`).

* `Z12.toQ12 : Z12 →+* Q12` is the inclusion (injective).
* `Z12.toZMod p ri rs hi hs : Z12 →+* ZMod p` sends `i ↦ ri`, `√3 ↦ rs`, for any chosen
  square roots `ri² = -1`, `rs² = 3` in `ZMod p`. Such roots exist exactly when both `-1` and `3`
  are squares mod `p`, e.g. for every prime `p ≡ 1 (mod 12)`.
* Concrete reductions `Z12.toZMod999049` and `Z12.toZMod1048573`; the root equations are
  checked by `decide +kernel`.

These maps are used only for *nonvanishing* transfer (a determinant that is nonzero mod `p`
is nonzero in `Z12`); no equality over `Z12` is ever inferred from a modular computation.

First-party definitions (no borrowed code).
-/

@[expose] public section

/-- The ring `ℤ[i, √3]` written in the basis `1, i, √3, i√3`. -/
@[ext]
structure Z12 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq

namespace Z12

/-- Componentwise addition. -/
def add (x y : Z12) : Z12 := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
/-- Componentwise negation. -/
def neg (x : Z12) : Z12 := ⟨-x.a, -x.b, -x.c, -x.d⟩
/-- Componentwise subtraction. -/
def sub (x y : Z12) : Z12 := ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩
/-- Multiplication, using `i² = -1`, `√3² = 3` (identical formulas to `Q12.mul`). -/
def mul (x y : Z12) : Z12 :=
  ⟨x.a * y.a - x.b * y.b + 3 * (x.c * y.c) - 3 * (x.d * y.d),
   x.a * y.b + x.b * y.a + 3 * (x.c * y.d + x.d * y.c),
   x.a * y.c + x.c * y.a - (x.b * y.d + x.d * y.b),
   x.a * y.d + x.d * y.a + x.b * y.c + x.c * y.b⟩

instance : Zero Z12 := ⟨⟨0, 0, 0, 0⟩⟩
instance : One Z12 := ⟨⟨1, 0, 0, 0⟩⟩
instance : Add Z12 := ⟨add⟩
instance : Neg Z12 := ⟨neg⟩
instance : Sub Z12 := ⟨sub⟩
instance : Mul Z12 := ⟨mul⟩
instance : SMul ℕ Z12 := ⟨fun n x => ⟨n * x.a, n * x.b, n * x.c, n * x.d⟩⟩
instance : SMul ℤ Z12 := ⟨fun n x => ⟨n * x.a, n * x.b, n * x.c, n * x.d⟩⟩
instance : NatCast Z12 := ⟨fun n => ⟨n, 0, 0, 0⟩⟩
instance : IntCast Z12 := ⟨fun n => ⟨n, 0, 0, 0⟩⟩

@[simp] lemma zero_a : (0 : Z12).a = 0 := rfl
@[simp] lemma zero_b : (0 : Z12).b = 0 := rfl
@[simp] lemma zero_c : (0 : Z12).c = 0 := rfl
@[simp] lemma zero_d : (0 : Z12).d = 0 := rfl
@[simp] lemma one_a : (1 : Z12).a = 1 := rfl
@[simp] lemma one_b : (1 : Z12).b = 0 := rfl
@[simp] lemma one_c : (1 : Z12).c = 0 := rfl
@[simp] lemma one_d : (1 : Z12).d = 0 := rfl
@[simp] lemma add_a (x y : Z12) : (x + y).a = x.a + y.a := rfl
@[simp] lemma add_b (x y : Z12) : (x + y).b = x.b + y.b := rfl
@[simp] lemma add_c (x y : Z12) : (x + y).c = x.c + y.c := rfl
@[simp] lemma add_d (x y : Z12) : (x + y).d = x.d + y.d := rfl
@[simp] lemma neg_a (x : Z12) : (-x).a = -x.a := rfl
@[simp] lemma neg_b (x : Z12) : (-x).b = -x.b := rfl
@[simp] lemma neg_c (x : Z12) : (-x).c = -x.c := rfl
@[simp] lemma neg_d (x : Z12) : (-x).d = -x.d := rfl
@[simp] lemma sub_a (x y : Z12) : (x - y).a = x.a - y.a := rfl
@[simp] lemma sub_b (x y : Z12) : (x - y).b = x.b - y.b := rfl
@[simp] lemma sub_c (x y : Z12) : (x - y).c = x.c - y.c := rfl
@[simp] lemma sub_d (x y : Z12) : (x - y).d = x.d - y.d := rfl
@[simp] lemma mul_a (x y : Z12) :
    (x * y).a = x.a * y.a - x.b * y.b + 3 * (x.c * y.c) - 3 * (x.d * y.d) := rfl
@[simp] lemma mul_b (x y : Z12) :
    (x * y).b = x.a * y.b + x.b * y.a + 3 * (x.c * y.d + x.d * y.c) := rfl
@[simp] lemma mul_c (x y : Z12) :
    (x * y).c = x.a * y.c + x.c * y.a - (x.b * y.d + x.d * y.b) := rfl
@[simp] lemma mul_d (x y : Z12) :
    (x * y).d = x.a * y.d + x.d * y.a + x.b * y.c + x.c * y.b := rfl
@[simp] lemma nsmul_a (n : ℕ) (x : Z12) : (n • x).a = n * x.a := rfl
@[simp] lemma nsmul_b (n : ℕ) (x : Z12) : (n • x).b = n * x.b := rfl
@[simp] lemma nsmul_c (n : ℕ) (x : Z12) : (n • x).c = n * x.c := rfl
@[simp] lemma nsmul_d (n : ℕ) (x : Z12) : (n • x).d = n * x.d := rfl
@[simp] lemma zsmul_a (n : ℤ) (x : Z12) : (n • x).a = n * x.a := rfl
@[simp] lemma zsmul_b (n : ℤ) (x : Z12) : (n • x).b = n * x.b := rfl
@[simp] lemma zsmul_c (n : ℤ) (x : Z12) : (n • x).c = n * x.c := rfl
@[simp] lemma zsmul_d (n : ℤ) (x : Z12) : (n • x).d = n * x.d := rfl
@[simp] lemma natCast_a (n : ℕ) : (n : Z12).a = n := rfl
@[simp] lemma natCast_b (n : ℕ) : (n : Z12).b = 0 := rfl
@[simp] lemma natCast_c (n : ℕ) : (n : Z12).c = 0 := rfl
@[simp] lemma natCast_d (n : ℕ) : (n : Z12).d = 0 := rfl
@[simp] lemma intCast_a (n : ℤ) : (n : Z12).a = n := rfl
@[simp] lemma intCast_b (n : ℤ) : (n : Z12).b = 0 := rfl
@[simp] lemma intCast_c (n : ℤ) : (n : Z12).c = 0 := rfl
@[simp] lemma intCast_d (n : ℤ) : (n : Z12).d = 0 := rfl

instance instCommRing : CommRing Z12 where
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

/-! ## The inclusion into `Q12` -/

/-- The inclusion `ℤ[i, √3] ↪ ℚ(i, √3)`, componentwise `ℤ ↪ ℚ`. -/
def toQ12 : Z12 →+* Q12 where
  toFun x := ⟨x.a, x.b, x.c, x.d⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' := by intros; ext <;> simp
  map_mul' := by intros; ext <;> simp

@[simp] lemma toQ12_apply (x : Z12) : toQ12 x = ⟨x.a, x.b, x.c, x.d⟩ := rfl

/-- The inclusion `Z12 → Q12` is injective. -/
theorem toQ12_injective : Function.Injective toQ12 := by
  intro x y h
  simp only [toQ12_apply, Q12.mk.injEq, Int.cast_inj] at h
  obtain ⟨ha, hb, hc, hd⟩ := h
  ext <;> assumption

/-! ## Reduction modulo `p` -/

/-- Reduction `Z12 → ZMod p` determined by a choice of square roots `ri` of `-1` and `rs` of `3`
in `ZMod p`: `a + b i + c √3 + d i √3 ↦ a + b·ri + c·rs + d·ri·rs`.

Hypotheses: `hi : ri * ri = -1`, `hs : rs * rs = 3`. These make the map multiplicative. -/
def toZMod (p : ℕ) (ri rs : ZMod p) (hi : ri * ri = -1) (hs : rs * rs = 3) : Z12 →+* ZMod p where
  toFun x := (x.a : ZMod p) + (x.b : ZMod p) * ri + (x.c : ZMod p) * rs
    + (x.d : ZMod p) * (ri * rs)
  map_one' := by simp
  map_zero' := by simp
  map_add' := by intros; simp; ring
  map_mul' := by
    intro x y
    simp only [mul_a, mul_b, mul_c, mul_d]
    push_cast
    linear_combination
      (-((x.b : ZMod p) * y.b + ((x.b : ZMod p) * y.d + (x.d : ZMod p) * y.b) * rs
          + (x.d : ZMod p) * y.d * (rs * rs))) * hi
      + (-((x.c : ZMod p) * y.c + ((x.c : ZMod p) * y.d + (x.d : ZMod p) * y.c) * ri
          - (x.d : ZMod p) * y.d)) * hs

lemma toZMod_apply (p : ℕ) (ri rs : ZMod p) (hi : ri * ri = -1) (hs : rs * rs = 3) (x : Z12) :
    toZMod p ri rs hi hs x = (x.a : ZMod p) + (x.b : ZMod p) * ri + (x.c : ZMod p) * rs
      + (x.d : ZMod p) * (ri * rs) := rfl

/-! ### The prime `p = 999049` -/

/-- `387724` is a square root of `-1` modulo `999049`. -/
theorem sqrtNegOne_mod_999049 : (387724 : ZMod 999049) * 387724 = -1 := by decide +kernel

/-- `174012` is a square root of `3` modulo `999049`. -/
theorem sqrtThree_mod_999049 : (174012 : ZMod 999049) * 174012 = 3 := by decide +kernel

/-- Reduction `Z12 → ZMod 999049` with `i ↦ 387724`, `√3 ↦ 174012`. -/
def toZMod999049 : Z12 →+* ZMod 999049 :=
  toZMod 999049 387724 174012 sqrtNegOne_mod_999049 sqrtThree_mod_999049

/-! ### The prime `p = 1048573 = 2²⁰ - 3` -/

/-- `365259` is a square root of `-1` modulo `1048573`. -/
theorem sqrtNegOne_mod_1048573 : (365259 : ZMod 1048573) * 365259 = -1 := by decide +kernel

/-- `1024 = 2¹⁰` is a square root of `3` modulo `1048573 = 2²⁰ - 3`. -/
theorem sqrtThree_mod_1048573 : (1024 : ZMod 1048573) * 1024 = 3 := by decide +kernel

/-- Reduction `Z12 → ZMod 1048573` with `i ↦ 365259`, `√3 ↦ 1024`. -/
def toZMod1048573 : Z12 →+* ZMod 1048573 :=
  toZMod 1048573 365259 1024 sqrtNegOne_mod_1048573 sqrtThree_mod_1048573

/-- Sanity check of the reduction map on a sample product, evaluated by the kernel. -/
example : toZMod999049 (⟨1, 2, -3, 4⟩ * ⟨-5, 6, 7, -8⟩) =
    toZMod999049 ⟨1, 2, -3, 4⟩ * toZMod999049 ⟨-5, 6, 7, -8⟩ := by decide +kernel

end Z12

end

#print axioms Z12.instCommRing
#print axioms Z12.toQ12
#print axioms Z12.toQ12_injective
#print axioms Z12.toZMod
#print axioms Z12.sqrtNegOne_mod_999049
#print axioms Z12.sqrtThree_mod_999049
#print axioms Z12.toZMod999049
#print axioms Z12.sqrtNegOne_mod_1048573
#print axioms Z12.sqrtThree_mod_1048573
#print axioms Z12.toZMod1048573

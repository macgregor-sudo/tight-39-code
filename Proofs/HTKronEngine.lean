module

public import NativeHIntegerCompute
public import NativeTWeights

@[expose] public section

/-!
# Kronecker point-evaluation engine for the native H/T reproduction (computation only)

First-party code. Exact arithmetic in `ℤ[i, √3]`
(`Z4`, four integer coordinates in the basis `1, i, √3, i√3`), a dense list holding the
native point `V(y*)` built from the ORIGINAL `d6Entries`/`eigenIndex`, and evaluators that read
the ORIGINAL `rawEntries`, `labelShape`, literal denominators and Book term tables. No literal
data is transcribed here. Every function is written with direct `Int`/`Nat` operations or raw
recursors so that the kernel evaluates it with GMP-backed literal arithmetic.
Interpretation lemmas are in `HTKronSemantics`.
-/

set_option autoImplicit false

namespace Option2.NativeStress.HTRouteKron

open QuarticCertificate.RowBridge BookHT.TangentCoordinates BookHT.Dictionary
open ConfigurationResidualIndices

/-- `a + b i + c √3 + d i √3` with integer coordinates. -/
@[ext] structure Z4 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving DecidableEq

namespace Z4

def zero : Z4 := ⟨0, 0, 0, 0⟩
def one : Z4 := ⟨1, 0, 0, 0⟩
def add (x y : Z4) : Z4 := ⟨Int.add x.a y.a, Int.add x.b y.b, Int.add x.c y.c, Int.add x.d y.d⟩
def neg (x : Z4) : Z4 := ⟨Int.neg x.a, Int.neg x.b, Int.neg x.c, Int.neg x.d⟩
def mul (x y : Z4) : Z4 :=
  ⟨Int.sub (Int.add (Int.mul x.a y.a) (Int.mul 3 (Int.mul x.c y.c)))
      (Int.add (Int.mul x.b y.b) (Int.mul 3 (Int.mul x.d y.d))),
   Int.add (Int.add (Int.mul x.a y.b) (Int.mul x.b y.a))
      (Int.mul 3 (Int.add (Int.mul x.c y.d) (Int.mul x.d y.c))),
   Int.sub (Int.add (Int.mul x.a y.c) (Int.mul x.c y.a))
      (Int.add (Int.mul x.b y.d) (Int.mul x.d y.b)),
   Int.add (Int.add (Int.mul x.a y.d) (Int.mul x.d y.a))
      (Int.add (Int.mul x.b y.c) (Int.mul x.c y.b))⟩
def smul (n : ℤ) (x : Z4) : Z4 := ⟨Int.mul n x.a, Int.mul n x.b, Int.mul n x.c, Int.mul n x.d⟩
def conj (x : Z4) : Z4 := ⟨x.a, Int.neg x.b, x.c, Int.neg x.d⟩
def ofInt (n : ℤ) : Z4 := ⟨n, 0, 0, 0⟩

@[simp] lemma add_a (x y : Z4) : (add x y).a = x.a + y.a := rfl
@[simp] lemma add_b (x y : Z4) : (add x y).b = x.b + y.b := rfl
@[simp] lemma add_c (x y : Z4) : (add x y).c = x.c + y.c := rfl
@[simp] lemma add_d (x y : Z4) : (add x y).d = x.d + y.d := rfl
@[simp] lemma neg_a (x : Z4) : (neg x).a = -x.a := rfl
@[simp] lemma neg_b (x : Z4) : (neg x).b = -x.b := rfl
@[simp] lemma neg_c (x : Z4) : (neg x).c = -x.c := rfl
@[simp] lemma neg_d (x : Z4) : (neg x).d = -x.d := rfl
@[simp] lemma mul_a (x y : Z4) :
    (mul x y).a = x.a * y.a + 3 * (x.c * y.c) - (x.b * y.b + 3 * (x.d * y.d)) := rfl
@[simp] lemma mul_b (x y : Z4) :
    (mul x y).b = x.a * y.b + x.b * y.a + 3 * (x.c * y.d + x.d * y.c) := rfl
@[simp] lemma mul_c (x y : Z4) :
    (mul x y).c = x.a * y.c + x.c * y.a - (x.b * y.d + x.d * y.b) := rfl
@[simp] lemma mul_d (x y : Z4) :
    (mul x y).d = x.a * y.d + x.d * y.a + (x.b * y.c + x.c * y.b) := rfl
@[simp] lemma smul_a (n : ℤ) (x : Z4) : (smul n x).a = n * x.a := rfl
@[simp] lemma smul_b (n : ℤ) (x : Z4) : (smul n x).b = n * x.b := rfl
@[simp] lemma smul_c (n : ℤ) (x : Z4) : (smul n x).c = n * x.c := rfl
@[simp] lemma smul_d (n : ℤ) (x : Z4) : (smul n x).d = n * x.d := rfl
@[simp] lemma zero_a : zero.a = 0 := rfl
@[simp] lemma zero_b : zero.b = 0 := rfl
@[simp] lemma zero_c : zero.c = 0 := rfl
@[simp] lemma zero_d : zero.d = 0 := rfl
@[simp] lemma one_a : one.a = 1 := rfl
@[simp] lemma one_b : one.b = 0 := rfl
@[simp] lemma one_c : one.c = 0 := rfl
@[simp] lemma one_d : one.d = 0 := rfl

instance : Zero Z4 := ⟨zero⟩
instance : One Z4 := ⟨one⟩
instance : Add Z4 := ⟨add⟩
instance : Neg Z4 := ⟨neg⟩
instance : Sub Z4 := ⟨fun x y => add x (neg y)⟩
instance : Mul Z4 := ⟨mul⟩
instance : SMul ℕ Z4 := ⟨fun n x => smul n x⟩
instance : SMul ℤ Z4 := ⟨smul⟩
instance : NatCast Z4 := ⟨fun n => ofInt n⟩
instance : IntCast Z4 := ⟨ofInt⟩

@[simp] lemma zero_a' : (0 : Z4).a = 0 := rfl
@[simp] lemma zero_b' : (0 : Z4).b = 0 := rfl
@[simp] lemma zero_c' : (0 : Z4).c = 0 := rfl
@[simp] lemma zero_d' : (0 : Z4).d = 0 := rfl
@[simp] lemma one_a' : (1 : Z4).a = 1 := rfl
@[simp] lemma one_b' : (1 : Z4).b = 0 := rfl
@[simp] lemma one_c' : (1 : Z4).c = 0 := rfl
@[simp] lemma one_d' : (1 : Z4).d = 0 := rfl
@[simp] lemma hadd_a (x y : Z4) : (x + y).a = x.a + y.a := rfl
@[simp] lemma hadd_b (x y : Z4) : (x + y).b = x.b + y.b := rfl
@[simp] lemma hadd_c (x y : Z4) : (x + y).c = x.c + y.c := rfl
@[simp] lemma hadd_d (x y : Z4) : (x + y).d = x.d + y.d := rfl
@[simp] lemma hneg_a (x : Z4) : (-x).a = -x.a := rfl
@[simp] lemma hneg_b (x : Z4) : (-x).b = -x.b := rfl
@[simp] lemma hneg_c (x : Z4) : (-x).c = -x.c := rfl
@[simp] lemma hneg_d (x : Z4) : (-x).d = -x.d := rfl
@[simp] lemma hsub_a (x y : Z4) : (x - y).a = x.a - y.a := by
  show x.a + -y.a = x.a - y.a; ring
@[simp] lemma hsub_b (x y : Z4) : (x - y).b = x.b - y.b := by
  show x.b + -y.b = x.b - y.b; ring
@[simp] lemma hsub_c (x y : Z4) : (x - y).c = x.c - y.c := by
  show x.c + -y.c = x.c - y.c; ring
@[simp] lemma hsub_d (x y : Z4) : (x - y).d = x.d - y.d := by
  show x.d + -y.d = x.d - y.d; ring
@[simp] lemma hmul_a (x y : Z4) :
    (x * y).a = x.a * y.a + 3 * (x.c * y.c) - (x.b * y.b + 3 * (x.d * y.d)) := rfl
@[simp] lemma hmul_b (x y : Z4) :
    (x * y).b = x.a * y.b + x.b * y.a + 3 * (x.c * y.d + x.d * y.c) := rfl
@[simp] lemma hmul_c (x y : Z4) :
    (x * y).c = x.a * y.c + x.c * y.a - (x.b * y.d + x.d * y.b) := rfl
@[simp] lemma hmul_d (x y : Z4) :
    (x * y).d = x.a * y.d + x.d * y.a + (x.b * y.c + x.c * y.b) := rfl
@[simp] lemma nsmul_a' (n : ℕ) (x : Z4) : (n • x).a = n * x.a := rfl
@[simp] lemma nsmul_b' (n : ℕ) (x : Z4) : (n • x).b = n * x.b := rfl
@[simp] lemma nsmul_c' (n : ℕ) (x : Z4) : (n • x).c = n * x.c := rfl
@[simp] lemma nsmul_d' (n : ℕ) (x : Z4) : (n • x).d = n * x.d := rfl
@[simp] lemma zsmul_a' (n : ℤ) (x : Z4) : (n • x).a = n * x.a := rfl
@[simp] lemma zsmul_b' (n : ℤ) (x : Z4) : (n • x).b = n * x.b := rfl
@[simp] lemma zsmul_c' (n : ℤ) (x : Z4) : (n • x).c = n * x.c := rfl
@[simp] lemma zsmul_d' (n : ℤ) (x : Z4) : (n • x).d = n * x.d := rfl
@[simp] lemma natCast_a' (n : ℕ) : (n : Z4).a = n := rfl
@[simp] lemma natCast_b' (n : ℕ) : (n : Z4).b = 0 := rfl
@[simp] lemma natCast_c' (n : ℕ) : (n : Z4).c = 0 := rfl
@[simp] lemma natCast_d' (n : ℕ) : (n : Z4).d = 0 := rfl
@[simp] lemma intCast_a' (n : ℤ) : (n : Z4).a = n := rfl
@[simp] lemma intCast_b' (n : ℤ) : (n : Z4).b = 0 := rfl
@[simp] lemma intCast_c' (n : ℤ) : (n : Z4).c = 0 := rfl
@[simp] lemma intCast_d' (n : ℤ) : (n : Z4).d = 0 := rfl

instance instCommRing : CommRing Z4 where
  add_assoc := by intros; ext <;> simp <;> ring
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp <;> ring
  mul_assoc := by intros; ext <;> simp <;> ring
  one_mul := by intros; ext <;> simp
  mul_one := by intros; ext <;> simp
  zero_mul := by intros; ext <;> simp
  mul_zero := by intros; ext <;> simp
  left_distrib := by intros; ext <;> simp <;> ring
  right_distrib := by intros; ext <;> simp <;> ring
  mul_comm := by intros; ext <;> simp <;> ring
  neg_add_cancel := by intros; ext <;> simp
  sub_eq_add_neg := by intros; rfl
  nsmul := (· • ·)
  nsmul_zero := by intros; ext <;> simp
  nsmul_succ := by intros; ext <;> simp <;> ring
  zsmul := (· • ·)
  zsmul_zero' := by intros; ext <;> simp
  zsmul_succ' := by intros; ext <;> simp <;> ring
  zsmul_neg' := by intros; ext <;> simp [Int.negSucc_eq] <;> ring
  natCast_zero := by ext <;> simp
  natCast_succ := by intros; ext <;> simp
  intCast_ofNat := by intros; ext <;> simp
  intCast_negSucc := by intros; ext <;> simp [Int.negSucc_eq]

end Z4

/-- Original integer coordinate tuple of a D6 entry, or of a native weight literal. -/
def ofCoeff (q : Coeff) : Z4 := ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩
def ofLit (c : NativeH.Literal) : Z4 := ⟨c.A, c.B, c.C, c.D⟩

/-- The H orientation (conjugation, sign) on a weight; T uses `⟨_, false, false⟩`. -/
def orient (s : NativeH.HSpec) (x : Z4) : Z4 :=
  let z := cond s.conjugated (Z4.conj x) x
  cond s.negated (Z4.neg z) z

/-! ## The native point `V(y)` from the original columns -/

/-- Add `y * entry` into a dense accumulator, walking the accumulator from coordinate `r`.
Each original column is strictly increasing in its row index (checked by the kernel in
`HTKronSemantics`), so one simultaneous pass places every entry. -/
noncomputable def addCol (y : ℤ) (acc : List Z4) : List Entry → ℕ → List Z4 :=
  List.rec (motive := fun _ => List Entry → ℕ → List Z4) (fun _ _ => [])
    (fun x xs ih es r => List.casesOn (motive := fun _ => List Z4) es (x :: xs)
      (fun e es' => Bool.rec (motive := fun _ => List Z4) (x :: ih es (Nat.succ r))
        (Z4.add x (Z4.smul y (ofCoeff e.2)) :: ih es' (Nat.succ r)) (Nat.beq e.1.val r)))
    acc

/-- All 24 eigencolumns, `eigenIndex` exactly as supplied, at an integer point `ys`, as a dense
list of the 1053 coordinates. -/
noncomputable def densePoint (ys : Fin 24 → ℤ) : List Z4 :=
  (List.finRange 24).foldl (fun acc j => addCol (ys j) acc (d6Entries (eigenIndex j)) 0)
    (List.replicate 1053 Z4.zero)

/-- Split into the 39 native points (label-first layout `27 p + k`). -/
def blocks (l : List Z4) : List (List Z4) :=
  Nat.rec (motive := fun _ => List Z4 → List (List Z4)) (fun _ => [])
    (fun _ ih l => l.take 27 :: ih (l.drop 27)) 39 l

/-! ## Evaluators reading the original rows -/

/-- Literal common denominator of an entry list (same fold as `commonDenominator`). -/
def denLcm (es : List NativeH.Entry) : ℕ := (es.map fun e => e.coefficient.denominator).foldr Nat.lcm 1

/-- Denominator-cleared weight; the factor `2` on non-idempotency rows absorbs the native half. -/
def weight (d : ℕ) (s : NativeH.HSpec) (e : NativeH.Entry) : Z4 :=
  Z4.smul (((d / e.coefficient.denominator) * (if (labelShape e.label).halfScaled then 1 else 2) : ℕ) : ℤ)
    (orient s (ofLit e.coefficient))

/-- `true` exactly for `0`; read as four integer tests. -/
def Z4.isZero (x : Z4) : Bool :=
  Nat.beq x.a.natAbs 0 && Nat.beq x.b.natAbs 0 && Nat.beq x.c.natAbs 0 && Nat.beq x.d.natAbs 0

/-- `x + acc`, returning `acc` itself when `x = 0` (no new literals for zero summands). -/
def addSkip (x acc : Z4) : Z4 := cond (Z4.isZero x) acc (Z4.add x acc)

def sumZ (l : List Z4) : Z4 := l.foldr addSkip Z4.zero

/-- The 27 coordinates of native point `p`. -/
noncomputable def stateList (ys : Fin 24 → ℤ) (p : Fin 39) : List Z4 :=
  (blocks (densePoint ys)).getD p.val []

/-- Trace-form pairing with the native weights `1,1,1,2,...,2`. -/
def pairDot (l m : List Z4) : Z4 :=
  let pr := List.zipWith Z4.mul l m
  Z4.add (sumZ (pr.take 3)) (Z4.smul 2 (sumZ (pr.drop 3)))

/-- Product of coordinates `a`, `b` of `l`, always formed in increasing index order so that the
kernel shares `x_a x_b` and `x_b x_a`. -/
def mulAt (l : List Z4) (a b : ℕ) : Z4 :=
  Bool.rec (motive := fun _ => Z4) (Z4.mul (l.getD b Z4.zero) (l.getD a Z4.zero))
    (Z4.mul (l.getD a Z4.zero) (l.getD b Z4.zero)) (Nat.ble a b)

/-- `(Σ_{n=1} + Σ_{n≠±1} n ·, Σ_{n=-1})` over a product table, so that unit coefficients cost no
scalar multiplication. -/
def idAcc (l : List Z4) : List (Fin 27 × Fin 27 × ℤ) → Z4 × Z4 :=
  List.foldr (fun e acc =>
    let x := mulAt l e.1.val e.2.1.val
    cond (Z4.isZero x) acc
      (cond (e.2.2 == 1) (Z4.add x acc.1, acc.2)
        (cond (e.2.2 == -1) (acc.1, Z4.add x acc.2) (Z4.add (Z4.smul e.2.2 x) acc.1, acc.2))))
    (Z4.zero, Z4.zero)

def idVal (l : List Z4) (t : List (Fin 27 × Fin 27 × ℤ)) : Z4 :=
  let r := idAcc l t
  Z4.add r.1 (Z4.neg r.2)

/-- Quadratic part of one original row at the point, read through the row label exactly as
`labelShape` does (idempotency rows use `productTable`, pairing rows the trace form; trace and
frame-sum rows have no quadratic part). -/
noncomputable def rowVal (S : Fin 39 → List Z4) : ConfigurationResidualIndices.FLabel → Z4
  | .inl (p, k) => idVal (S p) (productTable k)
  | .inr (.inr (.inr pq)) => pairDot (S pq.val.1) (S pq.val.2)
  | _ => Z4.zero

/-- One weighted row; rows without a quadratic part are skipped. -/
noncomputable def termVal (d : ℕ) (s : NativeH.HSpec) (S : Fin 39 → List Z4)
    (e : NativeH.Entry) : Z4 :=
  match e.label with
  | .inl _ => Z4.mul (weight d s e) (rowVal S e.label)
  | .inr (.inr (.inr _)) => Z4.mul (weight d s e) (rowVal S e.label)
  | _ => Z4.zero

noncomputable def engine (d : ℕ) (s : NativeH.HSpec) (es : List NativeH.Entry)
    (S : Fin 39 → List Z4) : Z4 :=
  sumZ (es.map (termVal d s S))

/-- Book terms `(p, q, c)` meaning `c * y p * y q`. -/
def hBook (i : Fin 4) (a : Fin 3) : List (Fin 24 × Fin 24 × ℤ) :=
  List.ofFn fun k : Fin 3 =>
    let s := NativeH.hSpec i a
    let t := terms s.quadricIndex k
    (NativeH.Reproduction.orientedIndex s t.1, NativeH.Reproduction.orientedIndex s t.2.1,
      if s.negated then -t.2.2 else t.2.2)

def tBook (i : Fin 4) (a : Fin 3) : List (Fin 24 × Fin 24 × ℤ) :=
  List.ofFn fun k : Fin 3 => terms (tIndex i a) k

noncomputable def bookVal (sc : ℤ) (l : List (Fin 24 × Fin 24 × ℤ)) (ys : Fin 24 → ℤ) : Z4 :=
  (l.map fun t => Z4.ofInt (Int.mul (Int.mul sc t.2.2) (Int.mul (ys t.1) (ys t.2.1)))).foldr
    Z4.add Z4.zero

/-! ## The Kronecker point -/

/-- Optimal 24-mark Golomb ruler: all 300 sums `g j + g l` (`j ≤ l`) are distinct. -/
def golList : List ℕ :=
  [0, 9, 33, 37, 38, 97, 122, 129, 140, 142, 152, 191, 205, 208, 252, 278, 286, 326, 332, 353,
    368, 384, 403, 425]
def gol (j : Fin 24) : ℕ := golList.getD j.val 0

/-- Digit width in bits. -/
def width : ℕ := 104

def ystar (j : Fin 24) : ℤ := Int.ofNat (Nat.pow 2 (Nat.mul width (gol j)))

/-- Full H scale `2 * d * 384540 ^ 2` with the literal common denominator. -/
def fullScale (d : ℕ) : ℕ := 2 * d * denominator * denominator

noncomputable def hValue (i : Fin 4) (a : Fin 3) : Z4 :=
  engine (denLcm (NativeH.rawEntries i a)) (NativeH.hSpec i a) (NativeH.rawEntries i a)
    (stateList ystar)
noncomputable def hBookValue (i : Fin 4) (a : Fin 3) : Z4 :=
  bookVal (fullScale (denLcm (NativeH.rawEntries i a))) (hBook i a) ystar
noncomputable def tValue (i : Fin 4) (a : Fin 3) : Z4 :=
  engine (denLcm (NativeT.rawEntries i a)) (NativeT.tSpec i a) (NativeT.rawEntries i a)
    (stateList ystar)
noncomputable def tBookValue (i : Fin 4) (a : Fin 3) : Z4 :=
  bookVal (fullScale (denLcm (NativeT.rawEntries i a))) (tBook i a) ystar

end Option2.NativeStress.HTRouteKron

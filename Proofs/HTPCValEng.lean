module

public import HTPCValSupp
public import HTKronEngine
public import HTKronExactness
public import HTPhaseKronSem

@[expose] public section

/-!
# Integer value engine for `Σ_r ℓ_r(u) Q_r(N(y)·Φ(u))` (computation only)

Everything is computed in the kernel from ORIGINAL data: the base point `baseQ12`, the plane characters
`planeExp`, the typed row labels, the certificate operators (the derivation-extension lists `aPairs` and the specified
`kPairs`), the covector list and the Book quadric `Dictionary.terms`. No computed table is a literal.

Structural reduction (proved in `HTPCValEngSound`): on a window state `p` (window `t`), `w_p = (N(y)Φ(u))_p` lies in
`J_t` and only the generators of sheet `t` contribute; pair rows between different windows reduce to the three
diagonal coordinates; idempotency rows `(p,k)` with `k ∉ J_t` vanish (product closure of `J_t`); trace and frame rows
have no quadratic part. So the engine needs `4bD·w` only on the 108 window-diagonal coordinates (`dAt`, Laurent terms
keyed by `eKey + M·j`), and checks each window block `(t,t')` separately against the Book quadric terms whose two
sheets are `{t,t'}` (`blockCheck`, one kernel declaration per block). Integer phased point adapted from the phased-covector engine’s
`HTPCovEngine` (first-party team code, same workspace), renamed into `ValEng`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace Option2.NativeStress.HTPhaseComplete.ValEng

open HTPhaseKron HTRouteKron NativeH NativeH.Equilibrium ConfigurationResidualIndices QuarticCertificate.RowBridge
open NativePolynomial.ConfigurationResiduals

/-! ## Integer phased point (adapted from `HTPCovEngine`, renamed) -/

def bD : ℕ := 192270

def ratZ (q : ℚ) : ℤ := ((bD : ℚ) * q).num

def baseZ (v : Fin 1053) : Z4 :=
  let x := baseQ12 v
  ⟨ratZ x.a, ratZ x.b, ratZ x.c, ratZ x.d⟩

def baseZn (n : ℕ) : Z4 := if h : n < 1053 then baseZ ⟨n, h⟩ else 0

def baseBlocks : List (List Z4) :=
  (List.range 39).map fun p => (List.range 27).map fun k => baseZn (27 * p + k)

def bz (n : ℕ) : Z4 := (baseBlocks.getD (n / 27) []).getD (n % 27) 0

def z4I : Z4 := ⟨0, 1, 0, 0⟩

def mulI (x : Z4) : Z4 := ⟨-x.b, x.a, -x.d, x.c⟩

def phiZraw (v : Fin 1053) : List (Z4 × Ex) :=
  let p := v.val / 27
  let k := v.val % 27
  if k < 3 then [((2 : ℤ) • bz v.val, (0, 0, 0, 0))] else
  let j := (k - 3) / 2
  match planeExp j with
  | none => [((2 : ℤ) • bz v.val, (0, 0, 0, 0))]
  | some m =>
    let a := 27 * p + 3 + 2 * j
    let x := bz a
    let y := bz (a + 1)
    let z := x - mulI y
    let zb := x + mulI y
    if (k - 3) % 2 = 0 then [(z, m), (zb, Ex.neg m)]
    else [(mulI z, m), (-(mulI zb), Ex.neg m)]

def isZ (x : Z4) : Bool := x.a == 0 && x.b == 0 && x.c == 0 && x.d == 0

def phiZ (v : Fin 1053) : List (Z4 × Ex) := (phiZraw v).filter fun t => !isZ t.1

def phiZn (n : ℕ) : List (Z4 × Ex) := if h : n < 1053 then phiZ ⟨n, h⟩ else []

def phiTab : List (List (List (Z4 × Ex))) :=
  (List.range 39).map fun p => (List.range 27).map fun k => phiZn (27 * p + k)

def phiAt (v : Fin 1053) : List (Z4 × Ex) := (phiTab.getD (v.val / 27) []).getD (v.val % 27) []

/-! ## Exact collection by natural keys (adapted from `insZ`/`collZ`) -/

def insZ (e : ℕ) (c : Z4) : List (ℕ × Z4) → List (ℕ × Z4)
  | [] => [(e, c)]
  | (k, s) :: r => if Nat.beq e k then (k, s + c) :: r else (k, s) :: insZ e c r

def collZ (l : List (ℕ × Z4)) : List (ℕ × Z4) := l.foldr (fun t acc => insZ t.1 t.2 acc) []

/-! ## Exponent keys: box `[-7, 7]⁴`, base 15 -/

def M : ℕ := 50625

def eKey (m : Ex) : ℕ :=
  (m.1 + 7).toNat + 15 * ((m.2.1 + 7).toNat + 15 * ((m.2.2.1 + 7).toNat + 15 * (m.2.2.2 + 7).toNat))

def eBox (m : Ex) : Bool :=
  decide (-7 ≤ m.1 ∧ m.1 ≤ 7 ∧ -7 ≤ m.2.1 ∧ m.2.1 ≤ 7 ∧ -7 ≤ m.2.2.1 ∧ m.2.2.1 ≤ 7 ∧
    -7 ≤ m.2.2.2 ∧ m.2.2.2 ≤ 7)

def eDec (e : ℕ) : Ex :=
  (((e % 15 : ℕ) : ℤ) - 7, (((e / 15) % 15 : ℕ) : ℤ) - 7, (((e / 225) % 15 : ℕ) : ℤ) - 7,
    (((e / 3375) % 15 : ℕ) : ℤ) - 7)

/-! ## The anchor operators `2N_j = 2A_j − 2K_j` as raw sparse entries (read from the certificate lists) -/

/-- Signed entries `(k, n, value)` of `nZ j = 2A_j − 2K_j`, directly from `aPairs` and `kPairs`
(positions may repeat; only sums are used). -/
def nEnt (j : Fin 24) : List (ℕ × ℕ × GaussianInt) :=
  match aPairOf j, kPairOf j with
  | some pr, some kp =>
    let sA : ℤ := if Nat.beq pr.2.1 j.val then 1 else -1
    let sK : ℤ := if Nat.beq kp.2.1 j.val then 1 else -1
    (pr.2.2.2.1.map fun e => (e.1.val, e.2.1.val, (⟨sA * e.2.2, 0⟩ : GaussianInt))) ++
    (pr.2.2.2.2.map fun e => (e.1.val, e.2.1.val, (⟨0, -e.2.2⟩ : GaussianInt))) ++
    (kp.2.2.2.1.map fun e => (e.1, e.2.1, (⟨-(sK * e.2.2.1), 0⟩ : GaussianInt))) ++
    (kp.2.2.2.2.map fun e => (e.1, e.2.1, (⟨0, e.2.2.1⟩ : GaussianInt)))
  | _, _ => []

/-- Row `c` of `nZ j` as `(n, value)` entries. -/
def rRow (j : Fin 24) (c : ℕ) : List (ℕ × GaussianInt) :=
  ((nEnt j).filter fun e => Nat.beq e.1 c).map fun e => (e.2.1, e.2.2)

def rTab : List (List (List (ℕ × GaussianInt))) :=
  (List.finRange 24).map fun j => (List.range 3).map fun c => rRow j c

def rAt (j : Fin 24) (c : ℕ) : List (ℕ × GaussianInt) := (rTab.getD j.val []).getD c []

/-- The generators of sheet `t`. -/
def sheetJs (t : ℕ) : List (Fin 24) := (List.finRange 24).filter fun j => Nat.beq (sheetOf j) t

def sjTab : List (List (Fin 24)) := (List.range 4).map sheetJs

def sjAt (t : ℕ) : List (Fin 24) := sjTab.getD t []

/-- `g · x` for a Gaussian integer `g` (`zq (gmul g x) = gToQ12 g · zq x`). -/
def gmul (g : GaussianInt) (x : Z4) : Z4 := g.re • x + g.im • mulI x

def phiAtN (m : ℕ) : List (Z4 × Ex) := (phiTab.getD (m / 27) []).getD (m % 27) []

/-! ## Diagonal values on window states, per generator: the character form

`dPoly p c j` = collected Laurent terms (keyed by `eKey`) of `2bD · Σ_n nZ j c n · Φ(u)_{p,n}`;
`charOK t j`: on window `t` every such list uses one single exponent key `ejKey t j` (the character of `j`);
`d0 p c j` = the sum of its coefficients. -/

def winSt (p : ℕ) : ℕ := (p - 3) / 9

def dPoly (p c : ℕ) (j : Fin 24) : List (ℕ × Z4) :=
  (collZ ((rAt j c).flatMap fun e =>
    (phiAtN (27 * p + e.1)).map fun t => (eKey t.2, gmul e.2 t.1))).filter fun q => !isZ q.2

def zsum (l : List (ℕ × Z4)) : Z4 := l.foldr (fun q acc => q.2 + acc) 0

def d0 (p c : ℕ) (j : Fin 24) : Z4 := zsum (dPoly p c j)

def winStates (t : ℕ) : List ℕ := (List.range 9).map fun i => 3 + 9 * t + i

def keysJ (t : ℕ) (j : Fin 24) : List ℕ :=
  (winStates t).flatMap fun p => (List.range 3).flatMap fun c => (dPoly p c j).map fun q => q.1

def ejKey (t : ℕ) (j : Fin 24) : ℕ := (keysJ t j).headD (eKey (0, 0, 0, 0))

def charOK (t : ℕ) (j : Fin 24) : Bool := (keysJ t j).all fun k => Nat.beq k (ejKey t j)

/-! ## Kronecker packing in `y` (one integer per diagonal coordinate) -/

def Ypow (n : ℕ) : Z4 := ((Int.ofNat (Nat.pow 2 (128 * n)) : ℤ) : Z4)

/-- `Σ_{j ∈ sheet} d0 p c j · Y^{sh·j}` (digits indexed by the generator itself). -/
def wd (p c sh : ℕ) : Z4 := ((sjAt (winSt p)).map fun j => d0 p c j * Ypow (sh * j.val)).sum

/-! ## Data conditions -/

/-- Covector entries: idempotency rows on window states outside `J_t`; pair rows between window states of
different windows; trace and frame rows unrestricted (no quadratic part). -/
def entryOK (pe : PEntry) : Bool :=
  match pe.e.label with
  | .inl (i, k) => Nat.ble 3 i.val && !(jMem (winSt i.val) k)
  | .inr (.inl _) => true
  | .inr (.inr (.inl _)) => true
  | .inr (.inr (.inr ij)) =>
    Nat.ble 3 ij.val.1.val && Nat.ble 3 ij.val.2.val && !(Nat.beq (winSt ij.val.1.val) (winSt ij.val.2.val))

/-- Product closure of `J_t`: no table entry of a coordinate `k ∉ J_t` has both factors in `J_t`. -/
def closureOK : Bool :=
  (List.range 4).all fun t => (List.finRange 27).all fun k =>
    jMem t k || (productTable k).all fun e => !(jMem t e.1 && jMem t e.2.1)

/-- Positions of the specified K literals are coordinates (`< 27`). -/
def kPosOK : Bool :=
  kPairs.all fun pr => (pr.2.2.2.1 ++ pr.2.2.2.2).all fun e => Nat.blt e.1 27 && Nat.blt e.2.1 27

/-- Every sheet `< 4` (the assignment of generators to windows). -/
def sheetOK : Bool := (List.finRange 24).all fun j => Nat.blt (sheetOf j) 4

/-- Base point on window states: equal diagonal, zero plane coordinates outside the own window. -/
noncomputable def baseOK : Bool :=
  (List.range 36).all fun q =>
    let p := q + 3
    decide (bq (27 * p) = bq (27 * p + 1)) && decide (bq (27 * p) = bq (27 * p + 2)) &&
    (List.range 24).all fun m =>
      Nat.beq (winOf (m / 2)) (winSt p) || decide (bq (27 * p + 3 + m) = 0)

/-! ## Block check -/

def Kw (L : List PEntry) : ℕ := L.foldr (fun pe a => Nat.lcm pe.e.coefficient.denominator a) 1

def wz (K : ℕ) (c : Literal) : Z4 := ((K / c.denominator : ℕ) : ℤ) • (⟨c.A, c.B, c.C, c.D⟩ : Z4)

def blk (t t' : ℕ) : ℕ := 4 * min t t' + max t t'

/-- Window block of a covector entry (`16` for non-pair rows). -/
def part (pe : PEntry) : ℕ :=
  match pe.e.label with
  | .inr (.inr (.inr ij)) => blk (winSt ij.val.1.val) (winSt ij.val.2.val)
  | _ => 16

/-- The packed block integer of one entry: `wz · Σ_{c<3} wd(p,c,1) · wd(q,c,6)`. -/
def bInt (K : ℕ) (pe : PEntry) : Z4 :=
  match pe.e.label with
  | .inr (.inr (.inr ij)) =>
    wz K pe.e.coefficient * (wd ij.val.1.val 0 1 * wd ij.val.2.val 0 24 + wd ij.val.1.val 1 1 * wd ij.val.2.val 1 24 +
      wd ij.val.1.val 2 1 * wd ij.val.2.val 2 24)
  | _ => 0

def rowMass (p c : ℕ) : ℕ := ((sjAt (winSt p)).map fun j => n1 (d0 p c j)).sum

/-- Coefficient mass of an entry (bounds every packed digit). -/
def bMass (K : ℕ) (pe : PEntry) : ℕ :=
  match pe.e.label with
  | .inr (.inr (.inr ij)) =>
    9 * n1 (wz K pe.e.coefficient) * (rowMass ij.val.1.val 0 * rowMass ij.val.2.val 0 +
      rowMass ij.val.1.val 1 * rowMass ij.val.2.val 1 + rowMass ij.val.1.val 2 * rowMass ij.val.2.val 2)
  | _ => 0

/-- Packed Book target of block `(t, t')`, `t < t'`, scaled by `sc`. -/
def tInt (sc : ℤ) (i : Fin 4) (a : Fin 3) (t t' : ℕ) : Z4 :=
  ((List.finRange 3).map fun m =>
    let e := BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m
    if Nat.beq (sheetOf e.1) t && Nat.beq (sheetOf e.2.1) t' then
      ((sc * e.2.2 : ℤ) : Z4) * Ypow (e.1.val + 24 * e.2.1.val)
    else if Nat.beq (sheetOf e.1) t' && Nat.beq (sheetOf e.2.1) t then
      ((sc * e.2.2 : ℤ) : Z4) * Ypow (e.2.1.val + 24 * e.1.val)
    else 0).sum

def tMass (sc : ℤ) (i : Fin 4) (a : Fin 3) : ℕ :=
  ((List.finRange 3).map fun m => (sc * (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).2.2).natAbs).sum

def eJ (j : Fin 24) : Ex := eDec (ejKey (sheetOf j) j)

/-- Book terms of the block sit at total exponent zero. -/
def tExpOK (m0 : Ex) (i : Fin 4) (a : Fin 3) (t t' : ℕ) : Bool :=
  (List.finRange 3).all fun m =>
    let e := BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m
    !(Nat.beq (blk (sheetOf e.1) (sheetOf e.2.1)) (blk t t')) ||
      decide (Ex.add m0 (Ex.add (eJ e.1) (eJ e.2.1)) = (0, 0, 0, 0))

def vScale (K : ℕ) : ℕ := K * (4 * bD) * (4 * bD)

/-- **Block check** of covector `L` against Book component `(i, a)` on windows `t < t'`. -/
def blockCheck (L : List PEntry) (i : Fin 4) (a : Fin 3) (t t' : ℕ) : Bool :=
  let K := Kw L
  let B := L.filter fun pe => Nat.beq (part pe) (blk t t')
  let m0 : Ex := match B.head? with | some pe => pe.x | none => (0, 0, 0, 0)
  (B.all fun pe => decide (pe.x = m0)) &&
  ((sjAt t).all fun j => charOK t j && eBox (eJ j)) && ((sjAt t').all fun j => charOK t' j && eBox (eJ j)) &&
  tExpOK m0 i a t t' &&
  Nat.blt ((B.map (bMass K)).sum + tMass (vScale K) i a) (Nat.pow 2 128) &&
  isZ ((B.map (bInt K)).sum - tInt (vScale K) i a t t')

/-- Global data check: entries well placed; every Book term joins two different sheets `< 4`. -/
def dataCheck (L : List PEntry) (i : Fin 4) (a : Fin 3) : Bool :=
  L.all entryOK &&
  (List.finRange 3).all fun m =>
    let e := BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m
    Nat.blt (sheetOf e.1) 4 && Nat.blt (sheetOf e.2.1) 4 && !(Nat.beq (sheetOf e.1) (sheetOf e.2.1))

end Option2.NativeStress.HTPhaseComplete.ValEng

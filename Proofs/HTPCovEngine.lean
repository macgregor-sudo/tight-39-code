module

public import HTKronExactness
public import HTPhaseKronSem

@[expose] public section

/-! # Integer Laurent engine for phased equilibrium covectors (first-party; computation only)

Generic in the covector data `L : List PEntry` (typed original row label, Q12 literal, Laurent tag).
Everything is read from the ORIGINAL objects: `labelShape` of each typed row, `baseQ12`, `planeExp`.
No computed table is stored as a literal; the only per-component data is the covector list.

For a column `c`, the identity `Σ_pe ℓ_pe u^{x_pe} · J_{pe,c}(Φ(u)) = 0` is scaled by the integer
`Kw · 4D` (`Kw` = lcm of the literal denominators, `D = bD` clears `baseQ12`), so every Laurent term has a
`Z4 = ℤ[i,√3]` coefficient. Terms are generated once per row (not once per column), filtered by column,
and collected exactly by the Kronecker slot `key m = enc₇(m + 3)` of their exponent (the base-7 digit
position of the one-point evaluation `u_a = B^(7^a)`, stored sparsely: at most ~14 occupied slots per column
instead of a 2401-digit packed integer, so no majorant/digit bound is needed). The semantics are in
`HTPCovEngineSound`. -/

set_option autoImplicit false
namespace Option2.NativeStress.HTPhaseComplete
open HTPhaseKron HTRouteKron NativeH NativeH.Equilibrium ConfigurationResidualIndices
open QuarticCertificate.RowBridge

/-- Common denominator of the base point `baseQ12` (checked by `baseZ_spec`). -/
def bD : ℕ := 192270

def ratZ (q : ℚ) : ℤ := ((bD : ℚ) * q).num

/-- `bD · baseQ12 v` as an element of `ℤ[i,√3]` (exactness: `baseZ_spec`). -/
def baseZ (v : Fin 1053) : Z4 :=
  let x := baseQ12 v
  ⟨ratZ x.a, ratZ x.b, ratZ x.c, ratZ x.d⟩

def baseZn (n : ℕ) : Z4 := if h : n < 1053 then baseZ ⟨n, h⟩ else 0

/-- The integer base point, one list of 27 coordinates per state (lookup `bz`). -/
def baseBlocks : List (List Z4) :=
  (List.range 39).map fun p => (List.range 27).map fun k => baseZn (27 * p + k)

def bz (n : ℕ) : Z4 := (baseBlocks.getD (n / 27) []).getD (n % 27) 0

def zI : Z4 := ⟨0, 1, 0, 0⟩

/-- Multiplication by `i` without multiplications (`mulI_eq : mulI x = zI * x`). -/
def mulI (x : Z4) : Z4 := ⟨-x.b, x.a, -x.d, x.c⟩

/-- Integer Laurent terms of `2·bD·Φ(u)_v` (same case split as `phiTerms`). -/
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

/-- The same terms with zero coefficients dropped (most moving-plane coordinates of the base vanish). -/
def phiZ (v : Fin 1053) : List (Z4 × Ex) := (phiZraw v).filter fun t => !isZ t.1

def phiZn (n : ℕ) : List (Z4 × Ex) := if h : n < 1053 then phiZ ⟨n, h⟩ else []

/-- The phased integer point, one list of 27 coordinate term lists per state (evaluated once). -/
def phiTab : List (List (List (Z4 × Ex))) :=
  (List.range 39).map fun p => (List.range 27).map fun k => phiZn (27 * p + k)

/-- Table lookup (`phiAt_eq : phiAt v = phiZ v`). -/
def phiAt (v : Fin 1053) : List (Z4 × Ex) := (phiTab.getD (v.val / 27) []).getD (v.val % 27) []

/-- lcm of the literal denominators of a covector. -/
def Kw (L : List PEntry) : ℕ := L.foldr (fun pe a => Nat.lcm pe.e.coefficient.denominator a) 1

/-- `K · literal` in `ℤ[i,√3]` (exact when the denominator divides `K`). -/
def wz (K : ℕ) (c : Literal) : Z4 := ((K / c.denominator : ℕ) : ℤ) • (⟨c.A, c.B, c.C, c.D⟩ : Z4)

/-- Twice the quadratic scale of a row shape (`½` for idempotency rows, `1` otherwise). -/
def sc2 (s : RowShape) : ℤ := if s.halfScaled then 1 else 2

/-- The Jacobian-row terms of one entry at `Φ(u)` in the columns of state `p`, scaled:
`(column, coefficient, Laurent exponent)`. -/
def rowZ (K p : ℕ) (pe : PEntry) : List (ℕ × Z4 × Ex) :=
  let s := labelShape pe.e.label
  let w := wz K pe.e.coefficient
  (s.quadratic.flatMap fun q =>
    (if Nat.beq (q.1.val / 27) p then
      (phiAt q.2.1).map fun t => (q.1.val, (sc2 s * q.2.2) • w * t.1, Ex.add pe.x t.2) else []) ++
    (if Nat.beq (q.2.1.val / 27) p then
      (phiAt q.1).map fun t => (q.2.1.val, (sc2 s * q.2.2) • w * t.1, Ex.add pe.x t.2) else [])) ++
  (s.linear.filter fun l => Nat.beq (l.1.val / 27) p).map fun l =>
    (l.1.val, ((4 * bD : ℕ) * l.2 : ℤ) • w, pe.x)

/-- Kronecker slot of an exponent in the box `[-3, 3]⁴`: base-7 digits of `m + 3`. -/
def key (m : Ex) : ℕ :=
  (m.1 + 3).toNat + 7 * ((m.2.1 + 3).toNat + 7 * ((m.2.2.1 + 3).toNat + 7 * (m.2.2.2 + 3).toNat))

def inBox (m : Ex) : Bool :=
  decide (-3 ≤ m.1 ∧ m.1 ≤ 3 ∧ -3 ≤ m.2.1 ∧ m.2.1 ≤ 3 ∧ -3 ≤ m.2.2.1 ∧ m.2.2.1 ≤ 3 ∧
    -3 ≤ m.2.2.2 ∧ m.2.2.2 ≤ 3)

def insZ (e : ℕ) (c : Z4) : List (ℕ × Z4) → List (ℕ × Z4)
  | [] => [(e, c)]
  | (k, s) :: r => if Nat.beq e k then (k, s + c) :: r else (k, s) :: insZ e c r

def collZ (l : List (ℕ × Z4)) : List (ℕ × Z4) := l.foldr (fun t acc => insZ t.1 t.2 acc) []

/-- One column: every term in the box, every collected slot zero. -/
def colCheck (ts : List (ℕ × Z4 × Ex)) (c : ℕ) : Bool :=
  let l := ts.filter fun t => Nat.beq t.1 c
  l.all (fun t => inBox t.2.2) && (collZ (l.map fun t => (key t.2.2, t.2.1))).all fun p => isZ p.2

/-- All 27 columns of state `p`; rows generated once. -/
def stateCheck (K : ℕ) (F : List PEntry) (p : ℕ) : Bool :=
  let ts := F.flatMap (rowZ K p)
  (List.range 27).all fun k => colCheck ts (27 * p + k)

/-- **The engine.** All 1053 columns (states with no entry are trivially fine). -/
def kronCheck (L : List PEntry) : Bool :=
  (List.finRange 39).all fun p => stateCheck (Kw L) (L.filter (touches p)) p.val

end Option2.NativeStress.HTPhaseComplete

module

public import HTPhaseKronData00

@[expose] public section

/-! # Phase-route core (computation side, data-free): the phased configuration Φ(u) as Laurent
terms over the ORIGINAL base point `baseQ12`, and the per-column expansion/collection of
`Σ_r ℓ_r u^{x_r} · jacobianEntry(½, ·, r, Φ(u), c)`. First-party. -/

set_option autoImplicit false
namespace Option2.NativeStress.HTPhaseKron
open NativeH NativeH.Equilibrium ConfigurationResidualIndices QuarticCertificate.RowBridge

def Ex.add (x y : Ex) : Ex := (x.1 + y.1, x.2.1 + y.2.1, x.2.2.1 + y.2.2.1, x.2.2.2 + y.2.2.2)
def Ex.neg (x : Ex) : Ex := (-x.1, -x.2.1, -x.2.2.1, -x.2.2.2)

/-- Literal character exponent of the α-line (`x - i y`) of plane `j` (coordinates `3+2j, 4+2j`):
windows 2 (planes 2, 7, 9) and 3 (planes 3, 5, 10) move, all other planes are fixed. -/
def planeExp : ℕ → Option Ex
  | 2 => some (-1, 0, 0, 0)
  | 7 => some (0, 1, 0, 0)
  | 9 => some (1, 1, 0, 0)
  | 3 => some (0, 0, 1, 0)
  | 5 => some (0, 0, 0, -1)
  | 10 => some (0, 0, 1, 1)
  | _ => none

/-- Base coordinate by natural index (the original `baseQ12`). -/
noncomputable def bq (n : ℕ) : Q12 := if h : n < 1053 then baseQ12 ⟨n, h⟩ else 0

noncomputable def half : Q12 := Q12.lit 1 0 0 0 2

/-- Laurent terms `(coefficient, exponent)` of coordinate `v` of `Φ(u)`: on a moving plane with
character `χ = u^m`, `x' = ½χ(x - iy) + ½χ⁻¹(x + iy)` and `y' = ½iχ(x - iy) - ½iχ⁻¹(x + iy)`. -/
noncomputable def phiTerms (v : Fin 1053) : List (Q12 × Ex) :=
  let p := v.val / 27
  let k := v.val % 27
  if k < 3 then [(bq v.val, (0, 0, 0, 0))] else
  let j := (k - 3) / 2
  match planeExp j with
  | none => [(bq v.val, (0, 0, 0, 0))]
  | some m =>
    let a := 27 * p + 3 + 2 * j
    let x := bq a
    let y := bq (a + 1)
    let z := x - Q12.I * y
    let zb := x + Q12.I * y
    if (k - 3) % 2 = 0 then [(half * z, m), (half * zb, Ex.neg m)]
    else [(half * (Q12.I * z), m), (-(half * (Q12.I * zb)), Ex.neg m)]

/-- Expanded terms of one covector entry at column `c`, mirroring `shapeJacobianEntry`. -/
noncomputable def entryTerms (pe : PEntry) (c : Fin 1053) : List (Q12 × Ex) :=
  let s := labelShape pe.e.label
  let w := pe.e.coefficient.toQ12
  let sc := quadraticScale half s
  (s.quadratic.flatMap fun q =>
    (if q.1 = c then (phiTerms q.2.1).map fun t => (w * (sc * (q.2.2 : Q12)) * t.1, Ex.add pe.x t.2)
      else []) ++
    (if q.2.1 = c then (phiTerms q.1).map fun t => (w * (sc * (q.2.2 : Q12)) * t.1, Ex.add pe.x t.2)
      else [])) ++
  (s.linear.flatMap fun l => if l.1 = c then [(w * (l.2 : Q12), pe.x)] else [])

noncomputable def colTerms (L : List PEntry) (c : Fin 1053) : List (Q12 × Ex) :=
  L.flatMap fun pe => entryTerms pe c

def insertT (t : Q12 × Ex) : List (Ex × Q12) → List (Ex × Q12)
  | [] => [(t.2, t.1)]
  | (m, s) :: rest => if m = t.2 then (m, s + t.1) :: rest else (m, s) :: insertT t rest

def collect (l : List (Q12 × Ex)) : List (Ex × Q12) := l.foldr insertT []

noncomputable def colOK (L : List PEntry) (c : Fin 1053) : Bool :=
  (collect (colTerms L c)).all fun p => p.2 = 0

/-- All 27 columns of state `p`. -/
noncomputable def stateOK (L : List PEntry) (p : ℕ) : Bool :=
  (List.range 27).all fun k => if h : 27 * p + k < 1053 then colOK L ⟨27 * p + k, h⟩ else true


/-- Jacobian row of one entry at `Φ(u)`, as `(column, (coefficient, exponent))` terms
(the phased analogue of `shapeJacobianRow`). -/
noncomputable def rowTerms (pe : PEntry) : List (Fin 1053 × (Q12 × Ex)) :=
  let s := labelShape pe.e.label
  let w := pe.e.coefficient.toQ12
  let sc := quadraticScale half s
  (s.quadratic.flatMap fun q =>
    ((phiTerms q.2.1).map fun t => (q.1, (w * (sc * (q.2.2 : Q12)) * t.1, Ex.add pe.x t.2))) ++
    ((phiTerms q.1).map fun t => (q.2.1, (w * (sc * (q.2.2 : Q12)) * t.1, Ex.add pe.x t.2)))) ++
  s.linear.map fun l => (l.1, (w * (l.2 : Q12), pe.x))

noncomputable def colTermsR (rows : List (List (Fin 1053 × (Q12 × Ex)))) (c : Fin 1053) :
    List (Q12 × Ex) :=
  rows.flatMap fun r => (r.filter fun t => t.1 = c).map Prod.snd

/-- All 27 columns of state `p`, each entry's row computed once. -/
noncomputable def stateOKR (L : List PEntry) (p : ℕ) : Bool :=
  let rows := L.map rowTerms
  (List.range 27).all fun k => if h : 27 * p + k < 1053 then
    (collect (colTermsR rows ⟨27 * p + k, h⟩)).all (fun q => q.2 = 0) else true

/-- Columns `lo, …, lo+n-1`. -/
noncomputable def okRange (L : List PEntry) (lo n : ℕ) : Bool :=
  (List.range n).all fun i => if h : lo + i < 1053 then colOK L ⟨lo + i, h⟩ else true

theorem okRange_spec (L : List PEntry) (lo n : ℕ) (h : okRange L lo n = true) (i : ℕ) (hi : i < n)
    (hc : lo + i < 1053) : colOK L ⟨lo + i, hc⟩ = true := by
  unfold okRange at h
  rw [List.all_eq_true] at h
  have := h i (List.mem_range.mpr hi)
  simpa [hc] using this

/-- Entries whose row reads state `p`. -/
def touches (p : Fin 39) (pe : PEntry) : Bool := (labelSlots pe.e.label).contains p

end Option2.NativeStress.HTPhaseKron

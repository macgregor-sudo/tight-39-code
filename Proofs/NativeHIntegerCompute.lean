module

public import NativeHQuadraticCompute

@[expose] public section

/-! Denominator-cleared evaluation of the unchanged inputs. Every denominator
and coefficient is computed from the imported source data; no certificate table.
The interpretation and nonzero-scale proofs are separate obligations. -/

namespace Option2.NativeStress.NativeH.Reproduction

open ConfigurationResidualIndices QuarticCertificate.RowBridge
open BookHT.TangentCoordinates BookHT.Dictionary

def integerMul (x y : Coeff) : Coeff :=
  (x.1*y.1 - x.2.1*y.2.1 + 3*x.2.2.1*y.2.2.1 - 3*x.2.2.2*y.2.2.2,
   x.1*y.2.1 + x.2.1*y.1 + 3*(x.2.2.1*y.2.2.2 + x.2.2.2*y.2.2.1),
   x.1*y.2.2.1 + x.2.2.1*y.1 - (x.2.1*y.2.2.2 + x.2.2.2*y.2.1),
   x.1*y.2.2.2 + x.2.2.2*y.1 + x.2.1*y.2.2.1 + x.2.2.1*y.2.1)

def integerScale (n : ℤ) (x : Coeff) : Coeff :=
  (n*x.1,n*x.2.1,n*x.2.2.1,n*x.2.2.2)

def integerConj (x : Coeff) : Coeff := (x.1,-x.2.1,x.2.2.1,-x.2.2.2)

def integerLiteral (c : Literal) : Coeff := (c.A,c.B,c.C,c.D)

def integerOriented (s : HSpec) (c : Literal) : Coeff :=
  let z := if s.conjugated then integerConj (integerLiteral c) else integerLiteral c
  if s.negated then -z else z

def commonDenominator (i : Fin 4) (a : Fin 3) : Nat :=
  ((rawEntries i a).map fun e => e.coefficient.denominator).foldr Nat.lcm 1

def integerNativeTerms (i : Fin 4) (a : Fin 3) : List (Nat × Coeff) :=
  (rawEntries i a).flatMap fun e =>
    (labelShape e.label).quadratic.map fun t =>
      (pairKey t.1 t.2.1,
       integerScale ((commonDenominator i a / e.coefficient.denominator : Nat) *
         (if (labelShape e.label).halfScaled then 1 else 2) * t.2.2)
         (integerOriented (hSpec i a) e.coefficient))

def integerNativeTree (i : Fin 4) (a : Fin 3) : CoeffTree Coeff 21 :=
  CoeffTree.collect (integerNativeTerms i a)

def integerColumnValue : List BookHT.TangentCoordinates.Entry → Fin 1053 → Coeff
  | [], _ => 0
  | e :: es, r => if r = e.1 then e.2 + integerColumnValue es r else integerColumnValue es r

noncomputable def integerColumn (b : Fin 24) (r : Fin 1053) : Coeff :=
  integerColumnValue (d6Entries b) r

noncomputable def integerCoordinateTerms (r : Fin 1053) : List (Fin 24 × Coeff) :=
  (List.ofFn fun j : Fin 24 => (j,integerColumn (eigenIndex j) r)).filter fun e => e.2 != 0

noncomputable def integerRestrictionTerms (i : Fin 4) (a : Fin 3) : List (Nat × Coeff) :=
  (CoeffTree.entries (integerNativeTree i a)).flatMap fun e =>
    (integerCoordinateTerms (firstCoordinate e.1)).flatMap fun p =>
      (integerCoordinateTerms (secondCoordinate e.1)).map fun q =>
        (pairKey p.1 q.1, integerMul (integerMul e.2 p.2) q.2)

noncomputable def integerRestrictionTree (i : Fin 4) (a : Fin 3) : CoeffTree Coeff 10 :=
  CoeffTree.collect (integerRestrictionTerms i a)

def integerFullScale (i : Fin 4) (a : Fin 3) : Nat :=
  2 * commonDenominator i a * denominator * denominator

def integerBookTerms (i : Fin 4) (a : Fin 3) : List (Nat × Coeff) :=
  List.ofFn fun k : Fin 3 =>
    let s := hSpec i a
    let t := terms s.quadricIndex k
    (pairKey (orientedIndex s t.1) (orientedIndex s t.2.1),
     ((integerFullScale i a : ℤ) * (if s.negated then -t.2.2 else t.2.2),0,0,0))

def integerBookTree (i : Fin 4) (a : Fin 3) : CoeffTree Coeff 10 :=
  CoeffTree.collect (integerBookTerms i a)

noncomputable def integerTermCoefficient (j k : Fin 24) (p q : Fin 1053) : Coeff :=
  let x := integerColumn (eigenIndex j) p
  let y := integerColumn (eigenIndex k) q
  let v := if x = 0 then 0 else if y = 0 then 0 else integerMul x y
  if j=k then v else
    let x' := integerColumn (eigenIndex k) p
    let y' := integerColumn (eigenIndex j) q
    v + if x' = 0 then 0 else if y' = 0 then 0 else integerMul x' y'

noncomputable def integerNativeCoefficient (i : Fin 4) (a : Fin 3)
    (j k : Fin 24) : Coeff :=
  let d := commonDenominator i a
  ((rawEntries i a).map fun e =>
    let s := labelShape e.label
    let v := (s.quadratic.map fun t =>
      integerScale t.2.2 (integerTermCoefficient j k t.1 t.2.1)).sum
    if v = 0 then 0 else
      integerScale ((d / e.coefficient.denominator : Nat) *
        (if s.halfScaled then 1 else 2))
        (integerMul (integerOriented (hSpec i a) e.coefficient) v)).sum

def integerBookCoefficient (i : Fin 4) (a : Fin 3) (j k : Fin 24) : Coeff :=
  ((integerBookTerms i a).map fun e => if e.1 = pairKey j k then e.2 else 0).sum

end Option2.NativeStress.NativeH.Reproduction

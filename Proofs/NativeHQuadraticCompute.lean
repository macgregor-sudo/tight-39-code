module

public import NativeHSparseCoefficients
public import NativeHLiteralQ12Bridge
public import RowEvaluation
public import BookTangentData

@[expose] public section

/-! Computational definitions only, importing the actual immutable data. The
separate interpretation modules prove equality to the original residual and V.
No geometric point, family or axis dependency is needed for computation. -/

namespace Option2.NativeStress.NativeH.Reproduction

open ConfigurationResidualIndices QuarticCertificate.RowBridge
open BookHT.TangentCoordinates BookHT.Dictionary

def pairKey {n : Nat} (p q : Fin n) : Nat :=
  if p.val ≤ q.val then n*p.val+q.val else n*q.val+p.val

def nativeTerms (i : Fin 4) (a : Fin 3) : List (Nat × Q12) :=
  (rawEntries i a).flatMap fun e =>
    (labelShape e.label).quadratic.map fun t =>
      (pairKey t.1 t.2.1,
       orientedQ12 (hSpec i a) e.coefficient *
         quadraticScale (Q12.lit 1 0 0 0 2) (labelShape e.label) * (t.2.2 : Q12))

def nativeTree (i : Fin 4) (a : Fin 3) : CoeffTree Q12 21 :=
  CoeffTree.collect (nativeTerms i a)

def collectedNative (i : Fin 4) (a : Fin 3) : List (Nat × Q12) :=
  CoeffTree.entries (nativeTree i a)

def columnLiteral (q : Coeff) : Q12 :=
  Q12.lit q.1 q.2.1 q.2.2.1 q.2.2.2 denominator

def columnValue : List BookHT.TangentCoordinates.Entry → Fin 1053 → Q12
  | [], _ => 0
  | e :: es, r => if r = e.1 then columnLiteral e.2 + columnValue es r else columnValue es r

noncomputable def columnQ12 (b : Fin 24) (r : Fin 1053) : Q12 :=
  columnValue (d6Entries b) r

noncomputable def coordinateTerms (v : Fin 1053) : List (Fin 24 × Q12) :=
  (List.ofFn fun j : Fin 24 => (j,columnQ12 (eigenIndex j) v)).filter fun e => e.2 != 0

def firstCoordinate (k : Nat) : Fin 1053 := ⟨(k/1053)%1053, Nat.mod_lt _ (by decide)⟩
def secondCoordinate (k : Nat) : Fin 1053 := ⟨k%1053, Nat.mod_lt _ (by decide)⟩

noncomputable def restrictionTerms (i : Fin 4) (a : Fin 3) : List (Nat × Q12) :=
  (collectedNative i a).flatMap fun e =>
    (coordinateTerms (firstCoordinate e.1)).flatMap fun p =>
      (coordinateTerms (secondCoordinate e.1)).map fun q =>
        (pairKey p.1 q.1, e.2 * p.2 * q.2)

noncomputable def restrictionTree (i : Fin 4) (a : Fin 3) : CoeffTree Q12 10 :=
  CoeffTree.collect (restrictionTerms i a)

def orientedIndex (s : HSpec) (j : Fin 24) : Fin 24 :=
  if s.conjugated then coordinateBar j else j

def bookTerms (i : Fin 4) (a : Fin 3) : List (Nat × Q12) :=
  List.ofFn fun k : Fin 3 =>
    let s := hSpec i a
    let t := terms s.quadricIndex k
    (pairKey (orientedIndex s t.1) (orientedIndex s t.2.1),
     if s.negated then -(t.2.2 : Q12) else (t.2.2 : Q12))

def bookTree (i : Fin 4) (a : Fin 3) : CoeffTree Q12 10 :=
  CoeffTree.collect (bookTerms i a)

end Option2.NativeStress.NativeH.Reproduction

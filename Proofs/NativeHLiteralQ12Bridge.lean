module

public import NativeHWeights
public import Q12

@[expose] public section

/-!
Q12 representation of the existing native H literal fields, without a second
input table. The same hSpec controls signs and conjugations, and the same
rawEntries controls every row and its order. This ordinary representation
equality makes no Jacobian, equilibrium, phase-continuation or native R claim.
The Q12 implementation and its embedding lemmas are imported unchanged from
the same source family; no proof body is copied.
-/

noncomputable section

namespace Option2.NativeStress.NativeH

open scoped BigOperators
open ConfigurationResidualIndices

/-- Interpret precisely the five already-frozen integer fields over Q12. -/
def Literal.toQ12 (c : Literal) : Q12 :=
  Q12.lit c.A c.B c.C c.D c.denominator

theorem Literal.toQ12_toComplex (c : Literal) :
    Q12.toComplex c.toQ12 = c.toComplex := by
  exact Q12.toComplex_lit c.A c.B c.C c.D c.denominator

/-- Existing H orientation, applied to the same literal before complex casting. -/
def orientedQ12 (s : HSpec) (c : Literal) : Q12 :=
  let z := if s.conjugated then Q12.conj c.toQ12 else c.toQ12
  if s.negated then -z else z

theorem orientedQ12_toComplex (s : HSpec) (c : Literal) :
    Q12.toComplex (orientedQ12 s c) = orientedValue s c := by
  cases hc : s.conjugated <;> cases hn : s.negated <;>
    simp only [orientedQ12, orientedValue, hc, hn, Bool.false_eq_true, ↓reduceIte,
      map_neg, Q12.toComplex_conj, Literal.toQ12_toComplex] <;> rfl

/-- The actual twelve Q12 lists reuse rawEntries and hSpec without new data. -/
def hEntriesQ12 (i : Fin 4) (a : Fin 3) : List (Fin 2184 × Q12) :=
  (rawEntries i a).map fun e =>
    (fNumber e.label, orientedQ12 (hSpec i a) e.coefficient)

/-- Complex embedding preserves the entire actual ordered sparse list. -/
theorem hEntriesQ12_toComplex (i : Fin 4) (a : Fin 3) :
    ((hEntriesQ12 i a).map fun e => (e.1, Q12.toComplex e.2)) = hEntries i a := by
  unfold hEntriesQ12 hEntries
  rw [List.map_map]
  congr 1
  funext e
  exact congrArg (fun z => (fNumber e.label, z)) (orientedQ12_toComplex (hSpec i a) e.coefficient)

/-- All listed occurrences contribute, as in the original complex decoder. -/
def sparseWeightQ12 {ι : Type*} [DecidableEq ι] (es : List (ι × Q12)) : ι → Q12 := fun r =>
  (es.map fun e => if e.1 = r then e.2 else 0).sum

theorem sparseWeightQ12_toComplex {ι : Type*} [DecidableEq ι]
    (es : List (ι × Q12)) (r : ι) :
    Q12.toComplex (sparseWeightQ12 es r) =
      sparseWeight (es.map fun e => (e.1, Q12.toComplex e.2)) r := by
  induction es with
  | nil => simp [sparseWeightQ12, sparseWeight]
  | cons e es ih =>
    simp only [sparseWeightQ12, sparseWeight, List.map_cons, List.sum_cons, map_add] at ih ⊢
    rw [ih]
    by_cases h : e.1 = r <;> simp [h]

def weightQ12 (i : Fin 4) (a : Fin 3) : Fin 2184 → Q12 :=
  sparseWeightQ12 (hEntriesQ12 i a)

/-- Pointwise equality of the actual twelve original-row covectors. -/
theorem weightQ12_toComplex (i : Fin 4) (a : Fin 3) (r : Fin 2184) :
    Q12.toComplex (weightQ12 i a r) = weightC i a r := by
  unfold weightQ12
  rw [sparseWeightQ12_toComplex, hEntriesQ12_toComplex]
  rfl

/-- Equality as complete Fin2184 covectors, with all twelve H quantifiers. -/
theorem covectorsQ12_toComplex (i : Fin 4) (a : Fin 3) :
    (fun r : Fin 2184 => Q12.toComplex (weightQ12 i a r)) = weightC i a :=
  funext (weightQ12_toComplex i a)

private theorem finite_contraction_map {ι : Type*} [Fintype ι] (w g : ι → Q12) :
    Q12.toComplex (∑ r : ι, w r * g r) =
      ∑ r : ι, Q12.toComplex (w r) * Q12.toComplex (g r) := by
  simp only [map_sum, map_mul]

/-- Finite contraction transport; no premise or conclusion asserts annihilation. -/
theorem weightQ12_contraction_toComplex (i : Fin 4) (a : Fin 3)
    (g : Fin 2184 → Q12) :
    Q12.toComplex (∑ r : Fin 2184, weightQ12 i a r * g r) =
      ∑ r : Fin 2184, weightC i a r * Q12.toComplex (g r) := by
  rw [finite_contraction_map]
  apply Finset.sum_congr rfl
  intro r _
  rw [weightQ12_toComplex]

end Option2.NativeStress.NativeH

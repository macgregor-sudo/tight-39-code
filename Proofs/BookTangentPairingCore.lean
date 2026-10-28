module

public import BookTangentData

@[expose] public section

/-!
Shared literal interpretation and sparse-list conjugation lemmas for the
sheet calculations. The literal data is imported unchanged.
No actual V, tangent membership, point comparison or reproduction is asserted.
-/

noncomputable section

namespace Option2.NativeStress.BookHT.TangentCoordinates

open scoped BigOperators ComplexConjugate
open Dictionary

/-- Literal interpretation reuses the accepted Q(i,sqrt(3)) coefficient convention. -/
noncomputable def coefficient (q : Coeff) : ℂ :=
  (⟨q.1, q.2.1, q.2.2.1, q.2.2.2, denominator, by decide⟩ : NativeH.Literal).toComplex

def negConjCoeff (q : Coeff) : Coeff := (-q.1, q.2.1, -q.2.2.1, q.2.2.2)
def negConjEntry (e : Entry) : Entry := (e.1, negConjCoeff e.2)

theorem coefficient_negConj (q : Coeff) :
    coefficient (negConjCoeff q) = -conj (coefficient q) := by
  simp [coefficient, negConjCoeff, NativeH.Literal.toComplex]
  ring

/-- Sparse ordered sum; missing ambient coordinates have coefficient zero. -/
noncomputable def sparseValue : List Entry → AnchorSupport.Ambient
  | [], _ => 0
  | e :: es, r => (if r = e.1 then coefficient e.2 else 0) + sparseValue es r

theorem sparseValue_negConj (es : List Entry) (r : Fin 1053) :
    sparseValue (es.map negConjEntry) r = -conj (sparseValue es r) := by
  induction es with
  | nil => simp [sparseValue]
  | cons e es ih =>
      simp only [List.map_cons, sparseValue, negConjEntry, ih]
      by_cases h : r = e.1 <;> simp [h, coefficient_negConj, add_comm]

/-- Each sheet has root pairs E01/E10, E02/E20, E12/E21. -/
def basisBar : Fin 24 → Fin 24 :=
  ![2,4,0,5,1,3,8,10,6,11,7,9,14,16,12,17,13,15,20,22,18,23,19,21]

theorem raw_bar_reverse {as bs : List Entry}
    (h : as = bs.map negConjEntry) : bs = as.map negConjEntry := by
  rw [h, List.map_map]
  simp [Function.comp_def, negConjEntry, negConjCoeff]


end Option2.NativeStress.BookHT.TangentCoordinates


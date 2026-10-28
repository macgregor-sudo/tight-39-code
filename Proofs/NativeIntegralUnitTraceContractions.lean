module

public import NativeIntegralStructureConstantsComplete

@[expose] public section

/-!
# Integer unit and trace contractions of the fixed native numerator

The unit uses the three diagonal coordinates; the trace pairing has weight1
on those coordinates and weight2 on the24 upper coordinates. These are direct
identities of the existing sparse integer N, whose universal binding to twice
the actual native structure constants is already proved in the import.
No integer Albert carrier, table-correspondence premise or coefficient field
is introduced. Three-term sums and the three physical slots suffice; there
is no enumeration of27-cubed tensor cells or octonion table products.

This is classical coordinate arithmetic, with no novelty claim. The native
source is imported, not copied, from
https://github.com/macgregor-sudo/compact-albert-recognition, commit
40d3b344180d9ddb78aaa2876873377c1e631515. Existing Apache-2.0 notices and the
earlier exact law extraction remain at THIRD_PARTY_NOTICES.md#native-albert-code.
Private index proofs repeat the earlier first-party label bookkeeping because the
preceding proof helpers are private; N and its data definitions are unchanged.
Imported Mathlib APIs are pinned at065356127b1dc0016f66b7283ce0ce2c4055aa55.
No outbound license is chosen. Thanks to the native-model, Lean and mathlib
contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

namespace NativePolynomial.IntegralStructureConstants

open scoped BigOperators

/-- Integral trace-pairing weight in the literal existing upper coordinates. -/
def coordinateTraceWeight (i : Fin 27) : ℤ := if i.val < 3 then 1 else 2

@[simp] theorem coordinateTraceWeight_diagonal (r : Fin 3) :
    coordinateTraceWeight (diagonalCoordinateIndex r) = 1 := by
  simp [coordinateTraceWeight, diagonalCoordinateIndex, r.isLt]

@[simp] theorem coordinateTraceWeight_upper (s : Fin 3) (a : Fin 8) :
    coordinateTraceWeight (upperCoordinateIndex s a) = 2 := by
  have hBound : 3 ≤ (upperCoordinateIndex s a).val := by
    change 3 ≤ 3 + 8 * s.val + a.val
    exact le_trans (Nat.le_add_right 3 (8 * s.val)) (Nat.le_add_right _ a.val)
  simp only [coordinateTraceWeight, ite_eq_right (not_lt_of_ge hBound)]

private theorem label_diagonal (r : Fin 3) :
    coordinateLabel (diagonalCoordinateIndex r) = .inl r := by
  fin_cases r <;> rfl

private theorem label_upper (s : Fin 3) (a : Fin 8) :
    coordinateLabel (upperCoordinateIndex s a) = .inr (s, a) := by
  fin_cases s <;> fin_cases a <;> rfl

private theorem diagonal_index_eq_iff (r t : Fin 3) :
    diagonalCoordinateIndex r = diagonalCoordinateIndex t ↔ r = t := by
  constructor
  · intro h
    have hLabels := congrArg coordinateLabel h
    rw [label_diagonal, label_diagonal] at hLabels
    exact Sum.inl.inj hLabels
  · rintro rfl
    rfl

private theorem diagonal_ne_upper (r s : Fin 3) (a : Fin 8) :
    diagonalCoordinateIndex r ≠ upperCoordinateIndex s a := by
  intro h
  have hLabels := congrArg coordinateLabel h
  rw [label_diagonal, label_upper] at hLabels
  cases hLabels

private theorem upper_ne_diagonal (s : Fin 3) (a : Fin 8) (r : Fin 3) :
    upperCoordinateIndex s a ≠ diagonalCoordinateIndex r :=
  (diagonal_ne_upper r s a).symm

private theorem upper_index_eq_iff (s t : Fin 3) (a b : Fin 8) :
    upperCoordinateIndex s a = upperCoordinateIndex t b ↔ s = t ∧ a = b := by
  constructor
  · intro h
    have hLabels := congrArg coordinateLabel h
    rw [label_upper, label_upper] at hLabels
    exact Prod.mk.inj (Sum.inr.inj hLabels)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The two incident diagonal unit coordinates each contribute1 to an upper
coordinate; a diagonal coordinate instead contributes its own coefficient2. -/
theorem numerator_unit_contraction (j k : Fin 27) :
    (∑ r : Fin 3, numerator (diagonalCoordinateIndex r) j k) =
      if k = j then 2 else 0 := by
  rw [Fin.sum_univ_three]
  rcases coordinate_cases j with ⟨t, rfl⟩ | ⟨s, a, rfl⟩
  · simp only [numerator, label_diagonal, numeratorFromLabels]
    fin_cases t <;> simp [integerCoordinate]
  · simp only [numerator, label_diagonal, label_upper, numeratorFromLabels]
    fin_cases s <;> simp [slotEndpoints, integerCoordinate]
    all_goals split_ifs <;> norm_num

/-- Summing the three output diagonals gives twice the literal weighted
coordinate pairing. Mixed upper slots have no diagonal output. -/
theorem numerator_trace_contraction (i j : Fin 27) :
    (∑ r : Fin 3, numerator i j (diagonalCoordinateIndex r)) =
      if i = j then 2 * coordinateTraceWeight i else 0 := by
  rw [Fin.sum_univ_three]
  rcases coordinate_cases i with ⟨r, rfl⟩ | ⟨s, a, rfl⟩
  · rcases coordinate_cases j with ⟨t, rfl⟩ | ⟨t, b, rfl⟩
    · simp only [numerator, label_diagonal, numeratorFromLabels,
        coordinateTraceWeight_diagonal]
      fin_cases r <;> fin_cases t <;>
        simp [integerCoordinate, diagonal_index_eq_iff]
    · simp [numerator, label_diagonal, label_upper,
        numeratorFromLabels, integerCoordinate, diagonal_ne_upper]
  · rcases coordinate_cases j with ⟨r, rfl⟩ | ⟨t, b, rfl⟩
    · simp [numerator, label_diagonal, label_upper,
        numeratorFromLabels, integerCoordinate, diagonal_ne_upper, upper_ne_diagonal]
    · by_cases h : a = b <;> fin_cases s <;> fin_cases t <;>
        simp [numerator_upper_upper, upperUpperNumerator,
          mixedUpperNumerator, integerCoordinate, slotEndpoints, diagonal_index_eq_iff,
          diagonal_ne_upper, upper_index_eq_iff, h]

end NativePolynomial.IntegralStructureConstants



#check @NativePolynomial.IntegralStructureConstants.coordinateTraceWeight
#check @NativePolynomial.IntegralStructureConstants.coordinateTraceWeight_diagonal
#check @NativePolynomial.IntegralStructureConstants.coordinateTraceWeight_upper
#check @NativePolynomial.IntegralStructureConstants.numerator_unit_contraction
#check @NativePolynomial.IntegralStructureConstants.numerator_trace_contraction

#print axioms NativePolynomial.IntegralStructureConstants.coordinateTraceWeight
#print axioms NativePolynomial.IntegralStructureConstants.coordinateTraceWeight_diagonal
#print axioms NativePolynomial.IntegralStructureConstants.coordinateTraceWeight_upper
#print axioms NativePolynomial.IntegralStructureConstants.numerator_unit_contraction
#print axioms NativePolynomial.IntegralStructureConstants.numerator_trace_contraction

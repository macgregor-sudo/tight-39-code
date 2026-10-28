module

public import NativeConfigurationPairIdealStandaloneAudit

@[expose] public section

/-!
# Reverse ideal assembly with an explicit trace-row input

The existing pair-row theorem covers every scalar overlap. Shared
idempotency and frame-sum rows are literal generators of the G ideal.
The remaining trace-row membership is stated as a visible hypothesis here;
this is an isolated interface check, not the closed ideal-equality result.
The corresponding conclusion is `fTrace_mem_gSpan` for all 39 actual point labels.

Only first-party residual APIs and mathlib's ideal-span operations are used.
This file copies no third-party implementation and makes no novelty claim.
-/

namespace NativePolynomial.ConfigurationResiduals

open ConfigurationResidualIndices

variable {R : Type*} [CommRing R]

/-- A shared idempotency F row is a literal G generator. -/
theorem fId_mem_gSpan (h t : R) (i : Fin 39) (k : Fin 27) :
    fRow h t (fNumber (fId i k)) ∈ Ideal.span (Set.range (gRow h t)) := by
  have hRow : gRow h t (gNumber (gId i k)) ∈
      Ideal.span (Set.range (gRow h t)) :=
    Ideal.subset_span ⟨gNumber (gId i k), rfl⟩
  rw [gRow_id] at hRow
  rw [fRow_id]
  exact hRow

/-- A shared frame-sum F row is a literal G generator. -/
theorem fSum_mem_gSpan (h t : R) (f : Fin 13) (k : Fin 27) :
    fRow h t (fNumber (fSum f k)) ∈ Ideal.span (Set.range (gRow h t)) := by
  have hRow : gRow h t (gNumber (gSum f k)) ∈
      Ideal.span (Set.range (gRow h t)) :=
    Ideal.subset_span ⟨gNumber (gSum f k), rfl⟩
  rw [gRow_sum] at hRow
  rw [fRow_sum]
  exact hRow

/-- Exhaust the four typed F row families once all trace rows are supplied. -/
theorem fRow_mem_gSpan_of_trace (h t : R) (hHalf : (2 : R) * h = 1)
    (hTrace : ∀ i : Fin 39,
      fRow h t (fNumber (fTrace i)) ∈ Ideal.span (Set.range (gRow h t)))
    (r : Fin 2184) :
    fRow h t r ∈ Ideal.span (Set.range (gRow h t)) := by
  have hAll (label : FLabel) :
      fRow h t (fNumber label) ∈ Ideal.span (Set.range (gRow h t)) := by
    rcases label with ik | other
    · rcases ik with ⟨i, k⟩
      exact fId_mem_gSpan h t i k
    · rcases other with i | other
      · exact hTrace i
      · rcases other with fk | ij
        · rcases fk with ⟨f, k⟩
          exact fSum_mem_gSpan h t f k
        · exact fPair_mem_gSpan h t hHalf ij
  have hRow := hAll (fNumber.symm r)
  rw [fNumber.apply_symm_apply] at hRow
  exact hRow

/-- The reverse ideal inclusion has exactly one unclosed trace-family input. -/
theorem fIdeal_le_gSpan_of_trace (h t : R) (hHalf : (2 : R) * h = 1)
    (hTrace : ∀ i : Fin 39,
      fRow h t (fNumber (fTrace i)) ∈ Ideal.span (Set.range (gRow h t))) :
    fIdeal h t ≤ Ideal.span (Set.range (gRow h t)) := by
  change Ideal.span (Set.range (fRow h t)) ≤ Ideal.span (Set.range (gRow h t))
  apply Ideal.span_le.mpr
  rintro q ⟨r, rfl⟩
  exact fRow_mem_gSpan_of_trace h t hHalf hTrace r

/-- Equality follows from the already checked forward inclusion and the
explicit trace-row input; this theorem does not establish that input. -/
theorem ideals_eq_of_trace (h t : R) (hHalf : (2 : R) * h = 1)
    (hTrace : ∀ i : Fin 39,
      fRow h t (fNumber (fTrace i)) ∈ Ideal.span (Set.range (gRow h t))) :
    fIdeal h t = Ideal.span (Set.range (gRow h t)) := by
  apply le_antisymm
  · exact fIdeal_le_gSpan_of_trace h t hHalf hTrace
  · exact gSpan_le_fIdeal h t hHalf

end NativePolynomial.ConfigurationResiduals

#check @NativePolynomial.ConfigurationResiduals.fId_mem_gSpan
#check @NativePolynomial.ConfigurationResiduals.fSum_mem_gSpan
#check @NativePolynomial.ConfigurationResiduals.fRow_mem_gSpan_of_trace
#check @NativePolynomial.ConfigurationResiduals.fIdeal_le_gSpan_of_trace
#check @NativePolynomial.ConfigurationResiduals.ideals_eq_of_trace
#print axioms NativePolynomial.ConfigurationResiduals.fId_mem_gSpan
#print axioms NativePolynomial.ConfigurationResiduals.fSum_mem_gSpan
#print axioms NativePolynomial.ConfigurationResiduals.fRow_mem_gSpan_of_trace
#print axioms NativePolynomial.ConfigurationResiduals.fIdeal_le_gSpan_of_trace
#print axioms NativePolynomial.ConfigurationResiduals.ideals_eq_of_trace

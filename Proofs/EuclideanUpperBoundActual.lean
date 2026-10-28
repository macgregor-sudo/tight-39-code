module

public import EuclideanUpperBound
public import ClosedSumConsequences

@[expose] public section

/-! Discharge the closed-sum hypothesis in the box-boundary
induction using the countable closed-sum theorem. The conclusion is
an unconditional small-inductive UPPER bound, not Euclidean normalization.

-/
noncomputable section
namespace SmallInductiveEuclideanA7

/-- Actual D2 discharges the metric finite closed-sum contract. -/
theorem finiteClosedSumContract_proved : FiniteClosedSumContract := by
  intro X ι _ _ _ n F hF hdim hcover
  exact SmallInductiveClosedSum.finite_closed_sum n F hF hdim hcover

theorem euclidean_smallInductiveDimension_upper_bound (n : ℕ) :
    smallInductiveDimension (EuclideanSpace ℝ (Fin n)) ≤ (n : WithBot ℕ∞) :=
  euclidean_smallInductiveDimension_le finiteClosedSumContract_proved n

theorem euclidean_subtype_smallInductiveDimension_upper_bound
    (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) :
    smallInductiveDimension A ≤ (n : WithBot ℕ∞) :=
  euclidean_subtype_smallInductiveDimension_le finiteClosedSumContract_proved n A

#print axioms finiteClosedSumContract_proved
#print axioms euclidean_smallInductiveDimension_upper_bound
#print axioms euclidean_subtype_smallInductiveDimension_upper_bound
end SmallInductiveEuclideanA7

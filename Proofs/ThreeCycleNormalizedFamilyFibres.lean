module

public import ThreeCycleNormalizedParameterRecovery

@[expose] public section

/-!
Exact algebraic fibres of the existing normalized matrix construction.
The parameter-recovery theorem supplies the converse. This composition reuses the
pinned Matrix.conjTranspose_smul, smul_mul and mul_smul lemmas directly.
No new family, parameter carrier, quotient, topology or native gauge claim.
-/

noncomputable section

namespace UnitaryErrorBases.ThreeCycleNormalized

private theorem scalar_star_mul_eq_one (Q : Mat) (c : Complex)
    (hQ : IsSpecialUnitary Q) (hscaled : IsSpecialUnitary (c • Q)) :
    star c * c = 1 := by
  have hu := hscaled.1
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hQ.1] at hu
  have hentry := congrArg (fun A : Mat => A (0 : Index) (0 : Index)) hu
  simpa [mul_comm] using hentry

/-- The reverse fibre implication under the same actual SU3/phase hypotheses. -/
theorem normalizedFamily_eq_of_parameters
    (Q Q' : Mat) (d d' : PhaseTriple)
    (hQ : IsSpecialUnitary Q) (hQ' : IsSpecialUnitary Q')
    (hparameters : d = d' ∧ ∃ c : Complex, c ^ 3 = 1 ∧ Q' = c • Q) :
    normalizedFamily Q d = normalizedFamily Q' d' := by
  rcases hparameters with ⟨rfl, c, _hcube, hcentral⟩
  rw [hcentral] at hQ' ⊢
  have hc : star c * c = 1 := scalar_star_mul_eq_one Q c hQ hQ'
  funext p
  simp only [normalizedFamily, Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, hc, one_smul]

/-- Global two-sided fibre identification, retaining all original hypotheses. -/
theorem normalizedFamily_eq_iff
    (Q Q' : Mat) (d d' : PhaseTriple)
    (hQ : IsSpecialUnitary Q) (hQ' : IsSpecialUnitary Q') :
    normalizedFamily Q d = normalizedFamily Q' d' ↔
      d = d' ∧ ∃ c : Complex, c ^ 3 = 1 ∧ Q' = c • Q :=
  ⟨normalizedFamily_parameter_recovery Q Q' d d' hQ hQ',
    normalizedFamily_eq_of_parameters Q Q' d d' hQ hQ'⟩

end UnitaryErrorBases.ThreeCycleNormalized

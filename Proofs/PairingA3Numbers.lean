module
public import PairingA3Matrix
public import ThreeCycleDimension
@[expose] public section
noncomputable section
namespace Option2StatementA3Matrix
theorem firstOrder_dimension (d : PhaseTriple) : Module.finrank ℝ (firstOrderSpace (monomialFamily d)) = 18 + 2 * resonanceCount d := by exact UnitaryErrorBases.ThreeCycleMatrix.firstOrder_finrank d
theorem resonance_count_cases (d : PhaseTriple) : resonanceCount d = 0 ∨ resonanceCount d = 1 ∨ resonanceCount d = 3 := by exact UnitaryErrorBases.ThreeCycleMatrix.resonanceCount_zero_one_three d
end Option2StatementA3Matrix

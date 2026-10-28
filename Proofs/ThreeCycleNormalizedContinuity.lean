module

public import ThreeCycleNormalizedParameterRecovery
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-!
Joint continuity of ThreeCycleNormalized.normalizedFamily.
The proof reuses the earlier continuity argument for this named family,
using its definition from the parameter-recovery module. Matrix and
PhaseTriple topologies and constraints are unchanged.
No special-unitary group framework, quotient descent, analyticity, immersion,
global embedding or full A2 claim is introduced.
First-party composition of the construction and pinned Mathlib APIs;
imported sources retain their notices. Thanks to their contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, 1676. https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
namespace UnitaryErrorBases.ThreeCycleNormalized

/-- Joint continuity in the original actual matrix and constrained phase
parameters, directly for the named family. -/
theorem continuous_normalizedFamily :
    Continuous (fun qd : Mat × PhaseTriple => normalizedFamily qd.1 qd.2) := by
  unfold normalizedFamily
  apply continuous_pi
  intro p
  have hphase : Continuous (fun qd : Mat × PhaseTriple => phaseMatrix qd.2 p.2) := by
    unfold phaseMatrix
    apply Continuous.matrix_diagonal
    apply continuous_pi
    intro j
    by_cases hb : p.2 = 2
    · simp only [if_pos hb]
      exact (continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)
    · simp only [if_neg hb]
      exact continuous_const
  have hmono : Continuous (fun qd : Mat × PhaseTriple => monomialFamily qd.2 p) := by
    unfold monomialFamily
    exact (continuous_const.mul hphase).mul continuous_const
  exact (continuous_fst.mul hmono).mul continuous_fst.matrix_conjTranspose

end UnitaryErrorBases.ThreeCycleNormalized

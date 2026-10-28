module

public import SpecialUnitaryLocalChart
public import Mathlib.Geometry.Manifold.IsManifold.Basic

@[expose] public section

/-!
# A real analytic atlas on the actual standard special-unitary group

The named charted-space structure uses the existing SU3
topology and the exact frozen local charts. Compatibility is proved on actual
overlap sources. Order omega is analytic, not merely infinitely differentiable.
No global instance is registered: consumers explicitly select the named
structure. No central-quotient atlas or normalized-family immersion is claimed.
First-party composition of proved chart expressions and pinned manifold APIs;
no upstream proof body copied. Thanks to the contributors. “If I have seen
further it is by standing on the sholders of Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise Topology
open UnitaryErrorBases.ThreeCycleNormalized

namespace UnitaryErrorBases.SpecialUnitaryConstraints

/-- The actual transition, from the Q₁ chart to the Q₀ chart, in raw matrix form. -/
theorem specialUnitaryLocalChart_transition_apply (Q₀ Q₁ : StandardSpecialUnitary)
    (k : ConstraintTangent) (hk : k ∈ (specialUnitaryLocalChart Q₁).target) :
    ((specialUnitaryLocalChart Q₁).symm.trans (specialUnitaryLocalChart Q₀)) k =
      specialUnitaryIdentityCoordinates
        (Q₀.val.conjTranspose * (Q₁.val * specialUnitaryIdentityParam k)) := by
  rw [OpenPartialHomeomorph.trans_apply, specialUnitaryLocalChart_apply,
    specialUnitaryLocalChart_symm_val Q₁ k hk]

/-- Real analytic compatibility on exactly the source of each actual transition. -/
theorem analyticOnNhd_specialUnitaryLocalChart_transition
    (Q₀ Q₁ : StandardSpecialUnitary) :
    AnalyticOnNhd ℝ
      ((specialUnitaryLocalChart Q₁).symm.trans (specialUnitaryLocalChart Q₀))
      ((specialUnitaryLocalChart Q₁).symm.trans (specialUnitaryLocalChart Q₀)).source := by
  intro k hk
  exact (analyticOnNhd_specialUnitaryLocalChart_coordinates Q₀ _ (Set.mem_univ _)).comp
    (analyticOnNhd_specialUnitaryLocalChart_symm_val Q₁ k hk.1)

theorem contDiffOn_specialUnitaryLocalChart_transition (Q₀ Q₁ : StandardSpecialUnitary) :
    ContDiffOn ℝ ω
      ((specialUnitaryLocalChart Q₁).symm.trans (specialUnitaryLocalChart Q₀))
      ((specialUnitaryLocalChart Q₁).symm.trans (specialUnitaryLocalChart Q₀)).source :=
  (analyticOnNhd_specialUnitaryLocalChart_transition Q₀ Q₁).contDiffOn
    ((specialUnitaryLocalChart Q₁).symm.trans (specialUnitaryLocalChart Q₀)).open_source.uniqueDiffOn

/-- The identity model uses the existing kernel topology, definitionally. -/
theorem constraintTangent_model_topology :
    (inferInstance : NormedAddCommGroup ConstraintTangent).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace ConstraintTangent) := rfl

/-- A named atlas on the existing topology, with the proved chart at every point.
The model topology is annotated to guide reducible typeclass unification. -/
@[instance_reducible]
def specialUnitaryChartedSpace :
    @ChartedSpace ConstraintTangent
      (inferInstance : NormedAddCommGroup ConstraintTangent).toUniformSpace.toTopologicalSpace
      StandardSpecialUnitary inferInstance where
  atlas := Set.range specialUnitaryLocalChart
  chartAt := specialUnitaryLocalChart
  mem_chart_source := self_mem_specialUnitaryLocalChart_source
  chart_mem_atlas Q := ⟨Q, rfl⟩

-- Deliberately local: importing this module does not choose a global chart instance.
attribute [local instance] specialUnitaryChartedSpace

theorem specialUnitaryChartedSpace_chartAt (Q : StandardSpecialUnitary) :
    @chartAt ConstraintTangent _ StandardSpecialUnitary _ specialUnitaryChartedSpace Q =
      specialUnitaryLocalChart Q := rfl

theorem specialUnitaryChartedSpace_atlas :
    @atlas ConstraintTangent _ StandardSpecialUnitary _ specialUnitaryChartedSpace =
      Set.range specialUnitaryLocalChart := rfl

/-- Actual analytic manifold structure, proved by the derived overlap compatibility. -/
theorem specialUnitary_isManifold :
    IsManifold 𝓘(ℝ, ConstraintTangent) ω StandardSpecialUnitary := by
  apply isManifold_of_contDiffOn 𝓘(ℝ, ConstraintTangent) ω StandardSpecialUnitary
  rintro e e' ⟨Q₁, rfl⟩ ⟨Q₀, rfl⟩
  change ContDiffOn ℝ ω
    ((specialUnitaryLocalChart Q₁).symm.trans (specialUnitaryLocalChart Q₀))
    (id ⁻¹' ((specialUnitaryLocalChart Q₁).symm.trans (specialUnitaryLocalChart Q₀)).source ∩
      Set.range id)
  simpa only [Set.preimage_id, Set.range_id, Set.inter_univ] using
    contDiffOn_specialUnitaryLocalChart_transition Q₀ Q₁

/-- Compatibility as mathlib's actual analytic transition groupoid. -/
theorem specialUnitary_hasGroupoid :
    HasGroupoid StandardSpecialUnitary (contDiffGroupoid ω 𝓘(ℝ, ConstraintTangent)) :=
  specialUnitary_isManifold.toHasGroupoid

/-- The real model of this particular analytic manifold has dimension exactly eight. -/
theorem specialUnitary_analytic_model_finrank :
    IsManifold 𝓘(ℝ, ConstraintTangent) ω StandardSpecialUnitary ∧
      Module.finrank ℝ ConstraintTangent = 8 :=
  ⟨specialUnitary_isManifold, finrank_constraintDifferential_kernel⟩

end UnitaryErrorBases.SpecialUnitaryConstraints

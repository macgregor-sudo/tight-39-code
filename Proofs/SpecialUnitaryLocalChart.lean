module

public import SpecialUnitaryImplicitChart
public import SpecialUnitaryTranslatedConstraints
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

@[expose] public section

/-!
# Local charts on the actual standard special-unitary subtype

The existing SU3 subtype topology and literal constraint
kernel are retained. Neighborhoods are chosen from proved local membership and
recovery statements. The inverse outside the valid parameter neighborhood is
irrelevant to the partial homeomorphism. No atlas or quotient immersion is claimed.
First-party assembly using imported owners and pinned mathlib APIs; no upstream
proof body copied. Thanks to the contributors. “If I have seen further it is by
standing on the sholders of Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
open scoped Matrix.Norms.Elementwise Topology
open Filter
open UnitaryErrorBases.ThreeCycleNormalized

namespace UnitaryErrorBases.SpecialUnitaryConstraints

/-- A proved analytic, SU3-valued parameter neighborhood, chosen once. -/
def specialUnitaryChartParameterDomain : Set ConstraintTangent :=
  Classical.choose exists_open_specialUnitaryIdentityParam_domain

theorem specialUnitaryChartParameterDomain_spec :
    IsOpen specialUnitaryChartParameterDomain ∧ 0 ∈ specialUnitaryChartParameterDomain ∧
      AnalyticOnNhd ℝ specialUnitaryIdentityParam specialUnitaryChartParameterDomain ∧
      ∀ k ∈ specialUnitaryChartParameterDomain,
        specialUnitaryIdentityParam k ∈ Matrix.specialUnitaryGroup Index ℂ :=
  Classical.choose_spec exists_open_specialUnitaryIdentityParam_domain

theorem exists_open_specialUnitaryChartRecoveryDomain :
    ∃ V : Set Mat, IsOpen V ∧ 1 ∈ V ∧ ∀ Q ∈ V,
      Q ∈ Matrix.specialUnitaryGroup Index ℂ ↔
        specialUnitaryIdentityParam (specialUnitaryIdentityCoordinates Q) = Q := by
  obtain ⟨V, hV, ho, h1⟩ := eventually_nhds_iff.mp
    eventually_mem_specialUnitary_iff_param_coordinates
  exact ⟨V, ho, h1, hV⟩

/-- A proved ambient neighborhood where the actual SU3 inverse law holds. -/
def specialUnitaryChartRecoveryDomain : Set Mat :=
  Classical.choose exists_open_specialUnitaryChartRecoveryDomain

theorem specialUnitaryChartRecoveryDomain_spec :
    IsOpen specialUnitaryChartRecoveryDomain ∧ 1 ∈ specialUnitaryChartRecoveryDomain ∧
      ∀ Q ∈ specialUnitaryChartRecoveryDomain,
        Q ∈ Matrix.specialUnitaryGroup Index ℂ ↔
          specialUnitaryIdentityParam (specialUnitaryIdentityCoordinates Q) = Q :=
  Classical.choose_spec exists_open_specialUnitaryChartRecoveryDomain

def specialUnitaryIdentityChartSource : Set StandardSpecialUnitary :=
  {Q | Q.val ∈ specialUnitaryChartRecoveryDomain ∧
    specialUnitaryIdentityCoordinates Q.val ∈ specialUnitaryChartParameterDomain}

def specialUnitaryIdentityChartTarget : Set ConstraintTangent :=
  specialUnitaryChartParameterDomain ∩
    specialUnitaryIdentityParam ⁻¹' specialUnitaryChartRecoveryDomain

/-- An extension to all parameters; only its values on the target are used. -/
def specialUnitaryIdentityChartInverse (k : ConstraintTangent) : StandardSpecialUnitary := by
  classical
  exact if hk : k ∈ specialUnitaryChartParameterDomain then
    ⟨specialUnitaryIdentityParam k, specialUnitaryChartParameterDomain_spec.2.2.2 k hk⟩
  else 1

theorem specialUnitaryIdentityChartInverse_val (k : ConstraintTangent)
    (hk : k ∈ specialUnitaryChartParameterDomain) :
    (specialUnitaryIdentityChartInverse k).val = specialUnitaryIdentityParam k := by
  simp only [specialUnitaryIdentityChartInverse, dite_eq_left hk]

theorem continuous_specialUnitaryIdentityCoordinates :
    Continuous specialUnitaryIdentityCoordinates :=
  continuous_iff_continuousAt.mpr fun Q =>
    (analyticAt_specialUnitaryIdentityCoordinates Q).continuousAt

/-- A genuine partial homeomorphism of actual SU3 near identity with the literal kernel. -/
def specialUnitaryIdentityChart :
    OpenPartialHomeomorph StandardSpecialUnitary ConstraintTangent where
  toFun Q := specialUnitaryIdentityCoordinates Q.val
  invFun := specialUnitaryIdentityChartInverse
  source := specialUnitaryIdentityChartSource
  target := specialUnitaryIdentityChartTarget
  map_source' := by
    intro Q hQ
    refine ⟨hQ.2, ?_⟩
    change specialUnitaryIdentityParam (specialUnitaryIdentityCoordinates Q.val) ∈
      specialUnitaryChartRecoveryDomain
    rw [(specialUnitaryChartRecoveryDomain_spec.2.2 Q.val hQ.1).mp Q.property]
    exact hQ.1
  map_target' := by
    intro k hk
    change (specialUnitaryIdentityChartInverse k).val ∈ specialUnitaryChartRecoveryDomain ∧
      specialUnitaryIdentityCoordinates (specialUnitaryIdentityChartInverse k).val ∈
        specialUnitaryChartParameterDomain
    rw [specialUnitaryIdentityChartInverse_val k hk.1]
    exact ⟨hk.2, by rw [specialUnitaryIdentityCoordinates_param]; exact hk.1⟩
  left_inv' := by
    intro Q hQ
    apply Subtype.ext
    rw [specialUnitaryIdentityChartInverse_val _ hQ.2]
    exact (specialUnitaryChartRecoveryDomain_spec.2.2 Q.val hQ.1).mp Q.property
  right_inv' := by
    intro k hk
    rw [specialUnitaryIdentityChartInverse_val k hk.1]
    exact specialUnitaryIdentityCoordinates_param k
  open_source :=
    (specialUnitaryChartRecoveryDomain_spec.1.preimage continuous_subtype_val).inter
      (specialUnitaryChartParameterDomain_spec.1.preimage
        (continuous_specialUnitaryIdentityCoordinates.comp continuous_subtype_val))
  open_target := specialUnitaryChartParameterDomain_spec.2.2.1.continuousOn.isOpen_inter_preimage
    specialUnitaryChartParameterDomain_spec.1 specialUnitaryChartRecoveryDomain_spec.1
  continuousOn_toFun :=
    (continuous_specialUnitaryIdentityCoordinates.comp continuous_subtype_val).continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun k : specialUnitaryIdentityChartTarget =>
        specialUnitaryIdentityParam k.val) :=
      (specialUnitaryChartParameterDomain_spec.2.2.1.continuousOn.mono
        (fun _ hk => hk.1)).domRestrict
    have hs := hc.subtype_mk (fun k =>
      specialUnitaryChartParameterDomain_spec.2.2.2 k.val k.property.1)
    convert hs using 1
    funext k
    apply Subtype.ext
    exact specialUnitaryIdentityChartInverse_val k.val k.property.1

theorem specialUnitaryIdentityChart_apply (Q : StandardSpecialUnitary) :
    specialUnitaryIdentityChart Q = specialUnitaryIdentityCoordinates Q.val := rfl

theorem specialUnitaryIdentityChart_symm_val (k : ConstraintTangent)
    (hk : k ∈ specialUnitaryIdentityChart.target) :
    (specialUnitaryIdentityChart.symm k).val = specialUnitaryIdentityParam k :=
  specialUnitaryIdentityChartInverse_val k hk.1

theorem one_mem_specialUnitaryIdentityChart_source :
    (1 : StandardSpecialUnitary) ∈ specialUnitaryIdentityChart.source := by
  refine ⟨specialUnitaryChartRecoveryDomain_spec.2.1, ?_⟩
  have h : specialUnitaryIdentityCoordinates (1 : Mat) = 0 := by
    simpa only [specialUnitaryIdentityParam_zero] using specialUnitaryIdentityCoordinates_param 0
  change specialUnitaryIdentityCoordinates (1 : Mat) ∈ specialUnitaryChartParameterDomain
  rw [h]
  exact specialUnitaryChartParameterDomain_spec.2.1

theorem zero_mem_specialUnitaryIdentityChart_target :
    (0 : ConstraintTangent) ∈ specialUnitaryIdentityChart.target := by
  refine ⟨specialUnitaryChartParameterDomain_spec.2.1, ?_⟩
  change specialUnitaryIdentityParam 0 ∈ specialUnitaryChartRecoveryDomain
  rw [specialUnitaryIdentityParam_zero]
  exact specialUnitaryChartRecoveryDomain_spec.2.1

theorem analyticOnNhd_specialUnitaryIdentityChart_symm_val :
    AnalyticOnNhd ℝ (fun k => (specialUnitaryIdentityChart.symm k).val)
      specialUnitaryIdentityChart.target := by
  intro k hk
  apply (specialUnitaryChartParameterDomain_spec.2.2.1 k hk.1).congr
  filter_upwards [specialUnitaryChartParameterDomain_spec.1.mem_nhds hk.1] with l hl
  exact (specialUnitaryIdentityChartInverse_val l hl).symm

/-- Actual left translation as a homeomorphism of the standard SU3 subtype. -/
def specialUnitaryToIdentityHomeomorph (Q₀ : StandardSpecialUnitary) :
    StandardSpecialUnitary ≃ₜ StandardSpecialUnitary where
  toFun Q := ⟨specialUnitaryLeftTranslation Q₀ Q.val,
    (specialUnitaryLeftTranslation_mem_iff Q₀ Q.val).mpr Q.property⟩
  invFun Q := ⟨(specialUnitaryLeftTranslation Q₀).symm Q.val,
    (specialUnitaryLeftTranslation_symm_mem_iff Q₀ Q.val).mpr Q.property⟩
  left_inv Q := Subtype.ext ((specialUnitaryLeftTranslation Q₀).symm_apply_apply Q.val)
  right_inv Q := Subtype.ext ((specialUnitaryLeftTranslation Q₀).apply_symm_apply Q.val)
  continuous_toFun :=
    ((specialUnitaryLeftTranslation Q₀).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((specialUnitaryLeftTranslation Q₀).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem specialUnitaryToIdentityHomeomorph_apply_self (Q₀ : StandardSpecialUnitary) :
    specialUnitaryToIdentityHomeomorph Q₀ Q₀ = 1 :=
  Subtype.ext (specialUnitaryLeftTranslation_apply_self Q₀)

/-- Genuine local charts at every actual standard SU3 matrix. -/
def specialUnitaryLocalChart (Q₀ : StandardSpecialUnitary) :
    OpenPartialHomeomorph StandardSpecialUnitary ConstraintTangent :=
  (specialUnitaryToIdentityHomeomorph Q₀).transOpenPartialHomeomorph specialUnitaryIdentityChart

theorem specialUnitaryLocalChart_apply (Q₀ Q : StandardSpecialUnitary) :
    specialUnitaryLocalChart Q₀ Q =
      specialUnitaryIdentityCoordinates (Q₀.val.conjTranspose * Q.val) := rfl

theorem specialUnitaryLocalChart_source (Q₀ : StandardSpecialUnitary) :
    (specialUnitaryLocalChart Q₀).source =
      (specialUnitaryToIdentityHomeomorph Q₀) ⁻¹' specialUnitaryIdentityChart.source := rfl

theorem specialUnitaryLocalChart_target (Q₀ : StandardSpecialUnitary) :
    (specialUnitaryLocalChart Q₀).target = specialUnitaryIdentityChart.target := rfl

theorem self_mem_specialUnitaryLocalChart_source (Q₀ : StandardSpecialUnitary) :
    Q₀ ∈ (specialUnitaryLocalChart Q₀).source := by
  rw [specialUnitaryLocalChart_source]
  change specialUnitaryToIdentityHomeomorph Q₀ Q₀ ∈ specialUnitaryIdentityChart.source
  rw [specialUnitaryToIdentityHomeomorph_apply_self]
  exact one_mem_specialUnitaryIdentityChart_source

theorem zero_mem_specialUnitaryLocalChart_target (Q₀ : StandardSpecialUnitary) :
    (0 : ConstraintTangent) ∈ (specialUnitaryLocalChart Q₀).target :=
  zero_mem_specialUnitaryIdentityChart_target

theorem specialUnitaryLocalChart_apply_self (Q₀ : StandardSpecialUnitary) :
    specialUnitaryLocalChart Q₀ Q₀ = 0 := by
  change specialUnitaryIdentityCoordinates (specialUnitaryLeftTranslation Q₀ Q₀.val) = 0
  rw [specialUnitaryLeftTranslation_apply_self]
  simpa only [specialUnitaryIdentityParam_zero] using specialUnitaryIdentityCoordinates_param 0

theorem specialUnitaryLocalChart_symm_val (Q₀ : StandardSpecialUnitary)
    (k : ConstraintTangent) (hk : k ∈ (specialUnitaryLocalChart Q₀).target) :
    ((specialUnitaryLocalChart Q₀).symm k).val = Q₀.val * specialUnitaryIdentityParam k := by
  change Q₀.val * (specialUnitaryIdentityChart.symm k).val = _
  rw [specialUnitaryIdentityChart_symm_val k hk]

theorem specialUnitaryLocalChart_symm_zero (Q₀ : StandardSpecialUnitary) :
    (specialUnitaryLocalChart Q₀).symm 0 = Q₀ := by
  apply Subtype.ext
  rw [specialUnitaryLocalChart_symm_val Q₀ 0 (zero_mem_specialUnitaryLocalChart_target Q₀),
    specialUnitaryIdentityParam_zero, Matrix.mul_one]

/-- The forward coordinate formula extends real analytically to every ambient matrix. -/
theorem analyticOnNhd_specialUnitaryLocalChart_coordinates (Q₀ : StandardSpecialUnitary) :
    AnalyticOnNhd ℝ (fun A : Mat =>
      specialUnitaryIdentityCoordinates (Q₀.val.conjTranspose * A)) Set.univ := by
  intro A _
  exact (analyticAt_specialUnitaryIdentityCoordinates _).comp
    ((specialUnitaryLeftTranslation Q₀).toContinuousLinearMap.analyticAt A)

/-- The chart inverse has its actual raw matrix expression analytic on its open target. -/
theorem analyticOnNhd_specialUnitaryLocalChart_symm_val (Q₀ : StandardSpecialUnitary) :
    AnalyticOnNhd ℝ (fun k => ((specialUnitaryLocalChart Q₀).symm k).val)
      (specialUnitaryLocalChart Q₀).target := by
  intro k hk
  exact ((specialUnitaryLeftTranslation Q₀).symm.toContinuousLinearMap.analyticAt _).comp
    (analyticOnNhd_specialUnitaryIdentityChart_symm_val k hk)

end UnitaryErrorBases.SpecialUnitaryConstraints

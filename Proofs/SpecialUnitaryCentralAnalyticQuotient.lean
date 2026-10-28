module

public import SpecialUnitaryAnalyticAtlas
public import SpecialUnitaryCentralLocalLift
public import Mathlib.Geometry.Manifold.ContMDiff.Defs

@[expose] public section

/-!
# Analytic local charts on the literal standard SU3 center quotient

Existing quotient topology, full actual group center, and
literal constraint-kernel model are retained. Analytic compatibility is derived
from local uniqueness of the admitted covering lifts and analytic fixed-matrix
translation; no analytic-lift or descent assumption is introduced. Named chart
structures are used, with no unqualified global instances.
First-party composition of pinned APIs and frozen owners, no upstream proof
body copied. Thanks to the contributors. “If I have seen further it is by
standing on the sholders of Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise Topology
open Filter
open UnitaryErrorBases.ThreeCycleNormalized

namespace UnitaryErrorBases.SpecialUnitaryConstraints

/-- The inverse of each admitted local lift is the literal quotient projection. -/
theorem standardCenterLocalLift_symm_apply (Q R : StandardSpecialUnitary) :
    (standardCenterLocalLift Q).symm R =
      (QuotientGroup.mk R : SpecialUnitaryCenterQuotient) :=
  congrFun (isLocalHomeomorph_standard_center_projection.localInverseAt_symm Q) R

theorem standardCenterLocalLift_mem_target (Q : StandardSpecialUnitary) :
    Q ∈ (standardCenterLocalLift Q).target := by
  have h := (standardCenterLocalLift Q).map_source (standardCenterLocalLift_mem_source Q)
  rwa [standardCenterLocalLift_apply_self] at h

/-- A lift of a continuous actual SU3 map differs locally by one fixed actual center element.
This follows from the open covering target and its inverse law, not analytic descent. -/
theorem standardCenterLocalLift_eventually_central_mul
    {X : Type*} [TopologicalSpace X] (Q : StandardSpecialUnitary)
    (f : X → StandardSpecialUnitary) (x : X) (hf : ContinuousAt f x)
    (hx : (QuotientGroup.mk (f x) : SpecialUnitaryCenterQuotient) ∈
      (standardCenterLocalLift Q).source) :
    ∃ c : Subgroup.center StandardSpecialUnitary,
      ∀ᶠ y in 𝓝 x, standardCenterLocalLift Q (QuotientGroup.mk (f y)) = c.val * f y := by
  let c : StandardSpecialUnitary := standardCenterLocalLift Q (QuotientGroup.mk (f x)) / f x
  have hc : c ∈ Subgroup.center StandardSpecialUnitary :=
    QuotientGroup.eq_iff_div_mem.mp (standardCenterLocalLift_section Q _ hx)
  have hc1 : (QuotientGroup.mk c : SpecialUnitaryCenterQuotient) = 1 :=
    (QuotientGroup.eq_one_iff c).mpr hc
  have hbase : c * f x = standardCenterLocalLift Q (QuotientGroup.mk (f x)) :=
    div_mul_cancel _ _
  have htarget : c * f x ∈ (standardCenterLocalLift Q).target := by
    rw [hbase]
    exact (standardCenterLocalLift Q).map_source hx
  have hnear := (continuousAt_const.mul hf).preimage_mem_nhds
    ((standardCenterLocalLift Q).open_target.mem_nhds htarget)
  refine ⟨⟨c, hc⟩, ?_⟩
  filter_upwards [hnear] with y hy
  have h := (standardCenterLocalLift Q).right_inv hy
  change standardCenterLocalLift Q ((standardCenterLocalLift Q).symm (c * f y)) = c * f y at h
  rw [standardCenterLocalLift_symm_apply, QuotientGroup.mk_mul, hc1, one_mul] at h
  exact h

/-- Actual quotient coordinates through a specified representative. -/
def standardCenterRepresentativeChart (Q : StandardSpecialUnitary) :
    OpenPartialHomeomorph SpecialUnitaryCenterQuotient ConstraintTangent :=
  (standardCenterLocalLift Q).trans (specialUnitaryLocalChart Q)

theorem standardCenterRepresentativeChart_apply (Q : StandardSpecialUnitary)
    (z : SpecialUnitaryCenterQuotient) :
    standardCenterRepresentativeChart Q z =
      specialUnitaryLocalChart Q (standardCenterLocalLift Q z) := rfl

theorem standardCenterRepresentativeChart_symm_apply (Q : StandardSpecialUnitary)
    (k : ConstraintTangent) :
    (standardCenterRepresentativeChart Q).symm k =
      (QuotientGroup.mk ((specialUnitaryLocalChart Q).symm k) :
        SpecialUnitaryCenterQuotient) :=
  standardCenterLocalLift_symm_apply Q _

theorem mk_mem_standardCenterRepresentativeChart_source (Q : StandardSpecialUnitary) :
    (QuotientGroup.mk Q : SpecialUnitaryCenterQuotient) ∈
      (standardCenterRepresentativeChart Q).source := by
  refine ⟨standardCenterLocalLift_mem_source Q, ?_⟩
  change standardCenterLocalLift Q (QuotientGroup.mk Q) ∈ (specialUnitaryLocalChart Q).source
  rw [standardCenterLocalLift_apply_self]
  exact self_mem_specialUnitaryLocalChart_source Q

theorem zero_mem_standardCenterRepresentativeChart_target (Q : StandardSpecialUnitary) :
    (0 : ConstraintTangent) ∈ (standardCenterRepresentativeChart Q).target := by
  refine ⟨zero_mem_specialUnitaryLocalChart_target Q, ?_⟩
  change (specialUnitaryLocalChart Q).symm 0 ∈ (standardCenterLocalLift Q).target
  rw [specialUnitaryLocalChart_symm_zero]
  exact standardCenterLocalLift_mem_target Q

/-- Analyticity of a concrete covering-lift expression in actual SU3 coordinates. -/
theorem analyticAt_standardCenterLocalLift_coordinates
    (P Q R : StandardSpecialUnitary) (k : ConstraintTangent)
    (hk : k ∈ (specialUnitaryLocalChart R).target)
    (hsource : (QuotientGroup.mk ((specialUnitaryLocalChart R).symm k) :
      SpecialUnitaryCenterQuotient) ∈ (standardCenterLocalLift Q).source) :
    AnalyticAt ℝ (fun y => specialUnitaryLocalChart P
      (standardCenterLocalLift Q (QuotientGroup.mk ((specialUnitaryLocalChart R).symm y)))) k := by
  obtain ⟨c, hc⟩ := standardCenterLocalLift_eventually_central_mul Q
    (specialUnitaryLocalChart R).symm k
    ((specialUnitaryLocalChart R).symm.continuousAt hk) hsource
  have ha := (analyticOnNhd_specialUnitaryLocalChart_coordinates P _ (Set.mem_univ _)).comp
    (((specialUnitaryLeftTranslation c.val).symm.toContinuousLinearMap.analyticAt _).comp
      (analyticOnNhd_specialUnitaryLocalChart_symm_val R k hk))
  apply ha.congr
  filter_upwards [hc] with y hy
  rw [hy, specialUnitaryLocalChart_apply]
  rfl

/-- All actual quotient-chart overlaps are real analytic. -/
theorem analyticOnNhd_standardCenterRepresentativeChart_transition
    (Q₀ Q₁ : StandardSpecialUnitary) :
    AnalyticOnNhd ℝ
      ((standardCenterRepresentativeChart Q₁).symm.trans (standardCenterRepresentativeChart Q₀))
      ((standardCenterRepresentativeChart Q₁).symm.trans
        (standardCenterRepresentativeChart Q₀)).source := by
  intro k hk
  have hsource : (QuotientGroup.mk ((specialUnitaryLocalChart Q₁).symm k) :
      SpecialUnitaryCenterQuotient) ∈ (standardCenterLocalLift Q₀).source := by
    have h := hk.2.1
    change (standardCenterRepresentativeChart Q₁).symm k ∈
      (standardCenterLocalLift Q₀).source at h
    rwa [standardCenterRepresentativeChart_symm_apply] at h
  have h := analyticAt_standardCenterLocalLift_coordinates Q₀ Q₀ Q₁ k hk.1.1 hsource
  convert h using 1
  funext y
  rw [OpenPartialHomeomorph.trans_apply, standardCenterRepresentativeChart_symm_apply,
    standardCenterRepresentativeChart_apply]

/-- A choice of actual representative, used only to select a chart at each quotient point. -/
def standardCenterRepresentative (z : SpecialUnitaryCenterQuotient) : StandardSpecialUnitary :=
  Classical.choose (QuotientGroup.mk_surjective z)

theorem standardCenterRepresentative_mk (z : SpecialUnitaryCenterQuotient) :
    (QuotientGroup.mk (standardCenterRepresentative z) : SpecialUnitaryCenterQuotient) = z :=
  Classical.choose_spec (QuotientGroup.mk_surjective z)

/-- Named charts on the existing literal group-center quotient topology. -/
@[instance_reducible]
def standardCenterQuotientChartedSpace :
    @ChartedSpace ConstraintTangent
      (inferInstance : NormedAddCommGroup ConstraintTangent).toUniformSpace.toTopologicalSpace
      SpecialUnitaryCenterQuotient inferInstance where
  atlas := Set.range standardCenterRepresentativeChart
  chartAt z := standardCenterRepresentativeChart (standardCenterRepresentative z)
  mem_chart_source z := by
    simpa only [standardCenterRepresentative_mk] using
      mk_mem_standardCenterRepresentativeChart_source (standardCenterRepresentative z)
  chart_mem_atlas z := ⟨standardCenterRepresentative z, rfl⟩

attribute [local instance] specialUnitaryChartedSpace standardCenterQuotientChartedSpace

theorem standardCenterQuotientChartedSpace_chartAt (z : SpecialUnitaryCenterQuotient) :
    @chartAt ConstraintTangent _ SpecialUnitaryCenterQuotient _ standardCenterQuotientChartedSpace z =
      standardCenterRepresentativeChart (standardCenterRepresentative z) := rfl

theorem standardCenterQuotient_isManifold :
    IsManifold 𝓘(ℝ, ConstraintTangent) ω SpecialUnitaryCenterQuotient := by
  apply isManifold_of_contDiffOn 𝓘(ℝ, ConstraintTangent) ω SpecialUnitaryCenterQuotient
  rintro e e' ⟨Q₁, rfl⟩ ⟨Q₀, rfl⟩
  change ContDiffOn ℝ ω
    ((standardCenterRepresentativeChart Q₁).symm.trans (standardCenterRepresentativeChart Q₀))
    (id ⁻¹' ((standardCenterRepresentativeChart Q₁).symm.trans
      (standardCenterRepresentativeChart Q₀)).source ∩ Set.range id)
  simp only [Set.preimage_id, Set.range_id, Set.inter_univ]
  exact (analyticOnNhd_standardCenterRepresentativeChart_transition Q₀ Q₁).contDiffOn
    ((standardCenterRepresentativeChart Q₁).symm.trans
      (standardCenterRepresentativeChart Q₀)).open_source.uniqueDiffOn

theorem standardCenterQuotient_analytic_model_finrank :
    IsManifold 𝓘(ℝ, ConstraintTangent) ω SpecialUnitaryCenterQuotient ∧
      Module.finrank ℝ ConstraintTangent = 8 :=
  ⟨standardCenterQuotient_isManifold, finrank_constraintDifferential_kernel⟩

attribute [local instance] specialUnitary_isManifold standardCenterQuotient_isManifold

/-- The projection agrees with the adapted SU3 coordinates on the actual covering target. -/
theorem standardCenterRepresentativeChart_mk (Q R : StandardSpecialUnitary)
    (hR : R ∈ (standardCenterLocalLift Q).target) :
    standardCenterRepresentativeChart Q (QuotientGroup.mk R) = specialUnitaryLocalChart Q R := by
  have h := (standardCenterLocalLift Q).right_inv hR
  rw [standardCenterLocalLift_symm_apply] at h
  rw [standardCenterRepresentativeChart_apply, h]

/-- In adapted coordinates the literal quotient projection is exactly identity. -/
theorem standardCenterProjection_coordinates (Q : StandardSpecialUnitary)
    (k : ConstraintTangent) (hk : k ∈ (standardCenterRepresentativeChart Q).target) :
    standardCenterRepresentativeChart Q (QuotientGroup.mk ((specialUnitaryLocalChart Q).symm k)) =
      k := by
  rw [← standardCenterRepresentativeChart_symm_apply]
  exact (standardCenterRepresentativeChart Q).right_inv hk

theorem analyticOnNhd_standardCenterProjection_coordinates (Q : StandardSpecialUnitary) :
    AnalyticOnNhd ℝ (fun k => standardCenterRepresentativeChart Q
      (QuotientGroup.mk ((specialUnitaryLocalChart Q).symm k)))
      (standardCenterRepresentativeChart Q).target := by
  intro k hk
  apply analyticAt_id.congr
  filter_upwards [(standardCenterRepresentativeChart Q).open_target.mem_nhds hk] with l hl
  exact (standardCenterProjection_coordinates Q l hl).symm

/-- The literal covering projection is real analytic for the two explicitly selected atlases. -/
theorem contMDiff_standard_center_projection :
    ContMDiff 𝓘(ℝ, ConstraintTangent) 𝓘(ℝ, ConstraintTangent) ω
      (QuotientGroup.mk : StandardSpecialUnitary → SpecialUnitaryCenterQuotient) := by
  intro Q
  have he : specialUnitaryLocalChart Q ∈
      IsManifold.maximalAtlas 𝓘(ℝ, ConstraintTangent) ω StandardSpecialUnitary :=
    IsManifold.subset_maximalAtlas ⟨Q, rfl⟩
  have he' : standardCenterRepresentativeChart Q ∈
      IsManifold.maximalAtlas 𝓘(ℝ, ConstraintTangent) ω SpecialUnitaryCenterQuotient :=
    IsManifold.subset_maximalAtlas ⟨Q, rfl⟩
  apply (contMDiffAt_iff_of_mem_maximalAtlas he he'
    (self_mem_specialUnitaryLocalChart_source Q)
    (mk_mem_standardCenterRepresentativeChart_source Q)).mpr
  refine ⟨isCoveringMap_standard_center_projection.continuous.continuousAt, ?_⟩
  change ContDiffWithinAt ℝ ω (fun k => standardCenterRepresentativeChart Q
    (QuotientGroup.mk ((specialUnitaryLocalChart Q).symm k)))
    (Set.range id) (specialUnitaryLocalChart Q Q)
  rw [specialUnitaryLocalChart_apply_self]
  exact (analyticOnNhd_standardCenterProjection_coordinates Q 0
    (zero_mem_standardCenterRepresentativeChart_target Q)).contDiffAt.contDiffWithinAt

/-- Each actual local section is analytic at every point of its open source. -/
theorem contMDiffAt_standardCenterLocalLift (Q : StandardSpecialUnitary)
    (z : SpecialUnitaryCenterQuotient) (hz : z ∈ (standardCenterLocalLift Q).source) :
    ContMDiffAt 𝓘(ℝ, ConstraintTangent) 𝓘(ℝ, ConstraintTangent) ω
      (standardCenterLocalLift Q) z := by
  let R := standardCenterLocalLift Q z
  have hR : (QuotientGroup.mk R : SpecialUnitaryCenterQuotient) = z :=
    standardCenterLocalLift_section Q z hz
  have he : standardCenterRepresentativeChart R ∈
      IsManifold.maximalAtlas 𝓘(ℝ, ConstraintTangent) ω SpecialUnitaryCenterQuotient :=
    IsManifold.subset_maximalAtlas ⟨R, rfl⟩
  have he' : specialUnitaryLocalChart R ∈
      IsManifold.maximalAtlas 𝓘(ℝ, ConstraintTangent) ω StandardSpecialUnitary :=
    IsManifold.subset_maximalAtlas ⟨R, rfl⟩
  have hzchart : z ∈ (standardCenterRepresentativeChart R).source := by
    rw [← hR]
    exact mk_mem_standardCenterRepresentativeChart_source R
  apply (contMDiffAt_iff_of_mem_maximalAtlas he he' hzchart
    (self_mem_specialUnitaryLocalChart_source R)).mpr
  refine ⟨(standardCenterLocalLift Q).continuousAt hz, ?_⟩
  change ContDiffWithinAt ℝ ω (fun k => specialUnitaryLocalChart R
    (standardCenterLocalLift Q ((standardCenterRepresentativeChart R).symm k)))
    (Set.range id) (standardCenterRepresentativeChart R z)
  have hz0 : standardCenterRepresentativeChart R z = 0 := by
    rw [← hR, standardCenterRepresentativeChart_mk R R (standardCenterLocalLift_mem_target R),
      specialUnitaryLocalChart_apply_self]
  rw [hz0]
  have hs : (QuotientGroup.mk ((specialUnitaryLocalChart R).symm 0) :
      SpecialUnitaryCenterQuotient) ∈ (standardCenterLocalLift Q).source := by
    rwa [specialUnitaryLocalChart_symm_zero, hR]
  have ha := analyticAt_standardCenterLocalLift_coordinates R Q R 0
    (zero_mem_specialUnitaryLocalChart_target R) hs
  have heq : (fun k => specialUnitaryLocalChart R
      (standardCenterLocalLift Q ((standardCenterRepresentativeChart R).symm k))) =
      (fun k => specialUnitaryLocalChart R
        (standardCenterLocalLift Q (QuotientGroup.mk ((specialUnitaryLocalChart R).symm k)))) := by
    funext k
    rw [standardCenterRepresentativeChart_symm_apply]
  rw [heq]
  exact ha.contDiffAt.contDiffWithinAt

theorem contMDiffOn_standardCenterLocalLift (Q : StandardSpecialUnitary) :
    ContMDiffOn 𝓘(ℝ, ConstraintTangent) 𝓘(ℝ, ConstraintTangent) ω
      (standardCenterLocalLift Q) (standardCenterLocalLift Q).source :=
  fun z hz => (contMDiffAt_standardCenterLocalLift Q z hz).contMDiffWithinAt

end UnitaryErrorBases.SpecialUnitaryConstraints

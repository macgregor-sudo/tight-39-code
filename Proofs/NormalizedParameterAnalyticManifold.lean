module
public import PhaseExponentialLocalChart
public import SpecialUnitaryAnalyticAtlas
public import Mathlib.Geometry.Manifold.ImmersionDiff

@[expose] public section
noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise Topology
open UnitaryErrorBases.SpecialUnitaryConstraints

namespace UnitaryErrorBases.ThreeCycleNormalized

/-- Named atlas on the unchanged actual phase subtype topology. -/
@[instance_reducible]
def phaseExponentialChartedSpace :
    @ChartedSpace (ℝ × ℝ)
      (inferInstance : NormedAddCommGroup (ℝ × ℝ)).toUniformSpace.toTopologicalSpace
      PhaseTriple inferInstance where
  atlas := Set.range (fun d => (phaseExponentialLocalParam d).symm)
  chartAt d := (phaseExponentialLocalParam d).symm
  mem_chart_source := self_mem_phaseExponentialLocalParam_target
  chart_mem_atlas d := ⟨d, rfl⟩

attribute [local instance] phaseExponentialChartedSpace

theorem phaseExponentialChartedSpace_chartAt (d : PhaseTriple) :
    @chartAt (ℝ × ℝ) _ PhaseTriple _ phaseExponentialChartedSpace d =
      (phaseExponentialLocalParam d).symm := rfl

theorem phaseExponential_isManifold : IsManifold 𝓘(ℝ, ℝ × ℝ) ω PhaseTriple := by
  apply isManifold_of_contDiffOn 𝓘(ℝ, ℝ × ℝ) ω PhaseTriple
  rintro e e' ⟨d₁, rfl⟩ ⟨d₀, rfl⟩
  have ha : AnalyticOnNhd ℝ
      ((phaseExponentialLocalParam d₁).trans (phaseExponentialLocalParam d₀).symm)
      ((phaseExponentialLocalParam d₁).trans (phaseExponentialLocalParam d₀).symm).source := by
    intro x hx
    exact analyticAt_phaseExponentialLocalParam_transition d₀ d₁ x hx.1 hx.2
  change ContDiffOn ℝ ω
    ((phaseExponentialLocalParam d₁).trans (phaseExponentialLocalParam d₀).symm)
    (id ⁻¹' ((phaseExponentialLocalParam d₁).trans
      (phaseExponentialLocalParam d₀).symm).source ∩ Set.range id)
  simpa only [Set.preimage_id, Set.range_id, Set.inter_univ] using
    ha.contDiffOn ((phaseExponentialLocalParam d₁).trans
      (phaseExponentialLocalParam d₀).symm).open_source.uniqueDiffOn

end UnitaryErrorBases.ThreeCycleNormalized

namespace CompactAlbert
open UnitaryErrorBases UnitaryErrorBases.ThreeCycleNormalized

abbrev NormalizedParameter := StandardSpecialUnitary × PhaseTriple

attribute [local instance] specialUnitaryChartedSpace phaseExponentialChartedSpace

/-- The product of the two proved named atlases, on the original product topology. -/
@[instance_reducible]
def normalizedParameterChartedSpace :
    @ChartedSpace NativeGraphParameters
      (inferInstance : NormedAddCommGroup NativeGraphParameters).toUniformSpace.toTopologicalSpace
      NormalizedParameter inferInstance := by
  exact @prodChartedSpace ConstraintTangent _ StandardSpecialUnitary _ specialUnitaryChartedSpace
    (ℝ × ℝ) _ PhaseTriple _ phaseExponentialChartedSpace

attribute [local instance] normalizedParameterChartedSpace

theorem normalizedParameter_isManifold :
    IsManifold 𝓘(ℝ, NativeGraphParameters) ω NormalizedParameter := by
  have := specialUnitary_isManifold
  have := phaseExponential_isManifold
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod StandardSpecialUnitary PhaseTriple

theorem normalizedParameter_model_finrank :
    IsManifold 𝓘(ℝ, NativeGraphParameters) ω NormalizedParameter ∧
      Module.finrank ℝ NativeGraphParameters = 10 :=
  ⟨normalizedParameter_isManifold, finrank_nativeGraphParameters⟩

theorem normalizedParameterChartedSpace_chartAt (p : NormalizedParameter) :
    @chartAt NativeGraphParameters _ NormalizedParameter _ normalizedParameterChartedSpace p =
      (specialUnitaryLocalChart p.1).prod (phaseExponentialLocalParam p.2).symm := rfl

theorem zero_mem_normalizedParameter_chartTarget (p : NormalizedParameter) :
    (0 : NativeGraphParameters) ∈ (@chartAt NativeGraphParameters _ NormalizedParameter _ normalizedParameterChartedSpace p).target :=
  ⟨zero_mem_specialUnitaryLocalChart_target p.1,
    zero_mem_phaseExponentialLocalParam_source p.2⟩

theorem normalizedParameter_chartAt_self (p : NormalizedParameter) :
    @chartAt NativeGraphParameters _ NormalizedParameter _ normalizedParameterChartedSpace p p = 0 := by
  change (specialUnitaryLocalChart p.1 p.1, (phaseExponentialLocalParam p.2).symm p.2) = 0
  apply Prod.ext
  · exact specialUnitaryLocalChart_apply_self p.1
  · change (phaseExponentialLocalParam p.2).symm p.2 = (0 : ℝ × ℝ)
    have h := (phaseExponentialLocalParam p.2).left_inv
      (zero_mem_phaseExponentialLocalParam_source p.2)
    simpa only [phaseExponentialLocalParam_apply, phaseExpParam_zero] using h

/-- The chosen product chart inverse has exactly the two frozen raw formulas. -/
theorem normalizedParameter_chart_symm_apply (p : NormalizedParameter) (x : NativeGraphParameters)
    (hx : x ∈ (@chartAt NativeGraphParameters _ NormalizedParameter _ normalizedParameterChartedSpace p).target) :
    ((@chartAt NativeGraphParameters _ NormalizedParameter _ normalizedParameterChartedSpace p).symm x).1.val = specialUnitaryGraphParam p.1 x.1 ∧
      ((@chartAt NativeGraphParameters _ NormalizedParameter _ normalizedParameterChartedSpace p).symm x).2 = phaseExpParam p.2 x.2 := by
  constructor
  · exact specialUnitaryLocalChart_symm_val p.1 x.1 hx.1
  · exact phaseExponentialLocalParam_apply p.2 x.2

/-- Actual representative native family on the unchanged standard SU3 × PhaseTriple carrier. -/
def nativeNormalizedParameterFamily (p : NormalizedParameter) : Fin 9 → Fin 3 → Fin 27 → ℝ :=
  nativeNormalizedFamilyExtension (p.1.val, p.2.val)

theorem nativeNormalizedParameterFamily_eq (p : NormalizedParameter) :
    nativeNormalizedParameterFamily p =
      NativeCentralArrayTopology.centralArrayCoordinates (fun _ => false) (nativeThreeCycleArray p.1.val p.2) := rfl

theorem nativeNormalizedParameterFamily_mk (Q : StandardSpecialUnitary) (z : Circle × Circle) :
    nativeNormalizedParameterFamily (Q, phaseOfCircles z) =
      nativeNormalizedProjectiveFamily (QuotientGroup.mk Q, z) := rfl

theorem nativeNormalizedParameterFamily_chart_symm (p : NormalizedParameter) (x : NativeGraphParameters)
    (hx : x ∈ (@chartAt NativeGraphParameters _ NormalizedParameter _ normalizedParameterChartedSpace p).target) :
    nativeNormalizedParameterFamily ((@chartAt NativeGraphParameters _ NormalizedParameter _ normalizedParameterChartedSpace p).symm x) =
      nativeNormalizedGraphFamily p.1 p.2 x := by
  obtain ⟨hQ, hd⟩ := normalizedParameter_chart_symm_apply p x hx
  unfold nativeNormalizedParameterFamily nativeNormalizedGraphFamily
  rw [hQ, hd]

/-- Neighborhood equality transfers the proved native graph differential, without another kernel proof. -/
theorem nativeNormalizedParameterFamily_chart_eventuallyEq (p : NormalizedParameter) :
    (fun x => nativeNormalizedParameterFamily ((@chartAt NativeGraphParameters _ NormalizedParameter _ normalizedParameterChartedSpace p).symm x)) =ᶠ[𝓝 0]
      nativeNormalizedGraphFamily p.1 p.2 := by
  filter_upwards [(@chartAt NativeGraphParameters _ NormalizedParameter _ normalizedParameterChartedSpace p).open_target.mem_nhds
    (zero_mem_normalizedParameter_chartTarget p)] with x hx
  exact nativeNormalizedParameterFamily_chart_symm p x hx

theorem analyticAt_nativeNormalizedParameterFamily_chart (p : NormalizedParameter) :
    AnalyticAt ℝ (fun x => nativeNormalizedParameterFamily ((@chartAt NativeGraphParameters _ NormalizedParameter _ normalizedParameterChartedSpace p).symm x)) 0 :=
  (analyticAt_nativeNormalizedGraphFamily p.1 p.2).congr
    (nativeNormalizedParameterFamily_chart_eventuallyEq p).symm

theorem nativeNormalizedParameterFamily_chart_hasFDerivAt (p : NormalizedParameter) :
    HasFDerivAt (fun x => nativeNormalizedParameterFamily ((@chartAt NativeGraphParameters _ NormalizedParameter _ normalizedParameterChartedSpace p).symm x))
      (fderiv ℝ (nativeNormalizedGraphFamily p.1 p.2) 0) 0 :=
  (nativeNormalizedGraphFamily_hasFDerivAt p.1 p.2).congr_of_eventuallyEq
    (nativeNormalizedParameterFamily_chart_eventuallyEq p)

theorem nativeNormalizedParameterFamily_chart_fderiv_injective (p : NormalizedParameter) :
    Function.Injective (fderiv ℝ
      (fun x => nativeNormalizedParameterFamily ((@chartAt NativeGraphParameters _ NormalizedParameter _ normalizedParameterChartedSpace p).symm x)) 0) := by
  rw [(nativeNormalizedParameterFamily_chart_hasFDerivAt p).fderiv]
  exact nativeNormalizedGraphFamily_fderiv_injective p.1 p.2

theorem continuous_nativeNormalizedParameterFamily : Continuous nativeNormalizedParameterFamily := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hc : ContinuousAt (fun q : NormalizedParameter => (q.1.val, q.2.val)) p :=
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)).continuousAt
  exact (analyticOnNhd_nativeNormalizedFamilyExtension (p.1.val, p.2.val)
    (Set.mem_univ _)).continuousAt.comp_of_eq hc rfl

theorem contMDiff_nativeNormalizedParameterFamily :
    ContMDiff 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Fin 9 → Fin 3 → Fin 27 → ℝ) ω
      nativeNormalizedParameterFamily := by
  intro p
  apply contMDiffAt_iff.mpr
  refine ⟨continuous_nativeNormalizedParameterFamily.continuousAt, ?_⟩
  simpa only [mfld_simps, normalizedParameter_chartAt_self, chartAt_self_eq,
    Function.id_comp, Function.comp_def, OpenPartialHomeomorph.refl_apply] using
    (analyticAt_nativeNormalizedParameterFamily_chart p).contDiffAt.contDiffWithinAt

/-- Differential immersion of the actual representative map on the proved named product atlas. -/
theorem isDiffImmersionAt_nativeNormalizedParameterFamily (p : NormalizedParameter) :
    IsDiffImmersionAt 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Fin 9 → Fin 3 → Fin 27 → ℝ)
      nativeNormalizedParameterFamily p := by
  apply IsDiffImmersionAt.of_injective_of_finiteDimensional
  have hmd := (contMDiff_nativeNormalizedParameterFamily p).mdifferentiableAt (by simp)
  rw [mfderiv, ite_eq_left hmd]
  have hf : Function.Injective (fderivWithin ℝ
      (writtenInExtChartAt 𝓘(ℝ, NativeGraphParameters)
        𝓘(ℝ, Fin 9 → Fin 3 → Fin 27 → ℝ) p nativeNormalizedParameterFamily)
      (Set.range 𝓘(ℝ, NativeGraphParameters))
      (extChartAt 𝓘(ℝ, NativeGraphParameters) p p)) := by
    simpa only [writtenInExtChartAt, mfld_simps, normalizedParameter_chartAt_self,
      chartAt_self_eq, Function.comp_def, OpenPartialHomeomorph.refl_apply, fderivWithin_univ] using
      nativeNormalizedParameterFamily_chart_fderiv_injective p
  exact (tangentSpaceCastModel 𝓘(ℝ, Fin 9 → Fin 3 → Fin 27 → ℝ)
    (nativeNormalizedParameterFamily p)).symm.injective.comp
      (hf.comp (tangentSpaceCastModel 𝓘(ℝ, NativeGraphParameters) p).injective)

end CompactAlbert

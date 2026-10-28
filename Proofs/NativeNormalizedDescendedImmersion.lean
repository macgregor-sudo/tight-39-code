module

public import NormalizedParameterAnalyticManifold
public import SpecialUnitaryCentralAnalyticQuotient
public import NativeNormalizedProjectiveFamily

@[expose] public section

/-!
# Analytic differential immersion of the actual descended normalized native family

The domain is the literal standard SU3 center quotient
times the unchanged PhaseTriple. The map is the frozen projective native family
through its exact phase homeomorphism. Its chart expression equals the already
proved representative chart expression; no analytic lift, differential
equivalence or immersion assumption is introduced. All Fin9/Fin3/Fin27 labels
and the fixed forward native orientation are unchanged. This proves the
differential-immersion predicate, not the stronger local-normal-form predicate.
First-party composition of frozen owners and pinned APIs, no upstream proof
body copied. Thanks to the contributors. “If I have seen further it is by
standing on the sholders of Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise Topology
open UnitaryErrorBases UnitaryErrorBases.ThreeCycleNormalized
open UnitaryErrorBases.SpecialUnitaryConstraints

namespace CompactAlbert

abbrev DescendedNormalizedParameter := SpecialUnitaryCenterQuotient × PhaseTriple

attribute [local instance] standardCenterQuotientChartedSpace phaseExponentialChartedSpace

/-- Named product of the proved quotient and phase atlases on the existing product topology. -/
@[instance_reducible]
def descendedNormalizedParameterChartedSpace :
    @ChartedSpace NativeGraphParameters
      (inferInstance : NormedAddCommGroup NativeGraphParameters).toUniformSpace.toTopologicalSpace
      DescendedNormalizedParameter inferInstance := by
  exact @prodChartedSpace ConstraintTangent _ SpecialUnitaryCenterQuotient _
    standardCenterQuotientChartedSpace (ℝ × ℝ) _ PhaseTriple _ phaseExponentialChartedSpace

attribute [local instance] descendedNormalizedParameterChartedSpace

theorem descendedNormalizedParameter_isManifold :
    IsManifold 𝓘(ℝ, NativeGraphParameters) ω DescendedNormalizedParameter := by
  have := standardCenterQuotient_isManifold
  have := phaseExponential_isManifold
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod SpecialUnitaryCenterQuotient PhaseTriple

theorem descendedNormalizedParameter_model_finrank :
    IsManifold 𝓘(ℝ, NativeGraphParameters) ω DescendedNormalizedParameter ∧
      Module.finrank ℝ NativeGraphParameters = 10 :=
  ⟨descendedNormalizedParameter_isManifold, finrank_nativeGraphParameters⟩

theorem descendedNormalizedParameterChartedSpace_chartAt (p : DescendedNormalizedParameter) :
    @chartAt NativeGraphParameters _ DescendedNormalizedParameter _
      descendedNormalizedParameterChartedSpace p =
      (standardCenterRepresentativeChart (standardCenterRepresentative p.1)).prod
        (phaseExponentialLocalParam p.2).symm := rfl

theorem zero_mem_descendedNormalizedParameter_chartTarget (p : DescendedNormalizedParameter) :
    (0 : NativeGraphParameters) ∈ (@chartAt NativeGraphParameters _ DescendedNormalizedParameter _
      descendedNormalizedParameterChartedSpace p).target :=
  ⟨zero_mem_standardCenterRepresentativeChart_target (standardCenterRepresentative p.1),
    zero_mem_phaseExponentialLocalParam_source p.2⟩

theorem descendedNormalizedParameter_chartAt_self (p : DescendedNormalizedParameter) :
    @chartAt NativeGraphParameters _ DescendedNormalizedParameter _
      descendedNormalizedParameterChartedSpace p p = 0 := by
  change (standardCenterRepresentativeChart (standardCenterRepresentative p.1) p.1,
    (phaseExponentialLocalParam p.2).symm p.2) = 0
  apply Prod.ext
  · calc
      standardCenterRepresentativeChart (standardCenterRepresentative p.1) p.1 =
          standardCenterRepresentativeChart (standardCenterRepresentative p.1)
            (QuotientGroup.mk (standardCenterRepresentative p.1)) :=
        congrArg _ (standardCenterRepresentative_mk p.1).symm
      _ = 0 := by
        rw [standardCenterRepresentativeChart_mk _ _
          (standardCenterLocalLift_mem_target (standardCenterRepresentative p.1)),
          specialUnitaryLocalChart_apply_self]
  · change (phaseExponentialLocalParam p.2).symm p.2 = (0 : ℝ × ℝ)
    have h := (phaseExponentialLocalParam p.2).left_inv
      (zero_mem_phaseExponentialLocalParam_source p.2)
    simpa only [phaseExponentialLocalParam_apply, phaseExpParam_zero] using h

/-- The exact old projective parameters, with only the proved phase homeomorphism applied. -/
def descendedNormalizedParameterProjectiveHomeomorph :
    DescendedNormalizedParameter ≃ₜ (SpecialUnitaryCenterQuotient × (Circle × Circle)) :=
  (Homeomorph.refl SpecialUnitaryCenterQuotient).prodCongr phaseTripleHomeomorph

/-- The actual frozen all-forward native family on the actual quotient and phase carrier. -/
def nativeNormalizedDescendedFamily (p : DescendedNormalizedParameter) :
    Fin 9 → Fin 3 → Fin 27 → ℝ :=
  nativeNormalizedProjectiveFamily (p.1, phaseTripleHomeomorph p.2)

/-- Exact descent/factorization, for every actual representative and phase. -/
theorem nativeNormalizedDescendedFamily_mk (Q : StandardSpecialUnitary) (d : PhaseTriple) :
    nativeNormalizedDescendedFamily (QuotientGroup.mk Q, d) =
      nativeNormalizedParameterFamily (Q, d) := by
  have hd : phaseOfCircles (phaseTripleHomeomorph d) = d :=
    phaseTripleHomeomorph.symm_apply_apply d
  simpa only [hd, nativeNormalizedDescendedFamily] using
    (nativeNormalizedParameterFamily_mk Q (phaseTripleHomeomorph d)).symm

/-- The inherited closed embedding is transported only through the actual phase homeomorphism. -/
theorem isClosedEmbedding_nativeNormalizedDescendedFamily :
    Topology.IsClosedEmbedding nativeNormalizedDescendedFamily :=
  isClosedEmbedding_nativeNormalizedProjectiveFamily.comp
    descendedNormalizedParameterProjectiveHomeomorph.isClosedEmbedding

theorem continuous_nativeNormalizedDescendedFamily : Continuous nativeNormalizedDescendedFamily :=
  isClosedEmbedding_nativeNormalizedDescendedFamily.continuous

/-- The quotient-chart native expression is literally the proved representative-chart expression.
This equality holds for the extended functions, hence also near the chart origin. -/
theorem nativeNormalizedDescendedFamily_chart_eq (p : DescendedNormalizedParameter) :
    (fun x => nativeNormalizedDescendedFamily
      ((@chartAt NativeGraphParameters _ DescendedNormalizedParameter _
        descendedNormalizedParameterChartedSpace p).symm x)) =
    (fun x => nativeNormalizedParameterFamily
      ((@chartAt NativeGraphParameters _ NormalizedParameter _ normalizedParameterChartedSpace
        (standardCenterRepresentative p.1, p.2)).symm x)) := by
  funext x
  change nativeNormalizedDescendedFamily
    ((standardCenterRepresentativeChart (standardCenterRepresentative p.1)).symm x.1,
      phaseExponentialLocalParam p.2 x.2) =
    nativeNormalizedParameterFamily
      ((specialUnitaryLocalChart (standardCenterRepresentative p.1)).symm x.1,
        phaseExponentialLocalParam p.2 x.2)
  rw [standardCenterRepresentativeChart_symm_apply, nativeNormalizedDescendedFamily_mk]

theorem analyticAt_nativeNormalizedDescendedFamily_chart (p : DescendedNormalizedParameter) :
    AnalyticAt ℝ (fun x => nativeNormalizedDescendedFamily
      ((@chartAt NativeGraphParameters _ DescendedNormalizedParameter _
        descendedNormalizedParameterChartedSpace p).symm x)) 0 := by
  rw [nativeNormalizedDescendedFamily_chart_eq]
  exact analyticAt_nativeNormalizedParameterFamily_chart (standardCenterRepresentative p.1, p.2)

theorem nativeNormalizedDescendedFamily_chart_fderiv_injective (p : DescendedNormalizedParameter) :
    Function.Injective (fderiv ℝ (fun x => nativeNormalizedDescendedFamily
      ((@chartAt NativeGraphParameters _ DescendedNormalizedParameter _
        descendedNormalizedParameterChartedSpace p).symm x)) 0) := by
  rw [nativeNormalizedDescendedFamily_chart_eq]
  exact nativeNormalizedParameterFamily_chart_fderiv_injective (standardCenterRepresentative p.1, p.2)

theorem contMDiff_nativeNormalizedDescendedFamily :
    ContMDiff 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Fin 9 → Fin 3 → Fin 27 → ℝ) ω
      nativeNormalizedDescendedFamily := by
  intro p
  apply contMDiffAt_iff.mpr
  refine ⟨continuous_nativeNormalizedDescendedFamily.continuousAt, ?_⟩
  simpa only [mfld_simps, descendedNormalizedParameter_chartAt_self, chartAt_self_eq,
    Function.id_comp, Function.comp_def, OpenPartialHomeomorph.refl_apply] using
    (analyticAt_nativeNormalizedDescendedFamily_chart p).contDiffAt.contDiffWithinAt

/-- Differential immersion at every actual quotient/phase parameter, with no extra premise. -/
theorem isDiffImmersionAt_nativeNormalizedDescendedFamily (p : DescendedNormalizedParameter) :
    IsDiffImmersionAt 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Fin 9 → Fin 3 → Fin 27 → ℝ)
      nativeNormalizedDescendedFamily p := by
  apply IsDiffImmersionAt.of_injective_of_finiteDimensional
  have hmd := (contMDiff_nativeNormalizedDescendedFamily p).mdifferentiableAt (by simp)
  rw [mfderiv, ite_eq_left hmd]
  have hf : Function.Injective (fderivWithin ℝ
      (writtenInExtChartAt 𝓘(ℝ, NativeGraphParameters)
        𝓘(ℝ, Fin 9 → Fin 3 → Fin 27 → ℝ) p nativeNormalizedDescendedFamily)
      (Set.range 𝓘(ℝ, NativeGraphParameters))
      (extChartAt 𝓘(ℝ, NativeGraphParameters) p p)) := by
    simpa only [writtenInExtChartAt, mfld_simps, descendedNormalizedParameter_chartAt_self,
      chartAt_self_eq, Function.comp_def, OpenPartialHomeomorph.refl_apply, fderivWithin_univ] using
      nativeNormalizedDescendedFamily_chart_fderiv_injective p
  exact (tangentSpaceCastModel 𝓘(ℝ, Fin 9 → Fin 3 → Fin 27 → ℝ)
    (nativeNormalizedDescendedFamily p)).symm.injective.comp
      (hf.comp (tangentSpaceCastModel 𝓘(ℝ, NativeGraphParameters) p).injective)

end CompactAlbert

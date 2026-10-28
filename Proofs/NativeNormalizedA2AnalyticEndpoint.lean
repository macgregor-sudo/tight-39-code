module
public import NativeNormalizedDescendedImmersion
public import NativeNormalizedConfigurationEmbedding
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

@[expose] public section
noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise Topology
open UnitaryErrorBases UnitaryErrorBases.ThreeCycleNormalized
open UnitaryErrorBases.SpecialUnitaryConstraints
open NativePolynomial NativePolynomial.PartialAction NativePolynomial.ConfigurationResiduals
open QuadraticCertificate.ExactCKMConfiguration

namespace CompactAlbert

attribute [local instance] descendedNormalizedParameterChartedSpace

/-- The existing full native configuration, through the exact phase homeomorphism. -/
def nativeNormalizedDescendedConfiguration (p : DescendedNormalizedParameter) : Configuration ℝ :=
  nativeNormalizedProjectiveConfiguration (descendedNormalizedParameterProjectiveHomeomorph p)

/-- The original point-first 1053 variables for that same full configuration. -/
def nativeNormalizedDescendedPackedConfiguration (p : DescendedNormalizedParameter) : Fin 1053 → ℝ :=
  pack (nativeNormalizedDescendedConfiguration p)

/-- Exact insertion binding; neither the native family nor the original points are redefined. -/
theorem nativeNormalizedDescendedConfiguration_eq_insert (p : DescendedNormalizedParameter) :
    nativeNormalizedDescendedConfiguration p =
      insertNativeAnchorCoordinates (nativeNormalizedDescendedFamily p) :=
  (insertNativeAnchorCoordinates_nativeNormalizedProjectiveFamily
    (descendedNormalizedParameterProjectiveHomeomorph p)).symm

private theorem configuration_contMDiff :
    ContMDiff 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Configuration ℝ) ω
      nativeNormalizedDescendedConfiguration := by
  have hi : ContDiff ℝ ω insertNativeAnchorCoordinates :=
    contDiff_iff_contDiffAt.mpr fun U => (analyticAt_insertNativeAnchorCoordinates U).contDiffAt
  simpa only [Function.comp_def, ← nativeNormalizedDescendedConfiguration_eq_insert] using!
    hi.contMDiff.comp contMDiff_nativeNormalizedDescendedFamily

private theorem insertion_diffImmersion (U : Fin 9 → Fin 3 → Fin 27 → ℝ) :
    IsDiffImmersionAt 𝓘(ℝ, Fin 9 → Fin 3 → Fin 27 → ℝ) 𝓘(ℝ, Configuration ℝ)
      insertNativeAnchorCoordinates U := by
  apply IsDiffImmersionAt.of_injective_of_finiteDimensional
  rw [mfderiv_eq_fderiv]
  exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (insertNativeAnchorCoordinates U)).symm.injective.comp
    ((insertNativeAnchorCoordinates_fderiv_injective U).comp
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) U).injective)

private theorem configuration_diffImmersion (p : DescendedNormalizedParameter) :
    IsDiffImmersionAt 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Configuration ℝ)
      nativeNormalizedDescendedConfiguration p := by
  simpa only [Function.comp_def, ← nativeNormalizedDescendedConfiguration_eq_insert] using!
    (insertion_diffImmersion (nativeNormalizedDescendedFamily p)).comp
      (isDiffImmersionAt_nativeNormalizedDescendedFamily p)

private theorem packed_contMDiff :
    ContMDiff 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Fin 1053 → ℝ) ω
      nativeNormalizedDescendedPackedConfiguration := by
  have hi : ContDiff ℝ ω (fun U => pack (insertNativeAnchorCoordinates U)) :=
    contDiff_iff_contDiffAt.mpr fun U => (analyticAt_pack_insertNativeAnchorCoordinates U).contDiffAt
  simpa only [Function.comp_def, ← nativeNormalizedDescendedConfiguration_eq_insert,
    nativeNormalizedDescendedPackedConfiguration] using!
      hi.contMDiff.comp contMDiff_nativeNormalizedDescendedFamily

private theorem packed_insertion_diffImmersion (U : Fin 9 → Fin 3 → Fin 27 → ℝ) :
    IsDiffImmersionAt 𝓘(ℝ, Fin 9 → Fin 3 → Fin 27 → ℝ) 𝓘(ℝ, Fin 1053 → ℝ)
      (fun V => pack (insertNativeAnchorCoordinates V)) U := by
  apply IsDiffImmersionAt.of_injective_of_finiteDimensional
  rw [mfderiv_eq_fderiv, (pack_insertNativeAnchorCoordinates_hasFDerivAt U).fderiv]
  exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) (pack (insertNativeAnchorCoordinates U))).symm.injective.comp
    (packedNativeCompletionInsertionLinear_injective.comp
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) U).injective)

private theorem packed_diffImmersion (p : DescendedNormalizedParameter) :
    IsDiffImmersionAt 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Fin 1053 → ℝ)
      nativeNormalizedDescendedPackedConfiguration p := by
  simpa only [Function.comp_def, ← nativeNormalizedDescendedConfiguration_eq_insert,
    nativeNormalizedDescendedPackedConfiguration] using!
      (packed_insertion_diffImmersion (nativeNormalizedDescendedFamily p)).comp
        (isDiffImmersionAt_nativeNormalizedDescendedFamily p)

/-- Complete actual-configuration endpoint: named analytic ten-dimensional parameter manifold,
closed embeddings, analytic differential immersions, literal native labels and every original F row.
The differential-immersion predicate is explicit; no stronger local-normal-form claim is made. -/
theorem nativeNormalizedDescendedConfiguration_analytic_endpoint :
    IsManifold 𝓘(ℝ, NativeGraphParameters) ω DescendedNormalizedParameter ∧
    Module.finrank ℝ NativeGraphParameters = 10 ∧
    (Topology.IsClosedEmbedding nativeNormalizedDescendedConfiguration ∧
      ContMDiff 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Configuration ℝ) ω
        nativeNormalizedDescendedConfiguration ∧
      ∀ p, IsDiffImmersionAt 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Configuration ℝ)
        nativeNormalizedDescendedConfiguration p) ∧
    (Topology.IsClosedEmbedding nativeNormalizedDescendedPackedConfiguration ∧
      ContMDiff 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Fin 1053 → ℝ) ω
        nativeNormalizedDescendedPackedConfiguration ∧
      ∀ p, IsDiffImmersionAt 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Fin 1053 → ℝ)
        nativeNormalizedDescendedPackedConfiguration p) ∧
    (∀ p : DescendedNormalizedParameter,
      (∀ i : Fin 39, i.val < 12 → nativeNormalizedDescendedConfiguration p i =
        upperCoordinates (nativePoint i)) ∧
      (∀ r : Fin 9, ∀ k : Fin 3,
        nativeNormalizedDescendedConfiguration p ⟨12 + 3 * r.val + k.val, by omega⟩ =
          nativeNormalizedDescendedFamily p r k) ∧
      (∀ r : Fin 2184,
        MvPolynomial.eval (nativeNormalizedDescendedPackedConfiguration p)
          (fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r) = 0)) := by
  refine ⟨descendedNormalizedParameter_isManifold, finrank_nativeGraphParameters,
    ⟨?_, configuration_contMDiff, configuration_diffImmersion⟩,
    ⟨?_, packed_contMDiff, packed_diffImmersion⟩, ?_⟩
  · exact isClosedEmbedding_nativeNormalizedProjectiveConfiguration.comp
      descendedNormalizedParameterProjectiveHomeomorph.isClosedEmbedding
  · exact isClosedEmbedding_pack_nativeNormalizedProjectiveConfiguration.comp
      descendedNormalizedParameterProjectiveHomeomorph.isClosedEmbedding
  · intro p
    exact ⟨nativeNormalizedProjectiveConfiguration_anchor
        (descendedNormalizedParameterProjectiveHomeomorph p),
      nativeNormalizedProjectiveConfiguration_completion
        (descendedNormalizedParameterProjectiveHomeomorph p),
      nativeNormalizedProjectiveConfiguration_all_original_F
        (descendedNormalizedParameterProjectiveHomeomorph p)⟩

end CompactAlbert

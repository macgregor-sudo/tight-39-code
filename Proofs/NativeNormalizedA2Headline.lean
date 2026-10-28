module
public import NativeNormalizedStrongImmersion
public import NativeCompletionRightNormalization

@[expose] public section
noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise Topology
open Manifold UnitaryErrorBases UnitaryErrorBases.ThreeCycleNormalized
open UnitaryErrorBases.SpecialUnitaryConstraints
open NativePolynomial NativePolynomial.PartialAction NativePolynomial.ConfigurationResiduals
open QuadraticCertificate.ExactCKMConfiguration

namespace CompactAlbert
attribute [local instance] descendedNormalizedParameterChartedSpace

/-- Exact MASTER A2 assembly for the labelled right-normalized constructed family.
PSU3 is the literal standard SU3/full-center quotient; the two-torus identification
is the existing explicit phase homeomorphism, not an arbitrary parameter space.
Both native ambient maps are strong analytic immersions and closed embeddings.
No claim of global exhaustion is part of this theorem. -/
theorem native_normalized_A2 :
    IsManifold 𝓘(ℝ, NativeGraphParameters) ω DescendedNormalizedParameter ∧
    Module.finrank ℝ NativeGraphParameters = 10 ∧
    (∀ p : DescendedNormalizedParameter,
      descendedNormalizedParameterProjectiveHomeomorph p =
        (p.1, (phaseCircle p.2 0, phaseCircle p.2 1))) ∧
    (∀ q : (Matrix.specialUnitaryGroup Index ℂ) ⧸
        Subgroup.center (Matrix.specialUnitaryGroup Index ℂ), ∀ z : Circle × Circle,
      descendedNormalizedParameterProjectiveHomeomorph.symm (q, z) = (q, phaseOfCircles z)) ∧
    (∀ x : SpecialUnitaryCenterQuotient × (Circle × Circle),
      nativeNormalizedDescendedConfiguration
          (descendedNormalizedParameterProjectiveHomeomorph.symm x) =
        nativeNormalizedProjectiveConfiguration x) ∧
    (Topology.IsClosedEmbedding nativeNormalizedDescendedConfiguration ∧
      ContMDiff 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Configuration ℝ) ω
        nativeNormalizedDescendedConfiguration ∧
      IsImmersion 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Configuration ℝ) ω
        nativeNormalizedDescendedConfiguration) ∧
    (Topology.IsClosedEmbedding nativeNormalizedDescendedPackedConfiguration ∧
      ContMDiff 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Fin 1053 → ℝ) ω
        nativeNormalizedDescendedPackedConfiguration ∧
      IsImmersion 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Fin 1053 → ℝ) ω
        nativeNormalizedDescendedPackedConfiguration) ∧
    (∀ x : SpecialUnitaryCenterQuotient × (Circle × Circle),
      nativeNormalizedProjectiveArray x 0 = (1 : TitsComplexMatrix) ∧
      completionRightNormalization (nativeNormalizedProjectiveArray x) = nativeNormalizedProjectiveArray x ∧
      ∀ R : TitsComplexMatrix, (R * R.conjTranspose = 1 ∧ R.det = 1) →
        completionRightNormalization (fun r => nativeNormalizedProjectiveArray x r * R) =
          nativeNormalizedProjectiveArray x) ∧
    (∀ Q : StandardSpecialUnitary, ∀ d : PhaseTriple,
      nativeNormalizedProjectiveArray (QuotientGroup.mk Q, phaseTripleHomeomorph d) =
        nativeThreeCycleArray Q.val d) ∧
    (∀ p : DescendedNormalizedParameter,
      nativeNormalizedDescendedPackedConfiguration p = pack (nativeNormalizedDescendedConfiguration p) ∧
      (∀ i : Fin 39, i.val < 12 → nativeNormalizedDescendedConfiguration p i =
        upperCoordinates (nativePoint i)) ∧
      (∀ r : Fin 9, ∀ k : Fin 3,
        nativeNormalizedDescendedConfiguration p ⟨12 + 3 * r.val + k.val, by omega⟩ =
          nativeNormalizedDescendedFamily p r k) ∧
      (∀ r : Fin 2184,
        MvPolynomial.eval (nativeNormalizedDescendedPackedConfiguration p)
          (fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r) = 0)) := by
  obtain ⟨hM, hdim, hfull, hpacked, hnative⟩ :=
    nativeNormalizedDescendedConfiguration_analytic_endpoint
  refine ⟨hM, hdim, ?_, ?_, ?_,
    ⟨hfull.1, hfull.2.1, isImmersion_nativeNormalizedDescendedConfiguration⟩,
    ⟨hpacked.1, hpacked.2.1, isImmersion_nativeNormalizedDescendedPackedConfiguration⟩,
    ?_, ?_, ?_⟩
  · intro p
    rfl
  · intro q z
    rfl
  · intro x
    unfold nativeNormalizedDescendedConfiguration
    rw [Homeomorph.apply_symm_apply]
  · intro x
    have hz := nativeNormalizedProjectiveArray_zero x
    have hn : completionRightNormalization (nativeNormalizedProjectiveArray x) =
        nativeNormalizedProjectiveArray x := by
      funext r
      simp only [completionRightNormalization, hz, Matrix.conjTranspose_one, Matrix.mul_one]
    exact ⟨hz, hn, fun R hR => (completionRightNormalization_common_right _ R hR.1).trans hn⟩
  · intro Q d
    rw [nativeNormalizedProjectiveArray_mk]
    have hd : phaseOfCircles (phaseTripleHomeomorph d) = d :=
      phaseTripleHomeomorph.symm_apply_apply d
    rw [hd]
  · intro p
    exact ⟨rfl, hnative p⟩

end CompactAlbert

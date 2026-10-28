module

public import NativeTraceMetricBinding
public import ULQuot
public import Mathlib.Topology.Homeomorph.Quotient

@[expose] public section

/-! Actual compensated finite action on the existing slice-zero germ, equipped
with an explicit trace metric of the same topology. All structures are explicit
values, not global replacements of the native coordinate metric or action. -/
noncomputable section
namespace CKM.NativeTraceMetricBinding
open NativeGroupSlice NativeUnlabelledSlice

variable (ξ : Fin 4 → ℂ) (W : Set Cfg)
variable (hW : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W)

abbrev sliceTraceMetric : MetricSpace (sliceGerm ξ W) :=
  MetricSpace.induced Subtype.val Subtype.val_injective
    (MetricSpace.induced Subtype.val Subtype.val_injective traceMetricSpace)

theorem sliceTraceMetric_topology :
    (sliceTraceMetric ξ W).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (sliceGerm ξ W)) := rfl

abbrev sliceAction : MulAction (stab ξ) (sliceGerm ξ W) where
  smul γ x := ⟨⟨(γ : Big) • (x.1 : Cfg),
      (stab_smul_mem_zeroSet_iff γ.2 _).mpr x.1.2⟩,
    (hW γ γ.2 _).mpr x.2.1, (smul_mem_sliceSet_iff γ.2 _).mpr x.2.2⟩
  one_smul x := Subtype.ext (Subtype.ext (one_smul Big (x.1 : Cfg)))
  mul_smul γ δ x := Subtype.ext (Subtype.ext (mul_smul (γ : Big) (δ : Big) (x.1 : Cfg)))

theorem sliceAction_isometry (γ : stab ξ) :
    @Isometry (sliceGerm ξ W) (sliceGerm ξ W)
      (sliceTraceMetric ξ W).toPseudoEMetricSpace (sliceTraceMetric ξ W).toPseudoEMetricSpace
      (fun x => (sliceAction ξ W hW).smul γ x) := by
  apply @Isometry.of_dist_eq _ _ (sliceTraceMetric ξ W).toPseudoMetricSpace
    (sliceTraceMetric ξ W).toPseudoMetricSpace
  intro x y
  exact traceDistance_big_action γ (x.1 : Cfg) (y.1 : Cfg)

theorem sliceAction_isIsometricSMul :
    @IsIsometricSMul (stab ξ) (sliceGerm ξ W)
      (sliceTraceMetric ξ W).toPseudoEMetricSpace (sliceAction ξ W hW).toSMul :=
  @IsIsometricSMul.mk _ _ (sliceTraceMetric ξ W).toPseudoEMetricSpace
    (sliceAction ξ W hW).toSMul (sliceAction_isometry ξ W hW)

/-- The constructed action uses exactly the existing native compensated orbit
relation; only the conventional orientation of orbit membership is reversed. -/
theorem sliceAction_orbitRel (s t : sliceGerm ξ W) :
    @MulAction.orbitRel (stab ξ) (sliceGerm ξ W) _ (sliceAction ξ W hW) s t ↔
      (stabSetoid ξ W).r s t := by
  letI := sliceAction ξ W hW
  have hreverse : MulAction.orbitRel (stab ξ) (sliceGerm ξ W) s t ↔
      (stabSetoid ξ W).r t s := by
    constructor
    · rintro ⟨γ, hγ⟩
      exact ⟨γ, γ.2, congrArg (fun z : sliceGerm ξ W => (z.1 : Cfg)) hγ⟩
    · rintro ⟨γ, hγ, heq⟩
      exact ⟨⟨γ, hγ⟩, Subtype.ext (Subtype.ext heq)⟩
  exact hreverse.trans ⟨(stabSetoid ξ W).symm, (stabSetoid ξ W).symm⟩

/-- Identity-on-representatives homeomorphism onto the frozen native slice quotient. -/
def sliceOrbitHomeomorph :
    Quotient (@MulAction.orbitRel (stab ξ) (sliceGerm ξ W) _ (sliceAction ξ W hW)) ≃ₜ SliceQuot ξ W :=
  Homeomorph.Quotient.congrRight (sliceAction_orbitRel ξ W hW)

#print axioms sliceAction_isIsometricSMul
#print axioms sliceAction_orbitRel
#print axioms sliceOrbitHomeomorph
end CKM.NativeTraceMetricBinding

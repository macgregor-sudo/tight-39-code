module

public import NativeSliceTraceAction
public import FiniteOrbitDimensionUpper

@[expose] public section

/-! Native finite-quotient upper-bound contract. The antecedent is the actual
slice-zero small-inductive dimension bound; no bound on that slice is assumed
proved by this module. The action, finite stabilizer, metric topology and frozen
native quotient correspondence are discharged by existing explicit declarations. -/
noncomputable section
namespace CKM.NativeTraceMetricBinding
open NativeGroupSlice NativeUnlabelledSlice NativeFirstOrder TopologicalSpace

theorem native_slice_quotient_dimension_le
    (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (W : Set Cfg)
    (hW : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W)
    (n : ℕ) (hdim : HasSmallInductiveDimensionLE (sliceGerm ξ W) n) :
    HasSmallInductiveDimensionLE (SliceQuot ξ W) n := by
  have hq := @FiniteIsometricStrata.finite_isometric_quotient_dimension_le
    (stab ξ) (sliceGerm ξ W) inferInstance (finite_stab ξ hξ)
    (sliceTraceMetric ξ W) (sliceAction ξ W hW)
    (sliceAction_isIsometricSMul ξ W hW) inferInstance n hdim
  exact ((sliceOrbitHomeomorph ξ W hW).hasSmallInductiveDimensionLE n).mp hq

/-- The exact dimension-ten upper-bound implication needed by retained A7. -/
theorem native_slice_quotient_dimension_le_ten
    (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (W : Set Cfg)
    (hW : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W)
    (hdim : HasSmallInductiveDimensionLE (sliceGerm ξ W) 10) :
    HasSmallInductiveDimensionLE (SliceQuot ξ W) 10 :=
  native_slice_quotient_dimension_le ξ hξ W hW 10 hdim

#print axioms native_slice_quotient_dimension_le
#print axioms native_slice_quotient_dimension_le_ten
end CKM.NativeTraceMetricBinding

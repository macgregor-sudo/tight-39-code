module

public import NativeOriginalCodeAccumulation
public import TopologyPreflight.ChartObstruction

@[expose] public section

/-!
Final obstruction consumer, conditional only on the explicitly stated native
ten-dimensional patch hypothesis.
The native good/pivot accumulation input is proved, not hypothesized here.
`TopologyPreflight.ChartObstruction` comes from the topology package; its source/provenance notices remain at their origin.
This does not assert local dimension ten at every good-phase quotient point.
-/
noncomputable section
open Filter Topology
open CKM.NativeFirstOrder CKM.NativeFourFamily CKM.NativeGoodPhase
open CKM.NativeUnlabelledSlice
open Option2.NativeStress.PhasePivotLocusA6

namespace Option2.NativeStress.NativeOriginalCodeA7

/-- Explicit geometric hypothesis. `U` is a genuine Euclidean open set;
`V` is open in the actual unlabelled tight-code quotient, not just a sheet. -/
def NativeGoodPivotTenPatches : Prop :=
  ∀ u : PhaseTorus, IsGoodPhase u.1 → u ∈ nativePivotLocus →
    ∀ N : Set CodeModuli, IsOpen N → codeClass u ∈ N →
      ∃ (U : Set (EuclideanSpace ℝ (Fin 10))) (V : Set CodeModuli),
        IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V ⊆ N ∧ Nonempty (U ≃ₜ V)

theorem originalCode_has_ten_patches_of_native_patches
    (hpatch : NativeGoodPivotTenPatches)
    (N : Set CodeModuli) (hN : IsOpen N) (hseed : originalCode ∈ N) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin 10))) (V : Set CodeModuli),
      IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V ⊆ N ∧ Nonempty (U ≃ₜ V) := by
  obtain ⟨u, _, hgood, hpivot, huN⟩ :=
    exists_good_pivot_code_mem_nhds (hN.mem_nhds hseed)
  exact hpatch u hgood hpivot N hN huN

/-- No Euclidean 24-chart at the original code, conditional on the separate
native ten-patch construction. This is the exact neighborhood obstruction;
there is no assertion about the original resonant germ's dimension or branches. -/
theorem originalCode_no_open24_chart_of_native_patches
    (hpatch : NativeGoodPivotTenPatches)
    {N : Set CodeModuli} {O : Set (EuclideanSpace ℝ (Fin 24))}
    (hN : IsOpen N) (hseed : originalCode ∈ N) (hO : IsOpen O) :
    IsEmpty (N ≃ₜ O) := by
  apply TopologyReuse.not_nhd_homeomorph_of_finrank_ne
    (originalCode_has_ten_patches_of_native_patches hpatch) _ hN hseed hO
  simp

end Option2.NativeStress.NativeOriginalCodeA7

#print axioms Option2.NativeStress.NativeOriginalCodeA7.originalCode_no_open24_chart_of_native_patches

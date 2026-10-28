module

public import NativeOriginalCodeObstruction
public import Mathlib.Geometry.Manifold.ChartedSpace

@[expose] public section

/-! A charted open neighborhood supplies an actual ambient open Euclidean chart.
This spells out the manifold-neighborhood consequence of the conditional native
patch consumer; the patch hypothesis remains explicit. All library use is by import. -/
noncomputable section
open CKM.NativeUnlabelledSlice

namespace Option2.NativeStress.NativeOriginalCodeA7

/-- An open neighborhood of the original code cannot carry a 24-dimensional
Euclidean atlas once the native ten-patch construction is supplied. -/
theorem originalCode_no_charted24_neighborhood_of_native_patches
    (hpatch : NativeGoodPivotTenPatches)
    (N : Set CodeModuli) (hN : IsOpen N) (hseed : originalCode ∈ N)
    [ChartedSpace (EuclideanSpace ℝ (Fin 24)) N] : False := by
  let n : N := ⟨originalCode, hseed⟩
  let inc := (⟨N, hN⟩ : TopologicalSpace.Opens CodeModuli).openPartialHomeomorphSubtypeCoe ⟨n⟩
  let chart := chartAt (EuclideanSpace ℝ (Fin 24)) n
  let ambient := inc.symm.trans chart
  have hinc : originalCode ∈ inc.target := by
    simpa [inc] using hseed
  have hinv : inc.symm originalCode = n := by
    have hn : n ∈ inc.source := by simp [inc]
    simpa [inc, n] using inc.left_inv hn
  have hsource : originalCode ∈ ambient.source := by
    change originalCode ∈ inc.symm.source ∩ inc.symm ⁻¹' chart.source
    exact ⟨hinc, by rw [Set.mem_preimage, hinv]; exact mem_chart_source _ n⟩
  exact (originalCode_no_open24_chart_of_native_patches hpatch
    ambient.open_source hsource ambient.open_target).false ambient.toHomeomorphSourceTarget

end Option2.NativeStress.NativeOriginalCodeA7

#print axioms Option2.NativeStress.NativeOriginalCodeA7.originalCode_no_charted24_neighborhood_of_native_patches

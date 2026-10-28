module

public import NativeOriginalCodeManifold
public import NativeCodeTenPatches

@[expose] public section

/-!
Unconditional native original-code obstruction. The actual native ten-patch
theorem discharges the explicit geometry premise of the earlier consumer.
The original point is literally `codeClass onePhase`, with the quotient topology
on tight codes. No chart or dimension conclusion is assumed.
The separate retained A7 local-dimension-ten assertion at every good phase is
not a conclusion of this module.
-/
noncomputable section
open CKM.NativeUnlabelledSlice
open CKM.NativeGoodPhase

namespace Option2.NativeStress.NativeOriginalCodeA7

theorem nativeGoodPivotTenPatches : NativeGoodPivotTenPatches := by
  intro u hgood hpivot N hN hseed
  obtain ⟨P, hP, hPn, Q, hQ, hQN, e⟩ :=
    NativeCodeTenPatchesA7.native_code_ten_patches u hgood hpivot hN hseed
  exact ⟨P, Q, hP, hQ, hPn, hQN, e⟩

/-- Every open neighborhood of the actual original unlabelled code contains
a nonempty open patch homeomorphic to an open subset of Euclidean ten-space. -/
theorem originalCode_has_ten_patches
    (N : Set CodeModuli) (hN : IsOpen N) (hseed : codeClass onePhase ∈ N) :
    ∃ (U : Set (EuclideanSpace ℝ (Fin 10))) (V : Set CodeModuli),
      IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V ⊆ N ∧ Nonempty (U ≃ₜ V) :=
  originalCode_has_ten_patches_of_native_patches nativeGoodPivotTenPatches N hN hseed

/-- The actual original code has no open Euclidean 24-chart. -/
theorem originalCode_no_open24_chart
    {N : Set CodeModuli} {O : Set (EuclideanSpace ℝ (Fin 24))}
    (hN : IsOpen N) (hseed : codeClass onePhase ∈ N) (hO : IsOpen O) :
    IsEmpty (N ≃ₜ O) :=
  originalCode_no_open24_chart_of_native_patches nativeGoodPivotTenPatches hN hseed hO

/-- No open neighborhood of the literal all-one code class carries a
24-dimensional Euclidean atlas. -/
theorem originalCode_no_charted24_neighborhood
    (N : Set CodeModuli) (hN : IsOpen N) (hseed : codeClass onePhase ∈ N)
    [ChartedSpace (EuclideanSpace ℝ (Fin 24)) N] : False :=
  originalCode_no_charted24_neighborhood_of_native_patches nativeGoodPivotTenPatches N hN hseed

end Option2.NativeStress.NativeOriginalCodeA7

#print axioms Option2.NativeStress.NativeOriginalCodeA7.originalCode_has_ten_patches
#print axioms Option2.NativeStress.NativeOriginalCodeA7.originalCode_no_open24_chart
#print axioms Option2.NativeStress.NativeOriginalCodeA7.originalCode_no_charted24_neighborhood

module

public import NativeCodeTenPatches
public import EuclideanNormalization

@[expose] public section

/-! The retained A7 lower-neighborhood inequality for the actual CodeModuli
quotient and Mathlib smallInductiveDimension. The locus is exactly the already
proved native good-phase plus explicit pivot predicate. No equality with any
other presentation of MASTER's discriminant locus is asserted here.
Numerical local dimension is not concluded here.
-/
noncomputable section
namespace Option2.NativeStress.NativeLocalDimensionA7
open CKM.NativeFirstOrder CKM.NativeFourFamily CKM.NativeUnlabelledSlice CKM.NativeGoodPhase
open PhasePivotA6 PhasePivotLocusA6 NativeCodeTenPatchesA7 SmallInductiveEuclideanA7

/-- Exact explicit source locus used by the admitted A6/accumulation and
native ten-patch chain. This declaration retains both hypotheses visibly. -/
def nativeAdmittedGoodLocus : Set NativePhaseTorus :=
  {u | IsGoodPhase u.1 ∧ u ∈ nativePivotLocus}

/-- Every open neighborhood of every native good/pivot code class has
small inductive dimension at least ten. The proof uses genuine open patches
and subtype monotonicity, not a finite-quotient dimension assertion. -/
theorem native_code_neighborhood_ind_ge_ten (u : NativePhaseTorus)
    (hu : u ∈ nativeAdmittedGoodLocus)
    {N : Set CodeModuli} (hN : IsOpen N) (hseed : codeClass u ∈ N) :
    (10 : WithBot ℕ∞) ≤ smallInductiveDimension N := by
  obtain ⟨P,hP,hPn,Q,_,hQN,⟨e⟩⟩ := native_code_ten_patches u hu.1 hu.2 hN hseed
  have hQdim : smallInductiveDimension Q = (10 : WithBot ℕ∞) :=
    e.smallInductiveDimension_congr.symm.trans
      (euclidean_open_smallInductiveDimension_eq 10 P hP hPn)
  have hle : smallInductiveDimension Q ≤ smallInductiveDimension N :=
    (Topology.IsEmbedding.inclusion hQN).toIsInducing.smallInductiveDimension_le
  rwa [hQdim] at hle

#print axioms native_code_neighborhood_ind_ge_ten
end Option2.NativeStress.NativeLocalDimensionA7

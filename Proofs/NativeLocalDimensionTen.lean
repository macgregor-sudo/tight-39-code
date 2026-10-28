module

public import NativeCodeDimensionTransfer
public import NativeGoodPhaseQuotientUpper

@[expose] public section

/-! Retained every-good-point A7 local small-inductive dimension statement.
The locus is EXACTLY PhaseA6.nativeA6Locus, already proved nonempty, open and
dense and already carrying the native A6/accumulation outputs. At every point
of this locus all open CodeModuli neighborhoods have ind≥10, and one has ind=10.
The proof uses actual normal zeros, actual finite compensated quotient topology,
and Mathlib smallInductiveDimension. The statement has no additional geometric hypotheses.
-/
set_option autoImplicit false
noncomputable section
namespace Option2.NativeStress.NativeLocalDimensionA7
open CKM.NativeFirstOrder CKM.NativeFourFamily CKM.NativeUnlabelledSlice CKM.NativeGoodPhase
open PhasePivotA6 PhasePivotLocusA6 NativeGoodPhaseQuotientUpper

/-- At each point of the SAME explicit native A6 locus, the actual code
quotient has local small inductive dimension ten in the neighborhood sense:
every open neighborhood has dimension at least ten and one has exactly ten. -/
theorem native_code_local_dimension_ten (u : NativePhaseTorus)
    (hu : u ∈ PhaseA6.nativeA6Locus) :
    (∀ N : Set CodeModuli, IsOpen N → codeClass u ∈ N →
      (10 : WithBot ℕ∞) ≤ smallInductiveDimension N) ∧
    ∃ N : Set CodeModuli, IsOpen N ∧ codeClass u ∈ N ∧
      smallInductiveDimension N = (10 : WithBot ℕ∞) := by
  have hsource : u ∈ nativeAdmittedGoodLocus :=
    nativeAdmittedGoodLocus_eq_nativeA6Locus.symm ▸ hu
  have hlower : ∀ {N : Set CodeModuli}, IsOpen N → codeClass u ∈ N →
      (10 : WithBot ℕ∞) ≤ smallInductiveDimension N :=
    fun hN hseed => native_code_neighborhood_ind_ge_ten u hsource hN hseed
  obtain ⟨W,_,hPW,_,hemb,hdim⟩ := native_good_phase_quotient_upper hu.1
  obtain ⟨N,hN,hseed,hupper⟩ := code_neighborhood_ind_le_ten_of_slice u W hPW hemb hdim
  exact ⟨fun N hN hseed => hlower hN hseed,N,hN,hseed,le_antisymm hupper (hlower hN hseed)⟩

/-- The exact two-inequality formulation of the retained headline. -/
theorem native_code_local_dimension_bounds (u : NativePhaseTorus)
    (hu : u ∈ PhaseA6.nativeA6Locus) :
    (∀ N : Set CodeModuli, IsOpen N → codeClass u ∈ N →
      (10 : WithBot ℕ∞) ≤ smallInductiveDimension N) ∧
    ∃ N : Set CodeModuli, IsOpen N ∧ codeClass u ∈ N ∧
      smallInductiveDimension N ≤ (10 : WithBot ℕ∞) := by
  obtain ⟨hl,N,hN,hseed,hdim⟩ := native_code_local_dimension_ten u hu
  exact ⟨hl,N,hN,hseed,hdim.le⟩

#print axioms native_code_local_dimension_ten
#print axioms native_code_local_dimension_bounds
end Option2.NativeStress.NativeLocalDimensionA7

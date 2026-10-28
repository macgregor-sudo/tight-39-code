module

public import GPCode
public import NativePhasePivotLocus

@[expose] public section

/-!
Native original-code accumulation on the joint good-phase and selected-minor locus.
This imports the existing native polynomial-pivot and quotient-continuity proofs;
it copies no upstream implementation. No distinctness of quotient classes is claimed.
-/
noncomputable section
open Filter Topology
open CKM.NativeFirstOrder CKM.NativeFourFamily CKM.NativeGoodPhase
open CKM.NativeUnlabelledSlice
open Option2.NativeStress.PhasePivotLocusA6

namespace Option2.NativeStress.NativeOriginalCodeA7

/-- The original literal code, with all four phases equal to one, in the actual
unlabelled quotient by Albert automorphisms and point permutations. -/
abbrev originalCode : CodeModuli := codeClass onePhase

theorem good_pivot_iff_goodAvoid (u : PhaseTorus) :
    (IsGoodPhase u.1 ∧ u ∈ nativePivotLocus) ↔ u ∈ GoodAvoid pivotPolynomial := by
  rw [nativePivotLocus_eq_polynomial]
  rfl

/-- The good phases used by the current analytic construction, including its
actual selected-minor hypothesis, accumulate at the original code. -/
theorem exists_good_pivot_code_mem_nhds {V : Set CodeModuli}
    (hV : V ∈ 𝓝 originalCode) :
    ∃ u : PhaseTorus, u ≠ onePhase ∧ IsGoodPhase u.1 ∧
      u ∈ nativePivotLocus ∧ codeClass u ∈ V := by
  obtain ⟨u, hne, hu, hmem⟩ :=
    exists_goodAvoid_codeClass_mem_nhds_one pivotPolynomial_ne_zero hV
  obtain ⟨hgood, hpivot⟩ := (good_pivot_iff_goodAvoid u).mpr hu
  exact ⟨u, hne, hgood, hpivot, hmem⟩

/-- Equivalent closure statement in the native quotient topology. -/
theorem originalCode_mem_closure_good_pivot :
    originalCode ∈ closure (codeClass ''
      {u : PhaseTorus | IsGoodPhase u.1 ∧ u ∈ nativePivotLocus}) := by
  rw [mem_closure_iff_nhds]
  intro V hV
  obtain ⟨u, _, hgood, hpivot, huV⟩ := exists_good_pivot_code_mem_nhds hV
  exact ⟨codeClass u, huV, u, ⟨hgood, hpivot⟩, rfl⟩

end Option2.NativeStress.NativeOriginalCodeA7

#print axioms Option2.NativeStress.NativeOriginalCodeA7.exists_good_pivot_code_mem_nhds
#print axioms Option2.NativeStress.NativeOriginalCodeA7.originalCode_mem_closure_good_pivot

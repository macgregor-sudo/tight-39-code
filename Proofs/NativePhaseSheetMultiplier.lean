module

public import NativePhasePrimeLocalization

@[expose] public section

/-!
# A single native multiplier isolating each constructed analytic sheet

Localized equality at the actual branch prime and Noetherianity supply finitely
many denominators. Their product is nonzero on that sheet and multiplies its
entire prime ideal into the original configuration ideal. This is an equality
of analytic germs, not yet a pointwise real zero-set or smoothness theorem.
Uses the pinned mathlib localization membership theorem without copying code.

-/

noncomputable section
namespace Option2.NativeStress.PhaseSheetMultiplierA7
open CKM.NativeFirstOrder CKM.NativeFourFamily
open PhasePivotA6 PhasePivotLocusA6 PhaseJetBoundA6
open PhaseAnalyticBranchesA6 PhasePrimeLocalizationA6
open ConvergentResidualJets

private theorem common_multiplier {R : Type*} [CommRing R]
    (I P : Ideal R) (hP : P.IsPrime) (s : Finset R)
    (h : ∀ x ∈ s, ∃ k, k ∉ P ∧ k * x ∈ I) :
    ∃ k, k ∉ P ∧ ∀ x ∈ s, k * x ∈ I := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1,hP.one_notMem,by simp⟩
  | @insert x s hx ih =>
    obtain ⟨a,ha,hax⟩ := h x (Finset.mem_insert_self _ _)
    obtain ⟨b,hb,hbmul⟩ := ih (fun y hy => h y (Finset.mem_insert_of_mem hy))
    refine ⟨a*b,fun hab => (hP.mem_or_mem hab).elim ha hb,?_⟩
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · simpa [mul_assoc,mul_left_comm] using I.mul_mem_left b hax
    · simpa [mul_assoc] using I.mul_mem_left a (hbmul y hy)

/-- One denominator works simultaneously for every germ vanishing on the
selected actual branch, rather than only for a single generator. -/
theorem native_phase_sheet_multiplier (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) (H : Fin 4) :
    ∃ k : GermRing 1053,
      (branchPullback H u.1 hgood.1) k ≠ 0 ∧
      ∀ f : GermRing 1053,
        (branchPullback H u.1 hgood.1) f = 0 →
        k * f ∈ nativePhaseAnalyticIdeal u.1 := by
  let := ConvergentGermSCVBridge.germRing_isNoetherianRing 1053
  let P := (nativeSheetPrime u.1 hgood.1 H).asIdeal
  let I := nativePhaseAnalyticIdeal u.1
  let S := Localization.AtPrime P
  have heq : I.map (algebraMap (GermRing 1053) S) =
      P.map (algebraMap (GermRing 1053) S) :=
    (native_phase_dimension62_primes_and_localized_ideal_eq u hgood hpivot).2 H
  obtain ⟨s,hs⟩ := P.fg_of_isNoetherianRing
  have hgen : ∀ x ∈ s, ∃ k, k ∉ P ∧ k*x ∈ I := by
    intro x hx
    have hxP : x ∈ P := hs ▸ Ideal.subset_span hx
    have hxmap : algebraMap (GermRing 1053) S x ∈ I.map (algebraMap _ S) := by
      rw [heq]
      exact Ideal.mem_map_of_mem _ hxP
    obtain ⟨k,hk,hkx⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl S I x).1 hxmap
    exact ⟨k,hk,hkx⟩
  obtain ⟨k,hk,hks⟩ := common_multiplier I P (nativeSheetPrime u.1 hgood.1 H).isPrime s hgen
  refine ⟨k,hk,?_⟩
  intro f hf
  have hfP : f ∈ P := hf
  rw [← hs] at hfP
  refine Submodule.span_induction (p := fun f _ => k * f ∈ I) ?_ ?_ ?_ ?_ hfP
  · exact hks
  · simp
  · intro x y _ _ hx hy
    simpa [mul_add] using I.add_mem hx hy
  · intro a x _ hx
    simpa [mul_assoc,mul_left_comm] using I.mul_mem_left a hx

#print axioms native_phase_sheet_multiplier
end Option2.NativeStress.PhaseSheetMultiplierA7

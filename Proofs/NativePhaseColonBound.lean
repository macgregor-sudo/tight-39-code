module

public import NativePhaseBranchSeparation
public import ConvergentFourBranchColonDimension

@[expose] public section

/-! The actual native residual ideal, the literal intersection of its four
proved branch kernels, and the dimension bound for their colon. The upper
estimate is the existing native analytic-jet theorem, transferred by the
generic shifted ideal-length comparison. No component or multiplicity claim
is made. -/

noncomputable section
namespace Option2.NativeStress.PhaseColonBoundA6
open CKM.NativeFirstOrder CKM.NativeFourFamily
open PhasePivotA6 PhasePivotLocusA6 PhaseJetBoundA6
open PhaseAnalyticBranchesA6 PhaseBranchSeparationA6
open ConvergentResidualJets

/-- The four ACTUAL pullback kernels, without radicalization or replacement. -/
def nativePhaseBranchIntersection (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Ideal (GermRing 1053) :=
  ⨅ H : Fin 4, RingHom.ker (branchPullback H ξ hξ).toRingHom

/-- Artin--Rees transfers the already proved original-F jet bound to the
two lengths for the actual ideal inclusion I ≤ J. -/
theorem native_phase_shifted_upper_bound (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) :
    ∃ c : ℕ, ∀ N : ℕ,
      Module.length (GermRing 1053)
        (ShiftedJetLength.QuotientIdealModule (nativePhaseAnalyticIdeal u.1)
          (nativePhaseBranchIntersection u.1 hgood.1) ⧸
          ((vanishingIdeal 1053 ^ (N+1)) •
            (⊤ : Submodule (GermRing 1053)
              (ShiftedJetLength.QuotientIdealModule (nativePhaseAnalyticIdeal u.1)
                (nativePhaseBranchIntersection u.1 hgood.1))))) +
      Module.length (GermRing 1053)
        (GermRing 1053 ⧸ (nativePhaseBranchIntersection u.1 hgood.1 ⊔
          vanishingIdeal 1053 ^ (N+c+1))) ≤
      ((4 * (N+c+62).choose 62 + 1540 * (N+c+61).choose 61 : ℕ) : ℕ∞) := by
  letI := ConvergentGermSCVBridge.germRing_isNoetherianRing 1053
  have hIJ : nativePhaseAnalyticIdeal u.1 ≤ nativePhaseBranchIntersection u.1 hgood.1 :=
    nativePhaseAnalyticIdeal_le_fourBranchKernels u.1 hgood.1
  obtain ⟨c,hc⟩ := ShiftedJetLength.exists_shifted_jet_length_comparison
    (vanishingIdeal 1053) (nativePhaseAnalyticIdeal u.1)
    (nativePhaseBranchIntersection u.1 hgood.1) hIJ
  exact ⟨c, fun N => (hc N).trans
    (native_phase_analytic_jet_length_bound u hgood hpivot (N+c))⟩

/-- On the actual good-phase pivot locus, removing the four actual branch
kernels leaves a colon quotient of Krull dimension at most 61. The top-colon
case is handled by its zero quotient; properness is not an assumption. -/
theorem native_phase_colon_krullDim_le_sixty_one (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) :
    ringKrullDim (GermRing 1053 ⧸
      (nativePhaseAnalyticIdeal u.1 : Submodule (GermRing 1053) (GermRing 1053)).colon
        (nativePhaseBranchIntersection u.1 hgood.1 : Set (GermRing 1053))) ≤
      (61 : WithBot ℕ∞) := by
  by_cases hK :
      (nativePhaseAnalyticIdeal u.1 : Submodule (GermRing 1053) (GermRing 1053)).colon
        (nativePhaseBranchIntersection u.1 hgood.1 : Set (GermRing 1053)) = ⊤
  · letI : Subsingleton (GermRing 1053 ⧸ _) := Ideal.Quotient.subsingleton_iff.mpr hK
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  · obtain ⟨c,hc⟩ := native_phase_shifted_upper_bound u hgood hpivot
    exact ConvergentFourBranchColonDimension.colon_krullDim_le_sixty_one
      (nativePhaseAnalyticIdeal u.1) (fun H => branchPullback H u.1 hgood.1)
      (fun H => branchPullback_surjective H u.1 hgood.1)
      (fun _ _ hne => branchKernel_not_le hgood hne)
      (nativePhaseAnalyticIdeal_le_fourBranchKernels u.1 hgood.1) hK c hc

#print axioms Option2.NativeStress.PhaseColonBoundA6.native_phase_shifted_upper_bound
#print axioms Option2.NativeStress.PhaseColonBoundA6.native_phase_colon_krullDim_le_sixty_one
end Option2.NativeStress.PhaseColonBoundA6

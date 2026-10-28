module

public import NativePhasePrimeLocalization

@[expose] public section

/-! Standard maximal-ideal jet lengths in the actual native quotient ring.
The existing upper bound and shifted four-branch lower bound are transported
to these intrinsic lengths. No ordinary multiplicity conclusion is made. -/

noncomputable section
namespace Option2.NativeStress.PhaseHilbertSamuelBoundsA6
open CKM.NativeFirstOrder CKM.NativeFourFamily
open PhasePivotA6 PhasePivotLocusA6 PhaseJetBoundA6 PhaseColonBoundA6
open PhaseAnalyticBranchesA6 PhaseBranchSeparationA6
open ConvergentResidualJets

theorem nativePhaseQuotient_nontrivial (u : NativePhaseTorus) :
    Nontrivial (GermRing 1053 ⧸ nativePhaseAnalyticIdeal u.1) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  exact ne_top_of_le_ne_top
    (ConvergentGermSCVBridge.kernel_isPrime (branchPullback 0 u.1 u.2)).ne_top
    (nativePhaseAnalyticIdeal_le_branchKernel 0 u.1 u.2)

/-- Exactly the standard quotient-ring length of its maximal-ideal jet.
The local nontrivial instance is supplied by the actual prime-kernel containment. -/
def nativePhaseIntrinsicJetLength (u : NativePhaseTorus) (N : ℕ) : ℕ∞ :=
  letI := nativePhaseQuotient_nontrivial u
  Module.length (GermRing 1053 ⧸ nativePhaseAnalyticIdeal u.1)
    ((GermRing 1053 ⧸ nativePhaseAnalyticIdeal u.1) ⧸
      IsLocalRing.maximalIdeal (GermRing 1053 ⧸ nativePhaseAnalyticIdeal u.1) ^ (N+1))

theorem nativePhaseIntrinsicJetLength_eq (u : NativePhaseTorus) (N : ℕ) :
    nativePhaseIntrinsicJetLength u N =
      Module.length (GermRing 1053) (GermRing 1053 ⧸
        (nativePhaseAnalyticIdeal u.1 ⊔ vanishingIdeal 1053 ^ (N+1))) := by
  letI := nativePhaseQuotient_nontrivial u
  exact ConvergentResidualColonDimension.quotientJet_length_eq (nativePhaseAnalyticIdeal u.1) N

theorem native_phase_intrinsic_jet_upper_bound (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) (N : ℕ) :
    nativePhaseIntrinsicJetLength u N ≤
      ((4 * (N+62).choose 62 + 1540 * (N+61).choose 61 : ℕ) : ℕ∞) := by
  rw [nativePhaseIntrinsicJetLength_eq]
  exact native_phase_analytic_jet_length_bound u hgood hpivot N

/-- The four actual incomparable branch kernels give the coefficient-four
lower bound with one common order shift. No pivot assumption is needed here. -/
theorem native_phase_intrinsic_jet_shifted_lower_bound (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) :
    ∃ cl : ℕ, ∀ N : ℕ, ((4 * (N+62).choose 62 : ℕ) : ℕ∞) ≤
      nativePhaseIntrinsicJetLength u (N+cl) := by
  obtain ⟨cl,hcl⟩ := ConvergentFourBranchColonDimension.exists_shifted_jet_lower_bound
    (fun H => branchPullback H u.1 hgood.1)
    (fun H => branchPullback_surjective H u.1 hgood.1)
    (fun _ _ hne => branchKernel_not_le hgood hne)
  have hIJ : nativePhaseAnalyticIdeal u.1 ≤ nativePhaseBranchIntersection u.1 hgood.1 :=
    nativePhaseAnalyticIdeal_le_fourBranchKernels u.1 hgood.1
  refine ⟨cl, fun N => ?_⟩
  rw [nativePhaseIntrinsicJetLength_eq]
  have hmono : Module.length (GermRing 1053)
      (GermRing 1053 ⧸ (nativePhaseBranchIntersection u.1 hgood.1 ⊔
        vanishingIdeal 1053 ^ (N+cl+1))) ≤
      Module.length (GermRing 1053)
      (GermRing 1053 ⧸ (nativePhaseAnalyticIdeal u.1 ⊔
        vanishingIdeal 1053 ^ (N+cl+1))) :=
    ShiftedJetLength.length_quotient_le_of_le (sup_le_sup_right hIJ _)
  exact (hcl N).trans hmono

theorem native_phase_intrinsic_jet_length_lt_top (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) (N : ℕ) :
    nativePhaseIntrinsicJetLength u N < ⊤ :=
  (native_phase_intrinsic_jet_upper_bound u hgood hpivot N).trans_lt (ENat.natCast_lt_top _)

#print axioms Option2.NativeStress.PhaseHilbertSamuelBoundsA6.native_phase_intrinsic_jet_upper_bound
#print axioms Option2.NativeStress.PhaseHilbertSamuelBoundsA6.native_phase_intrinsic_jet_shifted_lower_bound
#print axioms Option2.NativeStress.PhaseHilbertSamuelBoundsA6.native_phase_intrinsic_jet_length_lt_top
end Option2.NativeStress.PhaseHilbertSamuelBoundsA6

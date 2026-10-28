module

public import NativePhasePrimeLocalization

@[expose] public section

/-! Concrete analytic branch local algebras and generic reducedness. The result
is only at the four top-prime localizations; no global reducedness or assertion
about smaller components is introduced. -/

noncomputable section
namespace Option2.NativeStress.PhaseTopBranchAlgebrasA6
open CKM.NativeFirstOrder CKM.NativeFourFamily
open PhasePivotA6 PhasePivotLocusA6 PhaseJetBoundA6
open PhaseAnalyticBranchesA6 PhasePrimeLocalizationA6
open ConvergentResidualJets

/-- The actual analytic branch quotient is the actual 62-variable germ algebra. -/
def nativeBranchQuotientEquiv (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (GermRing 1053 ⧸ RingHom.ker (branchPullback H ξ hξ).toRingHom) ≃ₐ[ℂ]
      GermRing 62 :=
  Ideal.quotientKerAlgEquivOfSurjective (branchPullback_surjective H ξ hξ)

/-- The actual native residual quotient at each of its four top primes is a
field. This retains the actual original ideal before localization. -/
theorem native_top_prime_quotient_isField (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) (H : Fin 4) :
    IsField (Localization.AtPrime (nativeSheetPrime u.1 hgood.1 H).asIdeal ⧸
      Ideal.map (algebraMap (GermRing 1053)
        (Localization.AtPrime (nativeSheetPrime u.1 hgood.1 H).asIdeal))
        (nativePhaseAnalyticIdeal u.1)) := by
  rw [(native_phase_dimension62_primes_and_localized_ideal_eq u hgood hpivot).2 H]
  change IsField (Localization.AtPrime (nativeSheetPrime u.1 hgood.1 H).asIdeal ⧸
    (nativeSheetPrime u.1 hgood.1 H).asIdeal.map
      (algebraMap (GermRing 1053)
        (Localization.AtPrime (nativeSheetPrime u.1 hgood.1 H).asIdeal)))
  letI := Ideal.Quotient.field
    ((nativeSheetPrime u.1 hgood.1 H).asIdeal.map
      (algebraMap (GermRing 1053)
        (Localization.AtPrime (nativeSheetPrime u.1 hgood.1 H).asIdeal)))
  exact Field.toIsField _

theorem native_top_prime_quotient_isReduced (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) (H : Fin 4) :
    IsReduced (Localization.AtPrime (nativeSheetPrime u.1 hgood.1 H).asIdeal ⧸
      Ideal.map (algebraMap (GermRing 1053)
        (Localization.AtPrime (nativeSheetPrime u.1 hgood.1 H).asIdeal))
        (nativePhaseAnalyticIdeal u.1)) := by
  letI := (native_top_prime_quotient_isField u hgood hpivot H).isDomain
  infer_instance

#print axioms nativeBranchQuotientEquiv
#print axioms native_top_prime_quotient_isField
#print axioms native_top_prime_quotient_isReduced
end Option2.NativeStress.PhaseTopBranchAlgebrasA6


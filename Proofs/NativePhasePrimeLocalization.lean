module

public import NativePhaseColonBound
public import GermKrullDimSCV
public import FourTopPrimesDimension

@[expose] public section

/-! Ring-theoretic dimension and localization for the actual fixed-phase
original-F ideal and its four proved branch kernels. Generic algebra and
germ-dimension theorems are imported; no fixed-seed native ideal is used.
No ordinary multiplicity or component interpretation is asserted here. -/

noncomputable section
namespace Option2.NativeStress.PhasePrimeLocalizationA6
open CKM.NativeFirstOrder CKM.NativeFourFamily
open PhasePivotA6 PhasePivotLocusA6 PhaseJetBoundA6 PhaseColonBoundA6
open PhaseAnalyticBranchesA6 PhaseBranchSeparationA6
open ConvergentResidualJets

def nativeSheetPrime (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    PrimeSpectrum (GermRing 1053) :=
  ⟨RingHom.ker (branchPullback H ξ hξ).toRingHom,
    ConvergentGermSCVBridge.kernel_isPrime (branchPullback H ξ hξ)⟩

theorem nativeSheetPrime_injective {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    Function.Injective (nativeSheetPrime ξ hξ.1) := by
  intro H H' h
  by_contra hne
  exact branchKernel_not_le hξ hne (le_of_eq (congrArg PrimeSpectrum.asIdeal h))

theorem sheetIntersection_eq (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    FourTopPrimes.sheetIntersection (nativeSheetPrime ξ hξ) =
      nativePhaseBranchIntersection ξ hξ := by
  unfold FourTopPrimes.sheetIntersection nativePhaseBranchIntersection
  exact Finset.inf_univ_eq_iInf _

/-- The actual branch quotient is the 62-variable analytic germ ring, by
the proved surjectivity of the actual branch pullback. -/
theorem native_sheet_quotient_krull_dimension (H : Fin 4) (ξ : Fin 4 → ℂ)
    (hξ : IsUnitPhase ξ) :
    ringKrullDim (GermRing 1053 ⧸ RingHom.ker (branchPullback H ξ hξ).toRingHom) =
      (62 : WithBot ℕ∞) :=
  GermKrullDim.ringKrullDim_quotient_ker_of_surjective'
    (branchPullback H ξ hξ) (branchPullback_surjective H ξ hξ)

theorem native_phase_dimension_lower (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (62 : WithBot ℕ∞) ≤ ringKrullDim (GermRing 1053 ⧸ nativePhaseAnalyticIdeal ξ) := by
  have h0 := nativePhaseAnalyticIdeal_le_branchKernel 0 ξ hξ
  have hle := ringKrullDim_le_of_surjective (Ideal.Quotient.factor h0)
    (Ideal.Quotient.factor_surjective h0)
  rw [native_sheet_quotient_krull_dimension 0 ξ hξ] at hle
  exact hle

/-- Exact dimension-62 minimal primes and equality of localized ideals for
the actual native phase ideal. All maps and dimensions are supplied by proofs. -/
theorem native_phase_dimension62_primes_and_localized_ideal_eq (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) :
    ({p : Ideal (GermRing 1053) | (nativePhaseAnalyticIdeal u.1).IsMinimalPrime p ∧
        ringKrullDim (GermRing 1053 ⧸ p) = (62 : WithBot ℕ∞)} =
      Set.range (fun H => RingHom.ker (branchPullback H u.1 hgood.1).toRingHom)) ∧
    ∀ H : Fin 4,
      Ideal.map (algebraMap (GermRing 1053)
        (Localization.AtPrime (nativeSheetPrime u.1 hgood.1 H).asIdeal))
        (nativePhaseAnalyticIdeal u.1) =
      Ideal.map (algebraMap (GermRing 1053)
        (Localization.AtPrime (nativeSheetPrime u.1 hgood.1 H).asIdeal))
        (RingHom.ker (branchPullback H u.1 hgood.1).toRingHom) := by
  letI := ConvergentGermSCVBridge.germRing_isNoetherianRing 1053
  have hContain : nativePhaseAnalyticIdeal u.1 ≤
      FourTopPrimes.sheetIntersection (nativeSheetPrime u.1 hgood.1) := by
    rw [sheetIntersection_eq]
    exact nativePhaseAnalyticIdeal_le_fourBranchKernels u.1 hgood.1
  have hDim : ∀ H, ringKrullDim (GermRing 1053 ⧸ (nativeSheetPrime u.1 hgood.1 H).asIdeal) =
      (62 : WithBot ℕ∞) := fun H => native_sheet_quotient_krull_dimension H u.1 hgood.1
  have hDrop : ringKrullDim (GermRing 1053 ⧸
      FourTopPrimes.residualColon (nativePhaseAnalyticIdeal u.1)
        (nativeSheetPrime u.1 hgood.1)) ≤ (61 : WithBot ℕ∞) := by
    unfold FourTopPrimes.residualColon
    rw [sheetIntersection_eq]
    exact native_phase_colon_krullDim_le_sixty_one u hgood hpivot
  exact FourTopPrimes.top_minimalPrimes_and_localized_ideal_eq
    (nativePhaseAnalyticIdeal u.1) (nativeSheetPrime u.1 hgood.1)
    (nativeSheetPrime_injective hgood) hContain hDim hDrop

/-- Every prime over the actual native phase ideal has quotient dimension at
most 62, by the colon bound or containment of one actual branch kernel. -/
theorem native_phase_prime_quotient_dimension_upper (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus)
    (p : Ideal (GermRing 1053)) (hp : p.IsPrime) (hIp : nativePhaseAnalyticIdeal u.1 ≤ p) :
    ringKrullDim (GermRing 1053 ⧸ p) ≤ (62 : WithBot ℕ∞) := by
  classical
  let K := (nativePhaseAnalyticIdeal u.1 : Submodule (GermRing 1053) (GermRing 1053)).colon
    (nativePhaseBranchIntersection u.1 hgood.1 : Set (GermRing 1053))
  by_cases hKp : K ≤ p
  · exact (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hKp)
      (Ideal.Quotient.factor_surjective hKp)).trans
      ((native_phase_colon_krullDim_le_sixty_one u hgood hpivot).trans (by norm_num))
  · have hKJ : K * Finset.univ.inf
        (fun H : Fin 4 => RingHom.ker (branchPullback H u.1 hgood.1).toRingHom) ≤
        nativePhaseAnalyticIdeal u.1 := by
      simpa only [Finset.inf_univ_eq_iInf, K, nativePhaseBranchIntersection] using
        MinimalPrimeExhaustion.colon_mul_le (nativePhaseAnalyticIdeal u.1)
          (nativePhaseBranchIntersection u.1 hgood.1)
    obtain ⟨H, _, hHp⟩ := MinimalPrimeExhaustion.exists_le_of_isPrime_of_not_le
      Finset.univ (fun H : Fin 4 => RingHom.ker (branchPullback H u.1 hgood.1).toRingHom)
      (nativePhaseAnalyticIdeal u.1) K hKJ hp hIp hKp
    have hle := ringKrullDim_le_of_surjective (Ideal.Quotient.factor hHp)
      (Ideal.Quotient.factor_surjective hHp)
    rw [native_sheet_quotient_krull_dimension H u.1 hgood.1] at hle
    exact hle

theorem native_phase_dimension_upper (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) :
    ringKrullDim (GermRing 1053 ⧸ nativePhaseAnalyticIdeal u.1) ≤ (62 : WithBot ℕ∞) := by
  rw [ringKrullDim, Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro q
  let f := PrimeSpectrum.comap (Ideal.Quotient.mk (nativePhaseAnalyticIdeal u.1))
  have hf : StrictMono f :=
    Monotone.strictMono_of_injective
      (fun _ _ hab => Ideal.comap_mono hab)
      (PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective)
  have hco := Order.coheight_le_coheight_apply_of_strictMono f hf q
  have hIp : nativePhaseAnalyticIdeal u.1 ≤ (f q).asIdeal := by
    intro x hx
    change Ideal.Quotient.mk (nativePhaseAnalyticIdeal u.1) x ∈ q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact q.asIdeal.zero_mem
  have hup := native_phase_prime_quotient_dimension_upper u hgood hpivot
    (f q).asIdeal (f q).isPrime hIp
  rw [FourTopPrimes.ringKrullDim_quotient_eq_coheight] at hup
  exact (WithBot.coe_le_coe.mpr hco).trans hup

theorem native_phase_dimension_eq (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) :
    ringKrullDim (GermRing 1053 ⧸ nativePhaseAnalyticIdeal u.1) = (62 : WithBot ℕ∞) :=
  le_antisymm (native_phase_dimension_upper u hgood hpivot)
    (native_phase_dimension_lower u.1 hgood.1)

#print axioms Option2.NativeStress.PhasePrimeLocalizationA6.native_sheet_quotient_krull_dimension
#print axioms Option2.NativeStress.PhasePrimeLocalizationA6.native_phase_dimension62_primes_and_localized_ideal_eq
#print axioms Option2.NativeStress.PhasePrimeLocalizationA6.native_phase_prime_quotient_dimension_upper
#print axioms Option2.NativeStress.PhasePrimeLocalizationA6.native_phase_dimension_eq
end Option2.NativeStress.PhasePrimeLocalizationA6

module

public import GPPhase
public import NativePhaseOrdinaryMultiplicity
public import NativePhaseTopBranchAlgebras
public import NativePhaseRealLocus

@[expose] public section

/-! Native A6 assembly on the exact good-phase/Jacobian-pivot locus.
Conclusions use analytic local algebras, their top minimal primes and actual
branch pullbacks. The real statements concern the four retained branch
families; no all-component or all-real-zero exhaustion is asserted. -/
noncomputable section
namespace Option2.NativeStress.PhaseA6
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open PhasePivotA6 PhasePivotLocusA6 PhaseJetBoundA6 PhaseAnalyticBranchesA6
open PhasePrimeLocalizationA6 PhaseTopBranchAlgebrasA6
open PhaseHilbertSamuelBoundsA6 PhaseOrdinaryMultiplicityA6
open PhaseEntireFamilyA6 PhaseRealLocusA6 PhaseRealSliceNormalFormA6
open ConvergentResidualJets Filter Polynomial
open scoped Topology

/-- The actual twelve-test good-phase locus intersected with the actual
selected native 973-minor locus, in the original four unit phase variables. -/
def nativeA6Locus : Set NativePhaseTorus :=
  {u | IsGoodPhase u.1} ∩ nativePivotLocus

theorem nativeA6Locus_eq_goodAvoid :
    nativeA6Locus = CKM.NativeGoodPhase.GoodAvoid pivotPolynomial := by
  rw [nativeA6Locus, nativePivotLocus_eq_polynomial]
  rfl

theorem isOpen_dense_nativeA6Locus : IsOpen nativeA6Locus ∧ Dense nativeA6Locus := by
  rw [nativeA6Locus_eq_goodAvoid]
  exact CKM.NativeGoodPhase.isOpen_dense_goodAvoid pivotPolynomial_ne_zero

theorem nativeA6Locus_nonempty : nativeA6Locus.Nonempty := by
  letI : Nonempty NativePhaseTorus := ⟨referenceNativePhase⟩
  exact isOpen_dense_nativeA6Locus.2.nonempty

/-- Readable collection of proved outputs, all on the actual native ideal
and its actual four branch maps. This is not a new definition of component. -/
structure NativeA6LocalAlgebra (u : NativePhaseTorus) : Prop where
  dimension : ringKrullDim (GermRing 1053 ⧸ nativePhaseAnalyticIdeal u.1) =
    (62 : WithBot ℕ∞)
  ordinaryPolynomial : ∃! q : ℚ[X],
    (∀ᶠ N : ℕ in atTop,
      ((nativePhaseIntrinsicJetLength u N).toNat : ℚ) = q.eval (N : ℚ)) ∧
    q.degree = (62 : WithBot ℕ) ∧ (Nat.factorial 62 : ℚ) * q.leadingCoeff = 4
  distinctPrimes : Function.Injective (nativeSheetPrime u.1 u.2)
  topPrimes :
    {p : Ideal (GermRing 1053) | (nativePhaseAnalyticIdeal u.1).IsMinimalPrime p ∧
      ringKrullDim (GermRing 1053 ⧸ p) = (62 : WithBot ℕ∞)} =
    Set.range (fun H => RingHom.ker (branchPullback H u.1 u.2).toRingHom)
  localizedIdeal : ∀ H : Fin 4,
    Ideal.map (algebraMap (GermRing 1053)
      (Localization.AtPrime (nativeSheetPrime u.1 u.2 H).asIdeal))
      (nativePhaseAnalyticIdeal u.1) =
    Ideal.map (algebraMap (GermRing 1053)
      (Localization.AtPrime (nativeSheetPrime u.1 u.2 H).asIdeal))
      (RingHom.ker (branchPullback H u.1 u.2).toRingHom)
  branchAlgebras : ∀ H : Fin 4, Nonempty
    ((GermRing 1053 ⧸ RingHom.ker (branchPullback H u.1 u.2).toRingHom) ≃ₐ[ℂ]
      GermRing 62)
  localizedField : ∀ H : Fin 4,
    IsField (Localization.AtPrime (nativeSheetPrime u.1 u.2 H).asIdeal ⧸
      Ideal.map (algebraMap (GermRing 1053)
        (Localization.AtPrime (nativeSheetPrime u.1 u.2 H).asIdeal))
        (nativePhaseAnalyticIdeal u.1))
  localizedReduced : ∀ H : Fin 4,
    IsReduced (Localization.AtPrime (nativeSheetPrime u.1 u.2 H).asIdeal ⧸
      Ideal.map (algebraMap (GermRing 1053)
        (Localization.AtPrime (nativeSheetPrime u.1 u.2 H).asIdeal))
        (nativePhaseAnalyticIdeal u.1))
  realBranchLocus : ∀ H : Fin 4,
    ∃ U : Set (Fin 62 → ℂ), U ∈ 𝓝 0 ∧
      (branch H u.1 u.2 '' U) ∩ {y : Fin 1053 → ℂ | ∀ k, (y k).im = 0} =
        (fun x : Fin 62 → ℝ =>
          (fun k => ((NativePolynomial.PartialAction.pack
            (rawMap62 u.1 u.2 H (realParam (fun j => x (paramIndexEquiv j)))) k : ℝ) : ℂ)) -
              AnalyticDerivative.complexPack (literalCfg u.1)) ''
          {x : Fin 62 → ℝ | (fun j => (x j : ℂ)) ∈ U}
  realSliceNormalForm :
    ∃ Φ : OpenPartialHomeomorph SliceModel (normalC u.1),
      ∃ V₀ : Fin 4 → Set SliceParam,
      (0 : SliceModel) ∈ Φ.source ∧ Φ 0 = 0 ∧
      AnalyticOnNhd ℝ Φ Φ.source ∧ AnalyticOnNhd ℝ Φ.symm Φ.target ∧
      (∀ H, V₀ H ∈ 𝓝 (0 : SliceParam)) ∧
      ∀ V : Fin 4 → Set SliceParam,
        (∀ H, V H ∈ 𝓝 (0 : SliceParam)) → (∀ H, V H ⊆ V₀ H) →
        ∀ᶠ n : normalC u.1 in 𝓝 0, n ∈ Φ.target ∧
          (n ∈ ⋃ H : Fin 4, (sliceFam u.1 u.2 H) '' V H ↔
            ∃ H : Fin 4,
              (∀ j : Fin 4, j ≠ H → (Φ.symm n).2.1 j = 0) ∧
              (Φ.symm n).2.2 = 0)

/-- All output facts follow on the explicit native locus, with no extra
rank, quadratic, branch, Hilbert or multiplicity hypotheses. -/
theorem native_phase_A6 (u : NativePhaseTorus) (hu : u ∈ nativeA6Locus) :
    NativeA6LocalAlgebra u := by
  obtain ⟨hgood,hpivot⟩ := hu
  have htop := native_phase_dimension62_primes_and_localized_ideal_eq u hgood hpivot
  exact
    { dimension := native_phase_dimension_eq u hgood hpivot
      ordinaryPolynomial := native_phase_unique_hilbertSamuel_polynomial u hgood hpivot
      distinctPrimes := nativeSheetPrime_injective hgood
      topPrimes := htop.1
      localizedIdeal := htop.2
      branchAlgebras := fun H => ⟨nativeBranchQuotientEquiv H u.1 u.2⟩
      localizedField := native_top_prime_quotient_isField u hgood hpivot
      localizedReduced := native_top_prime_quotient_isReduced u hgood hpivot
      realBranchLocus := fun H => branch_local_real_locus_eq_real_family H u.1 u.2
      realSliceNormalForm := retained_real_slice_union_normal_form hgood }

#print axioms Option2.NativeStress.PhaseA6.nativeA6Locus_nonempty
#print axioms Option2.NativeStress.PhaseA6.isOpen_dense_nativeA6Locus
#print axioms Option2.NativeStress.PhaseA6.native_phase_A6
end Option2.NativeStress.PhaseA6

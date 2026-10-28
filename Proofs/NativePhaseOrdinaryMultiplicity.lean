module

public import NativePhaseJetAsymptotics
public import HSHilbertSerre
public import HilbertSamuelPolynomialMultiplicity

@[expose] public section

/-! The ordinary Hilbert--Samuel polynomial of the actual native analytic
quotient. Polynomial existence is supplied by the selected, attributed OAI
Hilbert--Serre port. Its exponent n is shifted to the native N+1 convention.
The proved native asymptotic then identifies degree and ordinary factorial-
scaled leading coefficient; a limit is not used as a replacement definition.
All intrinsic lengths are finite by native_phase_intrinsic_jet_length_lt_top. -/
noncomputable section
namespace Option2.NativeStress.PhaseOrdinaryMultiplicityA6
open Filter Polynomial
open CKM.NativeFourFamily
open PhasePivotLocusA6 PhaseJetBoundA6 PhaseHilbertSamuelBoundsA6
open PhaseJetAsymptoticsA6 HilbertSamuelPolynomialCoefficient
open ConvergentResidualJets
open scoped Topology

/-- The unique eventual rational polynomial for the standard maximal-ideal
jet lengths of the actual native quotient has degree 62 and ordinary
Hilbert--Samuel multiplicity 62! times its leading coefficient equal to 4. -/
theorem native_phase_unique_hilbertSamuel_polynomial (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) :
    ∃! q : ℚ[X],
      (∀ᶠ N : ℕ in atTop,
        ((nativePhaseIntrinsicJetLength u N).toNat : ℚ) = q.eval (N : ℚ)) ∧
      q.degree = (62 : WithBot ℕ) ∧ (Nat.factorial 62 : ℚ) * q.leadingCoeff = 4 := by
  letI := nativePhaseQuotient_nontrivial u
  letI := ConvergentGermSCVBridge.germRing_isNoetherianRing 1053
  let A := GermRing 1053 ⧸ nativePhaseAnalyticIdeal u.1
  let m : Ideal A := IsLocalRing.maximalIdeal A
  obtain ⟨p,hp⟩ := OAI.Lech.IdealGraded.eventuallyPolynomial_length m
  let q : ℚ[X] := p.comp (X + 1)
  have hq : ∀ᶠ N : ℕ in atTop,
      ((nativePhaseIntrinsicJetLength u N).toNat : ℚ) = q.eval (N : ℚ) := by
    have hshift := (Filter.tendsto_add_atTop_nat 1).eventually hp
    filter_upwards [hshift] with N hN
    change ((Module.length A (A ⧸ m ^ (N+1))).toNat : ℚ) = q.eval (N : ℚ)
    simpa only [q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one, Nat.cast_add, Nat.cast_one] using hN
  obtain ⟨hdegree,hleading⟩ :=
    degree_and_factorial_leadingCoeff_of_eventual_nat_polynomial
      (fun N => (nativePhaseIntrinsicJetLength u N).toNat) q 62 4 (by norm_num) hq
      (native_phase_normalized_intrinsic_jet_tendsto u hgood hpivot)
  refine ⟨q,⟨hq,hdegree,hleading⟩,?_⟩
  intro r hr
  exact eventual_nat_polynomial_unique
    (fun N => (nativePhaseIntrinsicJetLength u N).toNat) r q hr.1 hq

#print axioms Option2.NativeStress.PhaseOrdinaryMultiplicityA6.native_phase_unique_hilbertSamuel_polynomial
end Option2.NativeStress.PhaseOrdinaryMultiplicityA6

module

public import NativePhaseBook48Consumer
public import PolynomialJetSharpBoundModule
public import NativeConfigurationPolynomialDegree
public import NativeConfigurationResidualJetLength
public import NativeConfigurationJetTransfer

@[expose] public section

/-! Polynomial and analytic jets of all original 2184 residuals at the actual
literal phase configuration. The same half/third coefficients and translation
point are retained throughout. No multiplicity or component claim is made. -/

noncomputable section
namespace Option2.NativeStress.PhaseJetBoundA6
open MvPolynomial Module PolynomialJets
open PhasePivotA6 PhasePivotLocusA6 PhaseHilbertA6 PhaseBook48ConsumerA6
open CKM.NativeFirstOrder CKM.NativeFourFamily AnalyticDerivative
open NativePolynomial NativePolynomial.ConfigurationResiduals
open ConvergentResidualJets
open scoped BigOperators

/-- Complex evaluation of each unchanged original row at the actual unit-phase
solution, obtained from its proved real evaluation. -/
theorem native_phase_original_rows_vanish (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (r : Fin 2184) :
    eval (complexPack (literalCfg ξ)) (fRow (1/2 : ℂ) (1/3 : ℂ) r) = 0 := by
  have hrow : eval (complexPack (literalCfg ξ)) (fRow (1/2 : ℂ) (1/3 : ℂ) r) =
      (Option2.NativeStress.originalF (PartialAction.pack (literalCfg ξ)) r : ℂ) := by
    rw [NativeH.Reproduction.originalF_complex, QuarticCertificate.RowBridge.eval_fRow]
    rfl
  have hr : Option2.NativeStress.originalF (PartialAction.pack (literalCfg ξ)) r = 0 :=
    literalCfg_all_original_F ξ hξ r
  rw [hrow, hr, Complex.ofReal_zero]

theorem nativeRows_coeff_zero (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (r : Fin 2184) :
    (nativeRows ξ r).coeff 0 = 0 := by
  have h := ConvergentResidualPointBinding.evalAtZero_polynomialGerm_translate
    (complexPack (literalCfg ξ)) (fRow (1/2 : ℂ) (1/3 : ℂ) r)
  rw [ConvergentResidualPointBinding.evalAtZero_polynomialGerm, MvPolynomial.eval_zero] at h
  exact h.trans (native_phase_original_rows_vanish ξ hξ r)

theorem nativeRows_totalDegree_le_two (ξ : Fin 4 → ℂ) (r : Fin 2184) :
    (nativeRows ξ r).totalDegree ≤ 2 :=
  translated_fRow_totalDegree_le_two (1/2) (1/3) (complexPack (literalCfg ξ)) r

/-- The actual original polynomial jets on the good-phase pivot locus.
Every stress and every homogeneous degree bound is supplied by the proved
native Book endpoint; no finite-certificate premise remains. -/
theorem native_phase_polynomial_jet_bound (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) (N : ℕ) :
    finrank ℂ (equationJet (nativeRows u.1) N) ≤
      4 * (N+62).choose 62 + 1540 * (N+61).choose 61 := by
  obtain ⟨w,hw,hbound⟩ := native_phase_cumulative_relations u hgood hpivot
  exact (equationJet_finrank_le_cumulative_relations (nativeRows u.1) id w N
    (nativeRows_totalDegree_le_two u.1) (nativeRows_coeff_zero u.1 hgood.1) hw).trans (hbound N)

/-- The actual original-F analytic ideal at complexPack(literalCfg ξ), expressed
as germs in displacement coordinates centered at that same point. -/
def nativePhaseAnalyticIdeal (ξ : Fin 4 → ℂ) : Ideal (GermRing 1053) :=
  Ideal.map (polynomialGerm 1053).toRingHom (Ideal.span (Set.range (nativeRows ξ)))

theorem nativePhaseAnalyticIdeal_le_vanishingIdeal (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    nativePhaseAnalyticIdeal ξ ≤ vanishingIdeal 1053 := by
  exact (translated_fSpan_germ_le_vanishingIdeal_iff (1/2) (1/3)
    (complexPack (literalCfg ξ))).2 (native_phase_original_rows_vanish ξ hξ)

/-- The truncated length of the literal original-F analytic ideal inherits the
polynomial bound at the SAME arbitrary native phase point. -/
theorem native_phase_analytic_jet_length_bound (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) (N : ℕ) :
    Module.length (GermRing 1053)
      (GermRing 1053 ⧸ (nativePhaseAnalyticIdeal u.1 ⊔ vanishingIdeal 1053 ^ (N+1))) ≤
      ((4 * (N+62).choose 62 + 1540 * (N+61).choose 61 : ℕ) : ℕ∞) := by
  have hEq := (translated_equationJetEquiv (1/2 : ℂ) (1/3 : ℂ)
    (by norm_num) (by norm_num) (complexPack (literalCfg u.1)) N).finrank_eq
  have hG : finrank ℂ (MvPolynomial (Fin 1053) ℂ ⧸ equationJetSubmodule
      (fun r : Fin 3159 => translate (complexPack (literalCfg u.1))
        (gRow (1/2 : ℂ) (1/3 : ℂ) r)) N) ≤
      4 * (N+62).choose 62 + 1540 * (N+61).choose 61 :=
    hEq.symm.le.trans (native_phase_polynomial_jet_bound u hgood hpivot N)
  have hL := translated_f_analyticJet_length_le_g_polynomialJet
    (1/2 : ℂ) (1/3) (by norm_num) (by norm_num) (complexPack (literalCfg u.1)) N
  change Module.length (GermRing 1053)
      (GermRing 1053 ⧸ (nativePhaseAnalyticIdeal u.1 ⊔ vanishingIdeal 1053 ^ (N+1))) ≤
    (finrank ℂ (MvPolynomial (Fin 1053) ℂ ⧸ equationJetSubmodule
      (fun r : Fin 3159 => translate (complexPack (literalCfg u.1))
        (gRow (1/2 : ℂ) (1/3 : ℂ) r)) N) : ℕ∞) at hL
  exact hL.trans (ENat.natCast_le_natCast.mpr hG)

#print axioms Option2.NativeStress.PhaseJetBoundA6.native_phase_polynomial_jet_bound
#print axioms Option2.NativeStress.PhaseJetBoundA6.native_phase_analytic_jet_length_bound
end Option2.NativeStress.PhaseJetBoundA6

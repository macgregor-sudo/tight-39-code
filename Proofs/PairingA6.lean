module
public import PairingDefinitions
public import PairingA5Geometry
public import PairingA6Witness
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
/-
The analytic-representative carrier, constant map and evaluation below adapt
SeveralComplexVariables/AnalyticGerm.lean, declarations analyticGermSubring,
AnalyticGerm.ofAnalyticAt, AnalyticGerm.const and AnalyticGerm.eval, from
https://github.com/bjbraams/lean-SCV at
50392764ae64d75779abbea1396fe93d80b677cc.
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in that repository's LICENSE.
Authors: Bastiaan J Braams
Modifications: specialize to complex germs at zero in finite coordinate spaces;
omit the local-ring, zero-set and Noetherian development; add the polynomial
residual quotient map. Adapted portions retain their upstream license.
Thank you to the author and the Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/
/- The shared carrier, algebra structure and native ideal are defined in
PairingDefinitions; this module assembles the actual branch pullbacks. -/
noncomputable section
open Filter
open scoped Topology
namespace Option2StatementA6
/- Actual neighborhood germs having a representative analytic at zero. -/
end Option2StatementA6
/- Exact original 973-minor row/column selectors, extracted from first-party
A6LinLUData. No LU factors, altered ordering, or rank surrogate are included. -/
namespace Option2StatementA6
end Option2StatementA6
/- The native complex component theorem uses the shared analytic-germ carrier
and the real family geometry, with the explicit pivot locus below. -/
namespace Option2StatementA6
open CKM.NativeFirstOrder
open CKM.NativeFourFamily (IsGoodPhase)
open Option2StatementA5Raw Option2StatementA5Slice
open Filter Polynomial
open scoped Topology

theorem native_A6 :
    ∃ rows : (Fin 4 → ℂ) → Fin 2184 → MvPolynomial (Fin 1053) ℂ,
      (∀ ξ x r, MvPolynomial.eval (fun j => (x j : ℂ)) (rows ξ r) =
        (Option2StatementResidual.originalF (displaced ξ x) r : ℂ)) ∧
      IsOpen (replacementLocus rows) ∧ Dense (replacementLocus rows) ∧
      (replacementLocus rows).Nonempty ∧
      ∀ u ∈ replacementLocus rows, ∃ m : Product, NativeProduct m ∧
        ∃ σ : OpenPartialHomeomorph (derOf m × normal m u.1) Cfg,
          (0 : derOf m × normal m u.1) ∈ σ.source ∧
          (∀ p, σ p = sliceChart m u.1 p) ∧
          ∃ (e : (Fin 62 → ℝ) ≃ₗ[ℝ] RawParam62 m)
            (B : Fin 4 → (Fin 62 → ℂ) → (Fin 1053 → ℂ))
            (ρ : Fin 4 → GermRing 1053 →ₐ[ℂ] GermRing 62)
            (P : Fin 4 → PrimeSpectrum (GermRing 1053)),
            (∀ H, B H 0 = 0) ∧ (∀ H, Differentiable ℂ (B H)) ∧
            (∀ H, AnalyticAt ℂ (B H) 0) ∧
            (∀ H x, B H (fun k => (x k : ℂ)) =
              packC (rawMap62 m u.1 u.2 H (e x)) - packC (literalCfg u.1)) ∧
            (∀ H f (hf : AnalyticAt ℂ f 0) (hc : AnalyticAt ℂ (f ∘ B H) 0),
              ρ H (ofAnalyticAt f hf) = ofAnalyticAt (f ∘ B H) hc) ∧
            A6Output m u σ (rows u.1) B ρ P e := by
  letI : Module.Free ℝ CKM.NativeGroupSlice.derC := Module.Free.of_divisionRing ℝ CKM.NativeGroupSlice.derC
  let rows := Option2.NativeStress.PhaseHilbertA6.nativeRows
  have hl : replacementLocus rows = Option2.NativeStress.PhaseA6.nativeA6Locus := rfl
  refine ⟨rows, ?_, ?_, ?_, ?_, ?_⟩
  · intro ξ x r
    rw [Option2StatementResidual.originalF_eq_native]
    have hp : NativePolynomial.PartialAction.pack (displaced ξ x) =
        NativePolynomial.PartialAction.pack (literalCfg ξ) + x := by
      funext k
      simp only [NativePolynomial.PartialAction.pack, displaced, Pi.add_apply]
      congr 1
      exact congrArg x ((finProdFinEquiv : Fin 39 × Fin 27 ≃ Fin 1053).apply_symm_apply k)
    change MvPolynomial.eval _ (Option2.NativeStress.PhaseHilbertA6.nativeRows ξ r) =
      (MvPolynomial.eval (NativePolynomial.PartialAction.pack (displaced ξ x))
        (NativePolynomial.ConfigurationResiduals.fRow (1/2 : ℝ) (1/3 : ℝ) r) : ℂ)
    rw [hp]
    exact Option2.NativeStress.PhaseRealSheetIsolationA7.nativeRows_real_eval ξ x r
  · rw [hl]; exact Option2.NativeStress.PhaseA6.isOpen_dense_nativeA6Locus.1
  · rw [hl]; exact Option2.NativeStress.PhaseA6.isOpen_dense_nativeA6Locus.2
  · rw [hl]; exact Option2.NativeStress.PhaseA6.nativeA6Locus_nonempty
  · intro u hu
    have hu' : u ∈ Option2.NativeStress.PhaseA6.nativeA6Locus := hl ▸ hu
    let e := Option2StatementA6Witness.realCoordinates.trans
      Option2.NativeStress.PhaseBranchDerivativeA6.realParamEquiv
    refine ⟨CKM.NativeGroupSlice.prodC, CKM.NativeGroupSlice.prodC_eq_native,
      CKM.NativeGroupSlice.slicePH u.1 u.2,
      CKM.NativeGroupSlice.zero_mem_slicePH_source u.1 u.2, (fun _ => rfl),
      e, (fun H => Option2.NativeStress.PhaseAnalyticBranchesA6.branch H u.1 u.2),
      (fun H => Option2.NativeStress.PhaseAnalyticBranchesA6.branchPullback H u.1 u.2),
      Option2.NativeStress.PhasePrimeLocalizationA6.nativeSheetPrime u.1 u.2,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun H => Option2.NativeStress.PhaseAnalyticBranchesA6.branch_zero H u.1 u.2
    · exact fun H => Option2.NativeStress.PhaseAnalyticBranchesA6.branch_entire H u.1 u.2
    · exact fun H => Option2.NativeStress.PhaseAnalyticBranchesA6.branch_analyticAt H u.1 u.2
    · intro H x
      have he : e x = Option2.NativeStress.PhaseEntireFamilyA6.realParam
          (fun j => x (Option2.NativeStress.PhaseAnalyticBranchesA6.paramIndexEquiv j)) := by
        rw [LinearEquiv.trans_apply, Option2.NativeStress.PhaseBranchDerivativeA6.realParamEquiv_apply]
        rfl
      change Option2.NativeStress.PhaseAnalyticBranchesA6.branch H u.1 u.2 (fun k => (x k : ℂ)) =
        (fun k => ((NativePolynomial.PartialAction.pack (CKM.NativeFourFamily.rawMap62 u.1 u.2 H (e x))) k : ℂ)) -
          Option2.NativeStress.AnalyticDerivative.complexPack (literalCfg u.1)
      rw [he]
      exact Option2.NativeStress.PhaseRealSliceNormalFormA6.branch_real_parameters H u.1 u.2 x
    · intro H f hf hc
      exact AnalyticPullback.pullback_ofAnalyticAt _ _ _ f hf
    · have h := Option2.NativeStress.PhaseA6.native_phase_A6 u hu'
      refine ⟨(fun H => rfl), h.dimension, ?_, h.distinctPrimes,
        h.topPrimes, h.localizedIdeal, h.branchAlgebras, h.localizedField,
        h.localizedReduced, ?_, h.realSliceNormalForm⟩
      · have hj (N : ℕ) : jetLength (rows u.1) N =
            Option2.NativeStress.PhaseHilbertSamuelBoundsA6.nativePhaseIntrinsicJetLength u N := by
          rw [Option2.NativeStress.PhaseHilbertSamuelBoundsA6.nativePhaseIntrinsicJetLength_eq]
          rfl
        simpa only [hj] using h.ordinaryPolynomial
      · have he (x : Fin 62 → ℝ) : e x = Option2.NativeStress.PhaseEntireFamilyA6.realParam
            (fun j => x (Option2.NativeStress.PhaseAnalyticBranchesA6.paramIndexEquiv j)) := by
          rw [LinearEquiv.trans_apply, Option2.NativeStress.PhaseBranchDerivativeA6.realParamEquiv_apply]
          rfl
        change ∀ H : Fin 4, ∃ U : Set (Fin 62 → ℂ), U ∈ 𝓝 0 ∧
          (Option2.NativeStress.PhaseAnalyticBranchesA6.branch H u.1 u.2 '' U) ∩
            {y : Fin 1053 → ℂ | ∀ k, (y k).im = 0} =
          (fun x : Fin 62 → ℝ => (fun k => ((NativePolynomial.PartialAction.pack
            (CKM.NativeFourFamily.rawMap62 u.1 u.2 H (e x))) k : ℂ)) -
            Option2.NativeStress.AnalyticDerivative.complexPack (literalCfg u.1)) ''
            {x : Fin 62 → ℝ | (fun j => (x j : ℂ)) ∈ U}
        simpa only [he] using h.realBranchLocus

end Option2StatementA6

#print axioms Option2StatementA6.native_A6

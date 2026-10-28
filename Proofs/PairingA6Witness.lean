module
public import PairingDefinitions
public import NativePhaseA6
public import NativePhaseRealSheetIsolation
@[expose] public section
/-! Native adapter for an existential-witness A6 interface. Not a standalone
Challenge import closure; the compact germ definitions and A5 constructors
must be supplied separately. Existing source provenance remains unchanged. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Option2StatementA6Witness
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open Option2.NativeStress
open PhaseA6 PhaseHilbertA6 PhasePivotLocusA6 PhaseAnalyticBranchesA6
open PhasePrimeLocalizationA6 PhaseRealSliceNormalFormA6 PhaseEntireFamilyA6
open PhaseBranchDerivativeA6 PhaseHilbertSamuelBoundsA6
open ConvergentResidualJets Filter Polynomial
open scoped Topology

def rowIdeal (rows : Fin 2184 → MvPolynomial (Fin 1053) ℂ) : Ideal (GermRing 1053) :=
  Ideal.map (polynomialGerm 1053).toRingHom (Ideal.span (Set.range rows))
def jetLength (rows : Fin 2184 → MvPolynomial (Fin 1053) ℂ) (N : ℕ) : ℕ∞ :=
  Module.length (GermRing 1053)
    (GermRing 1053 ⧸ (rowIdeal rows ⊔ vanishingIdeal 1053 ^ (N+1)))
structure A6Output (u : NativePhaseTorus)
    (rows : Fin 2184 → MvPolynomial (Fin 1053) ℂ)
    (B : Fin 4 → (Fin 62 → ℂ) → (Fin 1053 → ℂ))
    (ρ : Fin 4 → GermRing 1053 →ₐ[ℂ] GermRing 62)
    (P : Fin 4 → PrimeSpectrum (GermRing 1053))
    (e : (Fin 62 → ℝ) ≃ₗ[ℝ] RawParam62) : Prop where
  primeBinding : ∀ H, (P H).asIdeal = RingHom.ker (ρ H).toRingHom
  dimension : ringKrullDim (GermRing 1053 ⧸ rowIdeal rows) =
    (62 : WithBot ℕ∞)
  ordinaryPolynomial : ∃! q : ℚ[X],
    (∀ᶠ N : ℕ in atTop,
      ((jetLength rows N).toNat : ℚ) = q.eval (N : ℚ)) ∧
    q.degree = (62 : WithBot ℕ) ∧ (Nat.factorial 62 : ℚ) * q.leadingCoeff = 4
  distinctPrimes : Function.Injective (P)
  topPrimes :
    {p : Ideal (GermRing 1053) | (rowIdeal rows).IsMinimalPrime p ∧
      ringKrullDim (GermRing 1053 ⧸ p) = (62 : WithBot ℕ∞)} =
    Set.range (fun H => RingHom.ker (ρ H).toRingHom)
  localizedIdeal : ∀ H : Fin 4,
    Ideal.map (algebraMap (GermRing 1053)
      (Localization.AtPrime (P H).asIdeal))
      (rowIdeal rows) =
    Ideal.map (algebraMap (GermRing 1053)
      (Localization.AtPrime (P H).asIdeal))
      (RingHom.ker (ρ H).toRingHom)
  branchAlgebras : ∀ H : Fin 4, Nonempty
    ((GermRing 1053 ⧸ RingHom.ker (ρ H).toRingHom) ≃ₐ[ℂ]
      GermRing 62)
  localizedField : ∀ H : Fin 4,
    IsField (Localization.AtPrime (P H).asIdeal ⧸
      Ideal.map (algebraMap (GermRing 1053)
        (Localization.AtPrime (P H).asIdeal))
        (rowIdeal rows))
  localizedReduced : ∀ H : Fin 4,
    IsReduced (Localization.AtPrime (P H).asIdeal ⧸
      Ideal.map (algebraMap (GermRing 1053)
        (Localization.AtPrime (P H).asIdeal))
        (rowIdeal rows))
  realBranchLocus : ∀ H : Fin 4,
    ∃ U : Set (Fin 62 → ℂ), U ∈ 𝓝 0 ∧
      (B H '' U) ∩ {y : Fin 1053 → ℂ | ∀ k, (y k).im = 0} =
        (fun x : Fin 62 → ℝ =>
          (fun k => ((NativePolynomial.PartialAction.pack
            (rawMap62 u.1 u.2 H (e x)) k : ℝ) : ℂ)) -
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


def realCoordinates : (Fin 62 → ℝ) ≃ₗ[ℝ] (ParamIndex → ℝ) where
  toFun x := x ∘ paramIndexEquiv
  invFun x := x ∘ paramIndexEquiv.symm
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem native_A6_witnesses (u : NativePhaseTorus) (hu : u ∈ nativeA6Locus) :
    ∃ (rows : Fin 2184 → MvPolynomial (Fin 1053) ℂ)
      (e : (Fin 62 → ℝ) ≃ₗ[ℝ] RawParam62)
      (B : Fin 4 → (Fin 62 → ℂ) → (Fin 1053 → ℂ))
      (ρ : Fin 4 → GermRing 1053 →ₐ[ℂ] GermRing 62)
      (P : Fin 4 → PrimeSpectrum (GermRing 1053)),
      (∀ x : Fin 1053 → ℝ, ∀ r, MvPolynomial.eval (fun j => (x j : ℂ)) (rows r) =
        (Option2.NativeStress.originalF (NativePolynomial.PartialAction.pack (literalCfg u.1) + x) r : ℂ)) ∧
      (∀ H, B H 0 = 0) ∧ (∀ H, Differentiable ℂ (B H)) ∧
      (∀ H, AnalyticAt ℂ (B H) 0) ∧
      (∀ H, ∀ x : Fin 62 → ℝ, B H (fun k => (x k : ℂ)) =
        (fun k => ((NativePolynomial.PartialAction.pack (rawMap62 u.1 u.2 H (e x)) k : ℝ) : ℂ)) -
          AnalyticDerivative.complexPack (literalCfg u.1)) ∧
      (∀ H f (hf : AnalyticAt ℂ f 0) (hc : AnalyticAt ℂ (f ∘ B H) 0),
        ρ H (ofAnalyticAt f hf) = ofAnalyticAt (f ∘ B H) hc) ∧
      A6Output u rows B ρ P e := by
  have hc (x : Fin 62 → ℝ) : realCoordinates x = fun j => x (paramIndexEquiv j) := rfl
  let e := realCoordinates.trans realParamEquiv
  refine ⟨nativeRows u.1, e, (fun H => branch H u.1 u.2),
    (fun H => branchPullback H u.1 u.2), nativeSheetPrime u.1 u.2,
    ?_, (fun H => branch_zero H u.1 u.2), ?_, ?_, ?_, ?_, ?_⟩
  · intro x r
    exact PhaseRealSheetIsolationA7.nativeRows_real_eval u.1 x r
  · intro H
    exact branch_entire H u.1 u.2
  · intro H
    exact branch_analyticAt H u.1 u.2
  · intro H x
    simpa only [e, LinearEquiv.trans_apply, realParamEquiv_apply, hc] using
      branch_real_parameters H u.1 u.2 x
  · intro H f hf hc
    exact AnalyticPullback.pullback_ofAnalyticAt _ _ _ f hf
  · have h := native_phase_A6 u hu
    refine ⟨(fun H => rfl), h.dimension, ?_, h.distinctPrimes,
      h.topPrimes, h.localizedIdeal, h.branchAlgebras, h.localizedField,
      h.localizedReduced, ?_, h.realSliceNormalForm⟩
    · simpa only [nativePhaseIntrinsicJetLength_eq, jetLength, rowIdeal, PhaseJetBoundA6.nativePhaseAnalyticIdeal] using h.ordinaryPolynomial
    · simpa only [e, LinearEquiv.trans_apply, realParamEquiv_apply, hc] using h.realBranchLocus
end Option2StatementA6Witness
#print axioms Option2StatementA6Witness.native_A6_witnesses

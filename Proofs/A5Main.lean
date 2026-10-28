module

public import A5Raw
public import A5AnchorF

@[expose] public section

/-!
# A5: the four actual fixed-quartet families and their common germ (endpoint bundle)

At every good phase `ξ₀` (`IsGoodPhase`: unit phases and all twelve signed anchor-phase cubes `≠ 1`,
equivalently all four resonance counts zero):

1. **Raw families.** For each anchor `H`, the eighteen-parameter model `preCfg ξ₀ H g h d` (quartet of
   `H` fixed, hidden matrices `c • g L E(d) R hᴴ`, original labels, signed native transport) satisfies
   all 2184 original equations for all `g, h ∈ SU(3)` and all phase triples, equals `P` at the base
   parameter, and has only the simultaneous central redundancy. Its `G`-saturation `rawMap` is
   analytic; its derivative kernel at the base point is exactly the eight-dimensional right gauge,
   whose group components are the pointwise fixer of the twelve quartet points; the complement
   `rawMap62` (`h = 1`) has injective derivative, so the derivative has rank 62.
2. **Common germ.** The `G`-saturation `commonMap` of the literal four-phase family satisfies the
   original equations, has injective 56-parameter derivative, and lies in every raw family germ
   through an analytic reparametrization (explicit quartet compensations).
3. **Slice germs.** The slice representatives `sliceFam H` (ten parameters) and `sliceCommon` (four)
   are analytic with injective derivatives, lie in the zero set, are pointwise fixed by the
   compensated anchor generators, and have tangent spaces exactly `Q^H` (dimension 10) and `Q^K`
   (dimension 4) of the compensated `K`-action on `Q = T ∩ N`.
4. **Simultaneous charts.** One analytic chart `ℝ⁴ × (ℝ⁶)⁴ × ℝ⁹⁷³ → N` (analytic inverse) maps the
   blocks `ℝ⁴ × ℝ⁶_H` onto the four slice family germs and `ℝ⁴` onto the common germ; one analytic
   chart `ℝ⁵⁶ × (ℝ⁶)⁴ × ℝ⁹⁷³ → Cfg` does the same for the raw germs (62 and 56). Distinct blocks meet
   exactly in the common block.
5. **Labelled quotient.** The slice germs are the raw germs intersected with the slice, and every raw
   family point near `P` is `G`-related to a point of its slice germ, inside the group/slice
   package's open embedding `sliceToOrbit` of slice germs into the orbit space.

Not claimed: exhaustion of real or complex solutions, multiplicities or components (A6, R), the code
consequence (A7), resonant phases, uniform radii, or a `K`-equivariant chart.
-/

noncomputable section

open CKM.NativeFirstOrder CKM.NativeGroupSlice CompactAlbert UnitaryErrorBases
open scoped Matrix Topology

namespace CKM.NativeFourFamily

/-- Clause 1: the four raw fixed-quartet families. -/
theorem native_raw_families {ξ₀ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ₀) (H : Fin 4) :
    (∀ {g h : Mat}, g ∈ Matrix.specialUnitaryGroup Index ℂ → h ∈ Matrix.specialUnitaryGroup Index ℂ →
      ∀ d, Option2.NativeStress.AnalyticDerivative.originalF (preCfg ξ₀ H g h d) = 0) ∧
    preCfg ξ₀ H 1 1 (anchorTriple ξ₀ hξ.1 H) = literalCfg ξ₀ ∧
    (∀ {g h g' h' : Mat}, g ∈ Matrix.specialUnitaryGroup Index ℂ →
      h ∈ Matrix.specialUnitaryGroup Index ℂ → g' ∈ Matrix.specialUnitaryGroup Index ℂ →
      h' ∈ Matrix.specialUnitaryGroup Index ℂ → ∀ d d',
      (preCfg ξ₀ H g h d = preCfg ξ₀ H g' h' d' ↔
        ∃ ζ : ℂ, ζ ^ 3 = 1 ∧ g' = ζ • g ∧ h' = ζ • h ∧ d' = d)) ∧
    (∀ p, Option2.NativeStress.AnalyticDerivative.originalF (rawMap ξ₀ hξ.1 H p) = 0) ∧
    AnalyticAt ℝ (rawMap ξ₀ hξ.1 H) 0 ∧
    HasStrictFDerivAt (rawMap ξ₀ hξ.1 H) (rawDer ξ₀ hξ.1 H) 0 ∧
    (∀ p, rawDer ξ₀ hξ.1 H p = orbitMapC ξ₀ (p.1 : CEnd) + preDer ξ₀ hξ.1 H p.2) ∧
    (∀ p, preDer ξ₀ hξ.1 H p = preVar ξ₀ hξ.1 H p) ∧
    Function.Injective (preDer ξ₀ hξ.1 H) ∧
    (∀ v, rawDer ξ₀ hξ.1 H v = 0 ↔ ∃ k, (v.1 : CEnd) = gaugeDer H k ∧ v.2 = (0, k, 0)) ∧
    Function.Injective (gaugeDer H) ∧
    Module.finrank ℝ ↥(LinearMap.ker (rawDer ξ₀ hξ.1 H : RawParam →ₗ[ℝ] Cfg)) = 8 ∧
    (∀ D : CEnd, D ∈ quartetFixer ξ₀ H ↔ ∃ v : RawParam, rawDer ξ₀ hξ.1 H v = 0 ∧ (v.1 : CEnd) = D) ∧
    Module.finrank ℝ ↥(quartetFixer ξ₀ H) = 8 ∧
    AnalyticAt ℝ (rawMap62 ξ₀ hξ.1 H) 0 ∧
    HasStrictFDerivAt (rawMap62 ξ₀ hξ.1 H) (rawDer62 ξ₀ hξ.1 H) 0 ∧
    Function.Injective (rawDer62 ξ₀ hξ.1 H) ∧
    Module.finrank ℝ ↥(LinearMap.range (rawDer ξ₀ hξ.1 H : RawParam →ₗ[ℝ] Cfg)) = 62 :=
  ⟨fun hg hh d => originalF_preCfg hξ.1 H hg hh d, preCfg_base hξ.1 H,
    fun hg hh hg' hh' d d' => preCfg_eq_iff hξ.1 H hg hh hg' hh' d d',
    originalF_rawMap hξ.1 H, analyticAt_rawMap hξ.1 H, hasStrictFDerivAt_rawMap hξ.1 H,
    rawDer_apply hξ.1 H, preDer_apply hξ.1 H, preDer_injective hξ.1 H, rawDer_eq_zero_iff hξ.1 H,
    gaugeDer_injective H, finrank_ker_rawDer hξ.1 H, quartetFixer_eq_ker_fst hξ.1 H,
    finrank_quartetFixer hξ.1 H, analyticAt_rawMap62 hξ.1 H, hasStrictFDerivAt_rawMap62 hξ.1 H,
    rawDer62_injective hξ.1 H, finrank_range_rawDer hξ.1 H⟩

/-- Clause 2: the common germ and its inclusion in every raw family. -/
theorem native_common_germ {ξ₀ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ₀) :
    (∀ p, Option2.NativeStress.AnalyticDerivative.originalF (commonMap ξ₀ p) = 0) ∧
    commonMap ξ₀ 0 = literalCfg ξ₀ ∧
    AnalyticAt ℝ (commonMap ξ₀) 0 ∧ HasStrictFDerivAt (commonMap ξ₀) (commonDer ξ₀) 0 ∧
    (∀ p, commonDer ξ₀ p = orbitMapC ξ₀ (p.1 : CEnd) + phaseDer ξ₀ p.2) ∧
    Function.Injective (commonDer ξ₀) ∧
    (∀ H, ∃ Γ : CommonParam → RawParam62, AnalyticAt ℝ Γ 0 ∧ Γ 0 = 0 ∧
      ∀ᶠ p in 𝓝 (0 : CommonParam), commonMap ξ₀ p = rawMap62 ξ₀ hξ.1 H (Γ p)) ∧
    (∀ H, IsGermSubset (commonMap ξ₀) 0 (rawMap62 ξ₀ hξ.1 H) 0) :=
  ⟨originalF_commonMap hξ.1, commonMap_zero hξ.1, analyticAt_commonMap hξ.1,
    hasStrictFDerivAt_commonMap hξ.1, commonDer_apply hξ.1, commonDer_injective hξ.1,
    exists_common_in_raw hξ.1, isGermSubset_common_raw hξ.1⟩

/-- Clause 3: the slice germs and their tangent identifications. -/
theorem native_slice_germs {ξ₀ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ₀) :
    sliceCommon ξ₀ hξ.1 0 = 0 ∧
    AnalyticAt ℝ (sliceCommon ξ₀ hξ.1) 0 ∧
    HasStrictFDerivAt (sliceCommon ξ₀ hξ.1) (sliceCommonDer ξ₀ hξ.1) 0 ∧
    Function.Injective (sliceCommonDer ξ₀ hξ.1) ∧
    (LinearMap.range (sliceCommonDer ξ₀ hξ.1 : (Fin 4 → ℝ) →ₗ[ℝ] ↥(normalC ξ₀))).map
      (normalC ξ₀).subtype = fixQK ξ₀ ∧
    Module.finrank ℝ ↥(fixQK ξ₀) = 4 ∧
    Module.finrank ℝ ↥(tanN ξ₀) = 28 ∧
    (∀ᶠ θ in 𝓝 (0 : Fin 4 → ℝ),
      Option2.NativeStress.AnalyticDerivative.originalF (literalCfg ξ₀ + ↑(sliceCommon ξ₀ hξ.1 θ)) = 0) ∧
    ∀ H : Fin 4,
      sliceFam ξ₀ hξ.1 H 0 = 0 ∧
      AnalyticAt ℝ (sliceFam ξ₀ hξ.1 H) 0 ∧
      HasStrictFDerivAt (sliceFam ξ₀ hξ.1 H) (sliceFamDer ξ₀ hξ.1 H) 0 ∧
      Function.Injective (sliceFamDer ξ₀ hξ.1 H) ∧
      (LinearMap.range (sliceFamDer ξ₀ hξ.1 H : SliceParam →ₗ[ℝ] ↥(normalC ξ₀))).map
        (normalC ξ₀).subtype = fixQ ξ₀ H ∧
      Module.finrank ℝ ↥(fixQ ξ₀ H) = 10 ∧
      (∀ᶠ p in 𝓝 (0 : SliceParam),
        Option2.NativeStress.AnalyticDerivative.originalF (literalCfg ξ₀ + ↑(sliceFam ξ₀ hξ.1 H p)) = 0) ∧
      (∀ᶠ p in 𝓝 (0 : SliceParam),
        kAct H (literalCfg ξ₀ + ↑(sliceFam ξ₀ hξ.1 H p)) = literalCfg ξ₀ + ↑(sliceFam ξ₀ hξ.1 H p)) ∧
      (∀ᶠ θ in 𝓝 (0 : Fin 4 → ℝ),
        kAct H (literalCfg ξ₀ + ↑(sliceCommon ξ₀ hξ.1 θ)) = literalCfg ξ₀ + ↑(sliceCommon ξ₀ hξ.1 θ)) ∧
      (∃ ψ : (Fin 4 → ℝ) → SliceParam, AnalyticAt ℝ ψ 0 ∧ ψ 0 = 0 ∧
        ∀ᶠ θ in 𝓝 (0 : Fin 4 → ℝ), sliceFam ξ₀ hξ.1 H (ψ θ) = sliceCommon ξ₀ hξ.1 θ) :=
  ⟨sliceCommon_zero hξ.1, analyticAt_sliceCommon hξ.1, hasStrictFDerivAt_sliceCommon hξ.1,
    sliceCommonDer_injective hξ.1, range_sliceCommonDer hξ, finrank_fixQK hξ, finrank_tanN hξ,
    eventually_originalF_sliceCommon hξ.1, fun H =>
    ⟨sliceFam_zero hξ.1 H, analyticAt_sliceFam hξ.1 H, hasStrictFDerivAt_sliceFam hξ.1 H,
      sliceFamDer_injective hξ.1 H, range_sliceFamDer hξ H, finrank_fixQ hξ H,
      eventually_originalF_sliceFam hξ.1 H, eventually_kAct_sliceFam hξ.1 H,
      eventually_kAct_sliceCommon hξ.1 H, exists_slice_inclusion hξ.1 H⟩⟩

/-- Clause 4: one simultaneous slice chart and one simultaneous raw chart. -/
theorem native_simultaneous_charts {ξ₀ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ₀) :
    (∃ Φ : OpenPartialHomeomorph SliceModel ↥(normalC ξ₀),
      (0 : SliceModel) ∈ Φ.source ∧ Φ 0 = 0 ∧
      AnalyticOnNhd ℝ Φ Φ.source ∧ AnalyticOnNhd ℝ Φ.symm Φ.target ∧
      IsGermImage (Φ '' (Φ.source ∩ commonBlock (Fin 4) (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ))) 0
        (sliceCommon ξ₀ hξ.1) 0 ∧
      (∀ H, IsGermImage (Φ '' (Φ.source ∩ familyBlock (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H)) 0
        (sliceFam ξ₀ hξ.1 H) 0) ∧
      (∀ H H', H ≠ H' →
        Φ '' (Φ.source ∩ familyBlock (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H) ∩
            Φ '' (Φ.source ∩ familyBlock (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H') =
          Φ '' (Φ.source ∩ commonBlock (Fin 4) (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ)))) ∧
    (∃ Φ : OpenPartialHomeomorph RawModel Cfg,
      (0 : RawModel) ∈ Φ.source ∧ Φ 0 = literalCfg ξ₀ ∧
      AnalyticOnNhd ℝ Φ Φ.source ∧ AnalyticOnNhd ℝ Φ.symm Φ.target ∧
      IsGermImage (Φ '' (Φ.source ∩ commonBlock (Fin 4) (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ)))
        (literalCfg ξ₀) (commonMap ξ₀) 0 ∧
      (∀ H, IsGermImage (Φ '' (Φ.source ∩ familyBlock (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H))
        (literalCfg ξ₀) (rawMap62 ξ₀ hξ.1 H) 0) ∧
      (∀ H, IsGermImage (Φ '' (Φ.source ∩ familyBlock (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H))
        (literalCfg ξ₀) (rawMap ξ₀ hξ.1 H) 0) ∧
      (∀ H H', H ≠ H' →
        Φ '' (Φ.source ∩ familyBlock (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H) ∩
            Φ '' (Φ.source ∩ familyBlock (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H') =
          Φ '' (Φ.source ∩ commonBlock (Fin 4) (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ)))) :=
  ⟨exists_slice_chart hξ, exists_raw_chart hξ⟩

/-- Clause 5: slice germs are raw germs cut by the slice, and the raw germs descend to them. -/
theorem native_labelled_quotient {ξ₀ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ₀) :
    (∃ V₀ ∈ 𝓝 (0 : CommonParam), ∀ U₀ ∈ 𝓝 (0 : CommonParam), U₀ ⊆ V₀ →
      IsGermImage (commonMap ξ₀ '' U₀ ∩ sliceSet ξ₀) (literalCfg ξ₀)
        (fun θ => literalCfg ξ₀ + ↑(sliceCommon ξ₀ hξ.1 θ)) 0) ∧
    (∃ W : Set Cfg, IsOpen W ∧ literalCfg ξ₀ ∈ W ∧ Topology.IsOpenEmbedding (sliceToOrbit ξ₀ W) ∧
      ∃ U₀ ∈ 𝓝 (0 : CommonParam), ∃ V₀ ∈ 𝓝 (0 : Fin 4 → ℝ),
        (∀ θ ∈ V₀, literalCfg ξ₀ + ↑(sliceCommon ξ₀ hξ.1 θ) ∈ W ∩ sliceSet ξ₀ ∩ zeroSet) ∧
        ∀ᶠ y in 𝓝 (literalCfg ξ₀), (y ∈ commonMap ξ₀ '' U₀ ↔
          ∃ θ ∈ V₀, ∃ A ∈ autC, actC A (literalCfg ξ₀ + ↑(sliceCommon ξ₀ hξ.1 θ)) = y)) ∧
    ∀ H : Fin 4,
      (∃ V₀ ∈ 𝓝 (0 : RawParam62), ∀ U₀ ∈ 𝓝 (0 : RawParam62), U₀ ⊆ V₀ →
        IsGermImage (rawMap62 ξ₀ hξ.1 H '' U₀ ∩ sliceSet ξ₀) (literalCfg ξ₀)
          (fun p => literalCfg ξ₀ + ↑(sliceFam ξ₀ hξ.1 H p)) 0) ∧
      (∃ W : Set Cfg, IsOpen W ∧ literalCfg ξ₀ ∈ W ∧ Topology.IsOpenEmbedding (sliceToOrbit ξ₀ W) ∧
        ∃ U₀ ∈ 𝓝 (0 : RawParam62), ∃ V₀ ∈ 𝓝 (0 : SliceParam),
          (∀ p ∈ V₀, literalCfg ξ₀ + ↑(sliceFam ξ₀ hξ.1 H p) ∈ W ∩ sliceSet ξ₀ ∩ zeroSet) ∧
          ∀ᶠ y in 𝓝 (literalCfg ξ₀), (y ∈ rawMap62 ξ₀ hξ.1 H '' U₀ ↔
            ∃ p ∈ V₀, ∃ A ∈ autC, actC A (literalCfg ξ₀ + ↑(sliceFam ξ₀ hξ.1 H p)) = y)) :=
  ⟨sliceCommon_germ_eq_raw_inter_slice hξ, common_descends hξ, fun H =>
    ⟨sliceFam_germ_eq_raw_inter_slice hξ H, rawFamily_descends hξ H⟩⟩

/-- The phase predicate: equivalent to vanishing resonance counts, nonempty, open in the torus. -/
theorem native_good_phases :
    (∀ ξ, IsGoodPhase ξ ↔ ∃ hξ : IsUnitPhase ξ, ∀ H, resonanceCount (anchorTriple ξ hξ H) = 0) ∧
    IsGoodPhase CKM.NativeGroupSliceConsumer.xiNonres ∧
    (∀ ξ₀, IsGoodPhase ξ₀ → ∃ V ∈ 𝓝 ξ₀, ∀ ξ ∈ V, IsUnitPhase ξ → IsGoodPhase ξ) ∧
    (∀ ξ₀, IsGoodPhase ξ₀ → ∀ᶠ θ in 𝓝 (0 : Fin 4 → ℝ), IsGoodPhase (commonPhase ξ₀ θ)) :=
  ⟨isGoodPhase_iff, isGoodPhase_xiNonres, fun _ h => exists_nhds_isGoodPhase h,
    fun _ h => eventually_isGoodPhase_commonPhase h⟩

end CKM.NativeFourFamily

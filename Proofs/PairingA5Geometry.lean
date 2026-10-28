module
public import PairingDefinitions
public import PairingA5Raw
public import NativeOrbitErrorTransfer
public import PairingResidual
@[expose] public section

noncomputable section
namespace Option2StatementA5
open NativePolynomial CKM.NativeTightCode CKM.NativeGroupSlice

theorem act_eq_native (g : Automorphism) (C : CodeCoords) :
    act g C = actC (autCEquiv.symm g).1 C := by
  funext i
  change upperCoordinates (g.1 (codePoint C i)) = coordEnd g.1.toLinearMap (C i)
  rw [coordEnd_apply]
  rfl

theorem saturation_eq_native (S : Set CodeCoords) :
    saturation S = CKM.NativeOrbitErrorTransfer.saturation S := by
  ext y
  simp only [saturation, CKM.NativeOrbitErrorTransfer.saturation, Set.mem_iUnion,
    Set.mem_image]
  constructor
  · rintro ⟨g, x, hx, hxy⟩
    exact ⟨autCEquiv.symm g, x, hx, (act_eq_native g x).symm.trans hxy⟩
  · rintro ⟨A, x, hx, hxy⟩
    refine ⟨autCEquiv A, x, hx, ?_⟩
    rw [act_eq_native, autCEquiv.symm_apply_apply]
    exact hxy

theorem nativeOrbit_eq_native (ξ : Fin 4 → ℂ) :
    nativeOrbit ξ = CKM.NativeOrbitErrorTransfer.nativeOrbit ξ :=
  saturation_eq_native _

theorem commonPhase_eq_native (ξ : Fin 4 → ℂ) (θ : Fin 4 → ℝ) :
    commonPhase ξ θ = CKM.NativeFourFamily.commonPhase ξ θ := rfl

#print axioms saturation_eq_native
end Option2StatementA5

/- Intrinsic trace-orthogonal slice and concrete slice families, parameterized
 by a product chart. The endpoint supplies that chart existentially with its
 exact forward formula; no chosen IFT implementation is part of the interface. -/
namespace Option2StatementA5Slice
open CKM.NativeFirstOrder Option2StatementA5Raw Option2StatementA5Anchor Option2StatementA5
open scoped BigOperators

end Option2StatementA5Slice

/- Geometric A5 target for the actual fixed maps. Chart witnesses are outputs,
 not hypotheses; the native product formula fixes the algebra completely. -/
namespace Option2StatementA5Slice
open CKM.NativeFirstOrder Option2StatementA5Raw Option2StatementA5Anchor Option2StatementA5
open Filter Topology

end Option2StatementA5Slice

namespace Option2StatementA5Slice
open CKM.NativeFirstOrder Option2StatementA5Raw Option2StatementA5Anchor Option2StatementA5
open Filter Topology

theorem native_A5_geometry {ξ : Fin 4 → ℂ} (hgood : CKM.NativeFourFamily.IsGoodPhase ξ) :
    ∃ m : Product, NativeProduct m ∧
      Module.finrank ℝ (derOf m) = 52 ∧
      Module.finrank ℝ (RawParam62 m) = 62 ∧ Module.finrank ℝ (CommonParam m) = 56 ∧
    ∃ σ : OpenPartialHomeomorph (derOf m × normal m ξ) Cfg,
      Module.finrank ℝ (normal m ξ) = 1001 ∧
      (0 : derOf m × normal m ξ) ∈ σ.source ∧ (∀ p, σ p = sliceChart m ξ p) ∧
      AnalyticAt ℝ σ 0 ∧ AnalyticAt ℝ σ.symm (literalCfg ξ) ∧
      (∀ H, AnalyticAt ℝ (rawMap62 m ξ hgood.1 H) 0 ∧
        Function.Injective (fderiv ℝ (rawMap62 m ξ hgood.1 H) 0) ∧
        ∀ p, Option2StatementResidual.originalF (rawMap62 m ξ hgood.1 H p) = 0) ∧
      (commonMap m ξ 0 = literalCfg ξ ∧ AnalyticAt ℝ (commonMap m ξ) 0 ∧
        Function.Injective (fderiv ℝ (commonMap m ξ) 0) ∧
        (∀ p, Option2StatementResidual.originalF (commonMap m ξ p) = 0) ∧
        ∀ H, ∃ Γ : CommonParam m → RawParam62 m, AnalyticAt ℝ Γ 0 ∧ Γ 0 = 0 ∧
          ∀ᶠ p in 𝓝 (0 : CommonParam m), commonMap m ξ p = rawMap62 m ξ hgood.1 H (Γ p)) ∧
      (sliceCommon σ 0 = 0 ∧ AnalyticAt ℝ (sliceCommon σ) 0 ∧
        Function.Injective (fderiv ℝ (sliceCommon σ) 0) ∧
        ∀ᶠ p in 𝓝 (0 : Fin 4 → ℝ),
          Option2StatementResidual.originalF (literalCfg ξ + ↑(sliceCommon σ p)) = 0) ∧
      (∀ H, sliceFam σ hgood.1 H 0 = 0 ∧ AnalyticAt ℝ (sliceFam σ hgood.1 H) 0 ∧
        Function.Injective (fderiv ℝ (sliceFam σ hgood.1 H) 0) ∧
        (∀ᶠ p in 𝓝 (0 : SliceParam),
          Option2StatementResidual.originalF (literalCfg ξ + ↑(sliceFam σ hgood.1 H p)) = 0) ∧
        ∃ ψ : (Fin 4 → ℝ) → SliceParam, AnalyticAt ℝ ψ 0 ∧ ψ 0 = 0 ∧
          ∀ᶠ p in 𝓝 (0 : Fin 4 → ℝ), sliceFam σ hgood.1 H (ψ p) = sliceCommon σ p) ∧
      Simultaneous m ξ hgood.1 σ ∧ GermCut m ξ hgood.1 σ ∧ GermDescent m ξ hgood.1 σ ∧
      LabelledSlice m ξ := by
  letI : Module.Free ℝ CKM.NativeGroupSlice.derC :=
    Module.Free.of_divisionRing ℝ CKM.NativeGroupSlice.derC
  have hf : Option2StatementResidual.originalF = Option2.NativeStress.AnalyticDerivative.originalF :=
    funext Option2StatementResidual.originalF_eq_native
  simp only [hf]
  refine ⟨CKM.NativeGroupSlice.prodC, CKM.NativeGroupSlice.prodC_eq_native,
    CKM.NativeGroupSlice.finrank_derC, ?_, ?_, CKM.NativeGroupSlice.slicePH ξ hgood.1,
    CKM.NativeGroupSlice.finrank_normalC ξ hgood.1,
    CKM.NativeGroupSlice.zero_mem_slicePH_source ξ hgood.1, (fun _ => rfl),
    CKM.NativeGroupSlice.analyticAt_sliceChart ξ 0,
    CKM.NativeGroupSlice.analyticAt_slicePH_symm ξ hgood.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Module.finrank ℝ (CKM.NativeGroupSlice.derC × (Fin 8 → ℝ) × (Fin 2 → ℝ)) = 62
    rw [Module.finrank_prod, Module.finrank_prod, CKM.NativeGroupSlice.finrank_derC,
      Module.finrank_fin_fun, Module.finrank_fin_fun]
  · change Module.finrank ℝ (CKM.NativeGroupSlice.derC × (Fin 4 → ℝ)) = 56
    rw [Module.finrank_prod, CKM.NativeGroupSlice.finrank_derC, Module.finrank_fin_fun]
  · intro H
    exact ⟨CKM.NativeFourFamily.analyticAt_rawMap62 hgood.1 H,
      CKM.NativeFourFamily.rawDer62_injective hgood.1 H,
      fun p => CKM.NativeFourFamily.originalF_rawMap hgood.1 H (p.1,p.2.1,0,p.2.2)⟩
  · exact ⟨CKM.NativeFourFamily.commonMap_zero hgood.1,
      CKM.NativeFourFamily.analyticAt_commonMap hgood.1,
      CKM.NativeFourFamily.commonDer_injective hgood.1,
      CKM.NativeFourFamily.originalF_commonMap hgood.1,
      CKM.NativeFourFamily.exists_common_in_raw hgood.1⟩
  · exact ⟨CKM.NativeFourFamily.sliceCommon_zero hgood.1,
      CKM.NativeFourFamily.analyticAt_sliceCommon hgood.1,
      CKM.NativeFourFamily.sliceCommonDer_injective hgood.1,
      CKM.NativeFourFamily.eventually_originalF_sliceCommon hgood.1⟩
  · intro H
    exact ⟨CKM.NativeFourFamily.sliceFam_zero hgood.1 H,
      CKM.NativeFourFamily.analyticAt_sliceFam hgood.1 H,
      CKM.NativeFourFamily.sliceFamDer_injective hgood.1 H,
      CKM.NativeFourFamily.eventually_originalF_sliceFam hgood.1 H,
      CKM.NativeFourFamily.exists_slice_inclusion hgood.1 H⟩
  · exact CKM.NativeFourFamily.native_simultaneous_charts hgood
  · exact ⟨CKM.NativeFourFamily.sliceCommon_germ_eq_raw_inter_slice hgood,
      CKM.NativeFourFamily.sliceFam_germ_eq_raw_inter_slice hgood⟩
  · constructor
    · obtain ⟨W,hW,hP,hemb,U,hU,V,hV,hmem,hgerm⟩ := CKM.NativeFourFamily.common_descends hgood
      refine ⟨U,hU,V,hV, ?_⟩
      filter_upwards [hgerm] with y hy
      rw [Option2StatementA5.saturation_eq_native, CKM.NativeOrbitErrorTransfer.mem_saturation]
      constructor
      · intro h
        obtain ⟨p,hp,A,hA,he⟩ := hy.mp h
        exact ⟨A,hA,_,⟨p,hp,rfl⟩,he⟩
      · rintro ⟨A,hA,x,⟨p,hp,rfl⟩,he⟩
        exact hy.mpr ⟨p,hp,A,hA,he⟩
    · intro H
      obtain ⟨W,hW,hP,hemb,U,hU,V,hV,hmem,hgerm⟩ := CKM.NativeFourFamily.rawFamily_descends hgood H
      refine ⟨U,hU,V,hV, ?_⟩
      filter_upwards [hgerm] with y hy
      rw [Option2StatementA5.saturation_eq_native, CKM.NativeOrbitErrorTransfer.mem_saturation]
      constructor
      · intro h
        obtain ⟨p,hp,A,hA,he⟩ := hy.mp h
        exact ⟨A,hA,_,⟨p,hp,rfl⟩,he⟩
      · rintro ⟨A,hA,x,⟨p,hp,rfl⟩,he⟩
        exact hy.mpr ⟨p,hp,A,hA,he⟩

  · unfold LabelledSlice
    rw [hf]
    refine ⟨CKM.NativeGroupSlice.orbitSetoid, ?_, ?_⟩
    · intro C D
      rw [Option2StatementA5.saturation_eq_native, CKM.NativeOrbitErrorTransfer.mem_saturation]
      simp only [Set.mem_singleton_iff, exists_eq_left]
      rfl
    · exact CKM.NativeGroupSlice.exists_sliceToOrbit_isOpenEmbedding ξ hgood.1

#print axioms native_A5_geometry
end Option2StatementA5Slice

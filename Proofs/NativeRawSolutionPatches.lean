module

public import NativePhaseRealSheetDensity
public import NativeUnlabelledDensePatches

@[expose] public section

/-! Genuine whole-solution open patches, accumulating at the native seed.
Their labelled quotient images are open and are covered by the actual selected
raw family. This closes the distinction between family-open and solution-open;
it does not yet identify those quotient patches with Euclidean ten-space.
 -/

noncomputable section
namespace Option2.NativeStress.RawSolutionPatchesA7
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeUnlabelledSlice NativePolynomial
open PhasePivotA6 PhasePivotLocusA6 PhaseAnalyticBranchesA6
open PhaseEntireFamilyA6 PhaseBranchDerivativeA6
open PhaseRealSheetIsolationA7 PhaseRealSheetDensityA7
open Filter
open scoped Topology

private theorem pack_injective : Function.Injective (PartialAction.pack (S := ℝ)) := by
  intro C D h
  funext i j
  simpa only [PartialAction.pack_variableIndex] using
    congrFun h (ConfigurationResiduals.variableIndex i j)

def rawPoint (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4)
    (a : Fin 62 → ℝ) : Cfg :=
  rawMap62 ξ hξ H (realParam (fun j => a (paramIndexEquiv j)))

theorem rawPoint_zero (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    rawPoint ξ hξ H 0 = literalCfg ξ := by
  have hp : realParam (fun j => (0 : Fin 62 → ℝ) (paramIndexEquiv j)) = 0 := by
    rw [← realParamEquiv_apply]
    exact realParamEquiv.map_zero
  change actC (groupChart _) (preMap ξ hξ H _) = _
  rw [hp]
  change actC (groupChart 0) (preMap ξ hξ H (0,0,0)) = _
  rw [groupChart_zero,actC_one]
  change preMap ξ hξ H 0 = literalCfg ξ
  exact preMap_zero hξ H

theorem continuousAt_rawPoint_zero (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    ContinuousAt (rawPoint ξ hξ H) 0 := by
  have hp : Continuous (fun a : Fin 62 → ℝ => realParam (fun j => a (paramIndexEquiv j))) := by
    simp_rw [← realParamEquiv_apply]
    have he : Continuous (fun x : ParamIndex → ℝ => realParamEquiv x) :=
      realParamCLM.continuous
    exact he.comp (continuous_pi fun j => continuous_apply (paramIndexEquiv j))
  have hp0 : realParam (fun j => (0 : Fin 62 → ℝ) (paramIndexEquiv j)) = 0 := by
    rw [← realParamEquiv_apply]
    exact realParamEquiv.map_zero
  exact (analyticAt_rawMap62 hξ H).continuousAt.comp_of_eq hp.continuousAt hp0

theorem rawPoint_mem_zeroSet (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4)
    (a : Fin 62 → ℝ) : rawPoint ξ hξ H a ∈ zeroSet := by
  have he : PartialAction.pack (rawPoint ξ hξ H a) =
      PartialAction.pack (literalCfg ξ) + nativeRealBranch H ξ hξ a := by
    simp only [nativeRealBranch,rawPoint,add_sub_cancel]
  change Option2.NativeStress.originalF (PartialAction.pack (rawPoint ξ hξ H a)) = 0
  rw [he]
  apply (nativeComplexZero_real_iff ξ _).1
  rw [nativeRealBranch_complex]
  exact fun r => branch_original_rows H ξ hξ r _

/-- The labelled orbit quotient map is open on the entire native zero set. -/
theorem isOpenMap_labelledOrbitMk : IsOpenMap (Quotient.mk orbitSetoid) := by
  intro U hU
  apply (isQuotientMap_quotient_mk' (s := orbitSetoid)).isOpen_preimage.1
  change IsOpen (Quotient.mk orbitSetoid ⁻¹' (Quotient.mk orbitSetoid '' U))
  have hs : Quotient.mk orbitSetoid ⁻¹' (Quotient.mk orbitSetoid '' U) =
      ⋃ g : autGroup, zeroAct ((g,1) : Big) ⁻¹' U := by
    ext s
    constructor
    · rintro ⟨t,ht,he⟩
      obtain ⟨A,hA,hAt⟩ := Quotient.exact he
      rw [← range_autVal] at hA
      obtain ⟨g,rfl⟩ := hA
      refine Set.mem_iUnion.2 ⟨g⁻¹,?_⟩
      have he' : zeroAct ((g⁻¹,1) : Big) s = t := by
        apply Subtype.ext
        have ht' : ((g,1) : Big) • (t : Cfg) = (s : Cfg) := hAt
        change ((g⁻¹,1) : Big) • (s : Cfg) = (t : Cfg)
        rw [← ht']
        exact inv_smul_smul ((g,1) : Big) (t : Cfg)
      rwa [Set.mem_preimage,he']
    · intro hs
      obtain ⟨g,hg⟩ := Set.mem_iUnion.1 hs
      refine ⟨zeroAct ((g,1) : Big) s,hg,Quotient.sound ?_⟩
      refine ⟨autVal g⁻¹,autVal_mem _,?_⟩
      exact inv_smul_smul ((g,1) : Big) (s : Cfg)
  rw [hs]
  apply isOpen_iUnion
  intro g
  exact hU.preimage (((continuous_const_smul ((g,1) : Big)).comp
    continuous_subtype_val).subtype_mk _)

/-- Every ambient neighborhood of the good seed contains a nonempty open
piece of the WHOLE original solution set contained in the actual raw family. -/
theorem native_open_solution_patches (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) (H : Fin 4)
    {N : Set Cfg} (hN : N ∈ 𝓝 (literalCfg u.1)) :
    ∃ O : Set Cfg, IsOpen O ∧ O ⊆ N ∧
      (O ∩ zeroSet).Nonempty ∧ O ∩ zeroSet ⊆ Set.range (rawPoint u.1 hgood.1 H) := by
  obtain ⟨κ,hκ,r,hr,_,hdense,P,_,V,hV,h0V,hball,hiso⟩ :=
    native_real_sheet_isolation_dense_parameters u hgood hpivot H
  obtain ⟨b,hb,hκb⟩ := hκ.exists_ball_analyticOnNhd
  obtain ⟨N₀,hN₀sub,hN₀,h0N₀⟩ := mem_nhds_iff.1 hN
  let d : Cfg → (Fin 1053 → ℝ) := fun C => PartialAction.pack C - PartialAction.pack (literalCfg u.1)
  have hd : Continuous d := packCLM.continuous.sub continuous_const
  have hd0 : d (literalCfg u.1) = 0 := sub_self _
  let c : Cfg → (Fin 1053 → ℂ) := fun C j => (d C j : ℂ)
  have hc : Continuous c := continuous_pi fun j =>
    Complex.continuous_ofReal.comp ((continuous_apply j).comp hd)
  have hc0 : c (literalCfg u.1) = 0 := by
    funext j
    simp [c,hd0]
  let W : Set Cfg := N₀ ∩ d ⁻¹' V ∩ c ⁻¹' Metric.ball 0 b
  have hW : IsOpen W := (hN₀.inter (hV.preimage hd)).inter (Metric.isOpen_ball.preimage hc)
  have h0W : literalCfg u.1 ∈ W := ⟨⟨h0N₀,by change d (literalCfg u.1) ∈ V; rwa [hd0]⟩,
    by change c (literalCfg u.1) ∈ Metric.ball 0 b; simpa [hc0] using hb⟩
  let O : Set Cfg := {C | C ∈ W ∧ κ (c C) ≠ 0}
  have hO : IsOpen O := by
    apply isOpen_iff_mem_nhds.2
    intro C hC
    exact inter_mem (hW.mem_nhds hC.1)
      (((hκb _ hC.1.2).continuousAt.comp hc.continuousAt).preimage_mem_nhds
        (isOpen_compl_singleton.mem_nhds hC.2))
  have hparam : rawPoint u.1 hgood.1 H ⁻¹' W ∈ 𝓝 0 := by
    apply (continuousAt_rawPoint_zero u.1 hgood.1 H).preimage_mem_nhds
    rw [rawPoint_zero]
    exact hW.mem_nhds h0W
  have hzclosure := hdense (Metric.mem_ball_self hr)
  obtain ⟨a,haW,haB,hak⟩ := (mem_closure_iff_nhds.1 hzclosure) _ hparam
  have hda : d (rawPoint u.1 hgood.1 H a) = nativeRealBranch H u.1 hgood.1 a := rfl
  have haO : rawPoint u.1 hgood.1 H a ∈ O := by
    exact ⟨haW,by simpa only [c,hda] using hak⟩
  refine ⟨O,hO,fun C hC => hN₀sub hC.1.1.1,
    ⟨rawPoint u.1 hgood.1 H a,haO,rawPoint_mem_zeroSet u.1 hgood.1 H a⟩,?_⟩
  intro C hC
  have hz : Option2.NativeStress.originalF (PartialAction.pack (literalCfg u.1) + d C) = 0 := by
    have he : PartialAction.pack (literalCfg u.1) + d C = PartialAction.pack C := by
      dsimp [d]
      abel
    rw [he]
    exact hC.2
  obtain ⟨a,_,ha⟩ := (hiso (d C) hC.1.1.1.2 hC.1.2).1 hz
  refine ⟨a,pack_injective ?_⟩
  change PartialAction.pack (rawPoint u.1 hgood.1 H a) = PartialAction.pack C
  have he : PartialAction.pack C - PartialAction.pack (literalCfg u.1) =
      PartialAction.pack (rawPoint u.1 hgood.1 H a) - PartialAction.pack (literalCfg u.1) := ha
  exact (sub_left_injective he).symm

/-- Genuine open labelled quotient patches accumulate at the native orbit;
every point in each patch is represented by the selected actual raw family. -/
theorem native_open_labelled_quotient_patches (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) (H : Fin 4)
    {N : Set OrbitSpace} (hN : IsOpen N)
    (hseed : Quotient.mk orbitSetoid (basePt u.1 hgood.1) ∈ N) :
    ∃ Q : Set OrbitSpace, IsOpen Q ∧ Q.Nonempty ∧ Q ⊆ N ∧
      ∀ q ∈ Q, ∃ a : Fin 62 → ℝ,
        Quotient.mk orbitSetoid ⟨rawPoint u.1 hgood.1 H a,
          rawPoint_mem_zeroSet u.1 hgood.1 H a⟩ = q := by
  have hpre : IsOpen (Quotient.mk orbitSetoid ⁻¹' N) := hN.preimage continuous_quot_mk
  obtain ⟨A,hA,hAeq⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.1 hpre
  have hseedA : literalCfg u.1 ∈ A := by
    change (basePt u.1 hgood.1 : Cfg) ∈ A
    rw [← Set.mem_preimage,hAeq]
    exact hseed
  obtain ⟨O,hO,hOA,⟨C,hCO,hCZ⟩,hfamily⟩ :=
    native_open_solution_patches u hgood hpivot H (hA.mem_nhds hseedA)
  let S : Set zeroSet := Subtype.val ⁻¹' O
  refine ⟨Quotient.mk orbitSetoid '' S,
    isOpenMap_labelledOrbitMk S (hO.preimage continuous_subtype_val),
    ⟨Quotient.mk orbitSetoid ⟨C,hCZ⟩,⟨⟨C,hCZ⟩,hCO,rfl⟩⟩,?_,?_⟩
  · rintro q ⟨C,hC,rfl⟩
    change C ∈ Quotient.mk orbitSetoid ⁻¹' N
    rw [← hAeq]
    exact hOA hC
  · rintro q ⟨C,hC,rfl⟩
    obtain ⟨a,ha⟩ := hfamily ⟨hC,C.2⟩
    refine ⟨a,?_⟩
    congr 1
    exact Subtype.ext ha

#print axioms native_open_solution_patches
#print axioms native_open_labelled_quotient_patches
end Option2.NativeStress.RawSolutionPatchesA7

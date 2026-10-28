module

public import NativeRawSolutionPatches
public import NativePhaseRealSheetDensityWithin

@[expose] public section

/-! Actual whole-zero open patches with prescribed small parameter domain.
No Euclidean-dimension conclusion is made here. -/

noncomputable section
namespace Option2.NativeStress.RawSolutionPatchesWithinA7
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeUnlabelledSlice NativePolynomial
open PhasePivotA6 PhasePivotLocusA6 PhaseAnalyticBranchesA6
open PhaseEntireFamilyA6 PhaseBranchDerivativeA6
open PhaseRealSheetIsolationA7 PhaseRealSheetDensityA7
open RawSolutionPatchesA7 PhaseRealSheetDensityWithinA7
open Filter
open scoped Topology

/-- Every ambient neighborhood of the good seed contains a nonempty open
piece of the WHOLE original solution set contained in the actual raw family. -/
theorem native_open_solution_patches_within (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) (H : Fin 4)
    (A : Set (Fin 62 → ℝ)) (hA : A ∈ 𝓝 0)
    {N : Set Cfg} (hN : N ∈ 𝓝 (literalCfg u.1)) :
    ∃ O : Set Cfg, IsOpen O ∧ O ⊆ N ∧
      (O ∩ zeroSet).Nonempty ∧ O ∩ zeroSet ⊆ rawPoint u.1 hgood.1 H '' A := by
  obtain ⟨κ,hκ,r,hr,_,hdense,P,_,hPA,V,hV,h0V,hball,hiso⟩ :=
    native_real_sheet_isolation_dense_parameters_within u hgood hpivot H A hA
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
  obtain ⟨a,haP,ha⟩ := (hiso (d C) hC.1.1.1.2 hC.1.2).1 hz
  refine ⟨a,by simpa only [Complex.ofReal_re] using hPA _ haP,?_⟩
  apply (show Function.Injective (PartialAction.pack (S := ℝ)) from fun C D h => by
    funext i j
    simpa only [PartialAction.pack_variableIndex] using
      congrFun h (ConfigurationResiduals.variableIndex i j))
  change PartialAction.pack (rawPoint u.1 hgood.1 H a) = PartialAction.pack C
  have he : PartialAction.pack C - PartialAction.pack (literalCfg u.1) =
      PartialAction.pack (rawPoint u.1 hgood.1 H a) - PartialAction.pack (literalCfg u.1) := ha
  exact (sub_left_injective he).symm


/-- Small-domain form matched to the accepted A5 RawParam62 germ API. -/
theorem native_open_raw_germ_patches (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) (H : Fin 4)
    (B : Set RawParam62) (hB : B ∈ 𝓝 0)
    {N : Set Cfg} (hN : N ∈ 𝓝 (literalCfg u.1)) :
    ∃ O : Set Cfg, IsOpen O ∧ O ⊆ N ∧
      (O ∩ zeroSet).Nonempty ∧ O ∩ zeroSet ⊆ rawMap62 u.1 hgood.1 H '' B := by
  let p : (Fin 62 → ℝ) → RawParam62 :=
    fun a => realParam (fun j => a (paramIndexEquiv j))
  have hp : Continuous p := by
    have he : Continuous (fun x : ParamIndex → ℝ => realParamEquiv x) :=
      realParamCLM.continuous
    have hc : Continuous (fun a : Fin 62 → ℝ => fun j : ParamIndex => a (paramIndexEquiv j)) :=
      continuous_pi fun j => continuous_apply (paramIndexEquiv j)
    simpa only [p,Function.comp_def,realParamEquiv_apply] using he.comp hc
  have hp0 : p 0 = 0 := by
    change realParam (fun _ => 0) = 0
    rw [← realParamEquiv_apply]
    exact realParamEquiv.map_zero
  have hA : p ⁻¹' B ∈ 𝓝 0 :=
    hp.continuousAt.preimage_mem_nhds (by rwa [hp0])
  obtain ⟨O,hO,hON,hne,hsub⟩ :=
    native_open_solution_patches_within u hgood hpivot H (p ⁻¹' B) hA hN
  refine ⟨O,hO,hON,hne,?_⟩
  intro C hC
  obtain ⟨a,ha,rfl⟩ := hsub hC
  exact ⟨p a,ha,rfl⟩

#print axioms native_open_solution_patches_within
#print axioms native_open_raw_germ_patches
end Option2.NativeStress.RawSolutionPatchesWithinA7

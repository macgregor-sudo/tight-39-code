module

public import NativeSliceChartTransport

@[expose] public section

/-! Project actual open raw solution pieces through the native group/slice
product chart. The resulting ambient-open normal-slice patches have their whole
original zero set exactly equal to the A5 ten-dimensional family block.
 -/

noncomputable section
namespace Option2.NativeStress.SliceChartIsolationA7
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open PhasePivotA6 PhasePivotLocusA6 RawSolutionPatchesWithinA7 SliceChartTransportA7
open Filter
open scoped Topology

def normalZero (ξ : Fin 4 → ℂ) : Set ↥(normalC ξ) :=
  {n | literalCfg ξ + (n : Cfg) ∈ zeroSet}

theorem native_open_slice_chart_patches (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) (H : Fin 4) :
    ∃ Φ : OpenPartialHomeomorph SliceModel ↥(normalC u.1),
      (0 : SliceModel) ∈ Φ.source ∧ Φ 0 = 0 ∧
      AnalyticOnNhd ℝ Φ Φ.source ∧ AnalyticOnNhd ℝ Φ.symm Φ.target ∧
      ∀ N ∈ 𝓝 (0 : ↥(normalC u.1)), ∃ V : Set ↥(normalC u.1),
        IsOpen V ∧ V ⊆ N ∧ V ⊆ Φ.target ∧ (V ∩ normalZero u.1).Nonempty ∧
        V ∩ normalZero u.1 = V ∩ (Φ '' (Φ.source ∩
          familyBlock (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H)) := by
  obtain ⟨Φ,h0Φ,hΦ0,hΦ,hΦi,_,hfam,_⟩ := exists_slice_chart hgood
  let M := Φ '' (Φ.source ∩ familyBlock (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H)
  have hM : IsGermImage M 0 (sliceFam u.1 hgood.1 H) 0 := hfam H
  obtain ⟨B,hB,hcover⟩ := native_raw_to_slice_block hgood.1 H hM
  have hzero : ∀ᶠ n in 𝓝 (0 : ↥(normalC u.1)), n ∈ M → n ∈ normalZero u.1 := by
    obtain ⟨U,hU,hg⟩ := hM
    let U' := U ∩ {p | literalCfg u.1 + (sliceFam u.1 hgood.1 H p : Cfg) ∈ zeroSet}
    have hU' : U' ∈ 𝓝 0 := inter_mem hU (eventually_originalF_sliceFam hgood.1 H)
    have he := hg U' hU' Set.inter_subset_left
    rw [eventuallyEqSet_iff] at he
    filter_upwards [he] with n hn hnm
    obtain ⟨p,hp,rfl⟩ := hn.2 hnm
    exact hp.2
  have hrep : Tendsto (sliceRep u.1 hgood.1) (𝓝 (literalCfg u.1)) (𝓝 0) := by
    have ht := (continuous_snd.continuousAt.comp
      ((slicePH u.1 hgood.1).continuousAt_symm
        (literalCfg_mem_slicePH_target u.1 hgood.1))).tendsto
    rw [Function.comp_apply,slicePH_symm_literalCfg] at ht
    exact ht
  have htarget : Φ.target ∈ 𝓝 (0 : ↥(normalC u.1)) := by
    rw [← hΦ0]
    exact Φ.open_target.mem_nhds (Φ.map_source h0Φ)
  refine ⟨Φ,h0Φ,hΦ0,hΦ,hΦi,?_⟩
  intro N hN
  let T := slicePH u.1 hgood.1
  have hT : T.target ∈ 𝓝 (literalCfg u.1) :=
    T.open_target.mem_nhds (literalCfg_mem_slicePH_target u.1 hgood.1)
  have hsmall : {y | y ∈ T.target ∧ sliceRep u.1 hgood.1 y ∈ N ∧
      sliceRep u.1 hgood.1 y ∈ Φ.target ∧
      (sliceRep u.1 hgood.1 y ∈ M → sliceRep u.1 hgood.1 y ∈ normalZero u.1) ∧
      (y ∈ rawMap62 u.1 hgood.1 H '' B → sliceRep u.1 hgood.1 y ∈ M)} ∈
      𝓝 (literalCfg u.1) :=
    inter_mem hT (inter_mem (hrep.eventually_mem hN)
      (inter_mem (hrep.eventually_mem htarget) (inter_mem (hrep.eventually hzero) hcover)))
  obtain ⟨O,hO,hsub,⟨y,hyO,hyZ⟩,hraw⟩ :=
    native_open_raw_germ_patches u hgood hpivot H B hB hsmall
  let V := Prod.snd '' (T.source ∩ T ⁻¹' O)
  have hV : IsOpen V := isOpenMap_snd _ (T.isOpen_inter_preimage hO)
  have hrepT : ∀ p ∈ T.source, sliceRep u.1 hgood.1 (T p) = p.2 := by
    intro p hp
    exact congrArg Prod.snd (T.left_inv hp)
  have hinfo : ∀ n ∈ V, n ∈ N ∧ n ∈ Φ.target ∧ (n ∈ M → n ∈ normalZero u.1) := by
    rintro n ⟨p,⟨hp,hpO⟩,rfl⟩
    have hi := hsub hpO
    simp only [Set.mem_ofPred_eq] at hi
    rw [hrepT p hp] at hi
    exact ⟨hi.2.1,hi.2.2.1,hi.2.2.2.1⟩
  have hyT : y ∈ T.target := (hsub hyO).1
  have hnV : (T.symm y).2 ∈ V :=
    ⟨T.symm y,⟨T.map_target hyT,by change T (T.symm y) ∈ O; rwa [T.right_inv hyT]⟩,rfl⟩
  have hnZ : (T.symm y).2 ∈ normalZero u.1 := by
    apply (originalF_sliceChart_eq_zero_iff u.1 (T.symm y)).1
    change Option2.NativeStress.AnalyticDerivative.originalF (T (T.symm y)) = 0
    rw [T.right_inv hyT]
    exact hyZ
  refine ⟨V,hV,fun n hn => (hinfo n hn).1,fun n hn => (hinfo n hn).2.1,
    ⟨(T.symm y).2,hnV,hnZ⟩,?_⟩
  ext n
  constructor
  · rintro ⟨hn,hnz⟩
    obtain ⟨p,⟨hp,hpO⟩,rfl⟩ := hn
    have hpz : T p ∈ zeroSet := (originalF_sliceChart_eq_zero_iff u.1 p).2 hnz
    have hi := (hsub hpO).2.2.2.2 (hraw ⟨hpO,hpz⟩)
    rw [hrepT p hp] at hi
    exact ⟨⟨p,⟨hp,hpO⟩,rfl⟩,hi⟩
  · rintro ⟨hn,hm⟩
    exact ⟨hn,(hinfo n hn).2.2 hm⟩

#print axioms native_open_slice_chart_patches
end Option2.NativeStress.SliceChartIsolationA7

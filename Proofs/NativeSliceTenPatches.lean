module

public import NativeTenBlockPatch

@[expose] public section

/-! Transfer actual normal-zero charts to the native zero-slice used by the
finite unlabelled quotient.  -/
noncomputable section
namespace Option2.NativeStress.SliceTenPatchesA7
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeUnlabelledSlice
open PhasePivotA6 PhasePivotLocusA6 SliceChartIsolationA7 TenBlockPatchA7
open Filter
open scoped Topology

def sliceNormal (ξ : Fin 4 → ℂ) (W : Set Cfg) (s : sliceGerm ξ W) : ↥(normalC ξ) :=
  ⟨(s.1 : Cfg) - literalCfg ξ,s.2.2⟩

theorem continuous_sliceNormal (ξ : Fin 4 → ℂ) (W : Set Cfg) :
    Continuous (sliceNormal ξ W) :=
  ((continuous_subtype_val.comp continuous_subtype_val).sub continuous_const).subtype_mk _

/-- Affine identification with the actual nested zero-slice subtype. -/
def normalPatchHomeo {ξ : Fin 4 → ℂ} {W : Set Cfg}
    (V : Set ↥(normalC ξ)) (hVW : ∀ n ∈ V, literalCfg ξ + (n : Cfg) ∈ W) :
    ↥(V ∩ normalZero ξ) ≃ₜ ↥(sliceNormal ξ W ⁻¹' V) :=
  { toFun := fun n => ⟨⟨⟨literalCfg ξ + (n.1 : Cfg),n.2.2⟩,
        hVW n n.2.1,by
          change literalCfg ξ + (n.1 : Cfg) - literalCfg ξ ∈ normalC ξ
          simpa only [add_sub_cancel_left] using n.1.2⟩,
        by
          change (⟨literalCfg ξ + (n.1 : Cfg) - literalCfg ξ,_⟩ : ↥(normalC ξ)) ∈ V
          simpa only [add_sub_cancel_left] using n.2.1⟩
    invFun := fun s => ⟨sliceNormal ξ W s.1,s.2,by
      change literalCfg ξ + ((s.1.1 : Cfg) - literalCfg ξ) ∈ zeroSet
      simpa only [add_sub_cancel] using s.1.1.2⟩
    left_inv := fun n => Subtype.ext (Subtype.ext (add_sub_cancel_left _ _))
    right_inv := fun s => Subtype.ext (Subtype.ext (Subtype.ext (add_sub_cancel _ _)))
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_const.add (continuous_subtype_val.comp continuous_subtype_val)
    continuous_invFun := ((continuous_sliceNormal ξ W).comp continuous_subtype_val).subtype_mk _ }

/-- Every native zero-slice neighborhood of the seed contains a genuine
open ten-parameter patch. No quotient or dimension inference occurs here. -/
theorem native_slice_ten_patches (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus)
    {W : Set Cfg} (hW : IsOpen W) (hseed : literalCfg u.1 ∈ W)
    {N : Set (sliceGerm u.1 W)} (hN : IsOpen N)
    (h0N : (⟨basePt u.1 hgood.1, hseed,by change literalCfg u.1 - literalCfg u.1 ∈ normalC u.1; simp⟩ : sliceGerm u.1 W) ∈ N) :
    ∃ U : Set TenParam, IsOpen U ∧ U.Nonempty ∧
      ∃ Q : Set (sliceGerm u.1 W), IsOpen Q ∧ Q ⊆ N ∧ Nonempty (U ≃ₜ Q) := by
  let V₀ : Set ↥(normalC u.1) := {n | literalCfg u.1 + (n : Cfg) ∈ W}
  have hV₀ : IsOpen V₀ := hW.preimage (continuous_const.add continuous_subtype_val)
  have h0V₀ : (0 : ↥(normalC u.1)) ∈ V₀ := by simpa [V₀] using hseed
  let e₀ := normalPatchHomeo V₀ (fun _ h => h)
  let n₀ : ↥(V₀ ∩ normalZero u.1) := ⟨0,h0V₀,by
    change AnalyticDerivative.originalF (literalCfg u.1 + (0 : Cfg)) = 0
    simpa only [add_zero] using originalF_literalCfg u.1 hgood.1⟩
  have hopen : IsOpen ((fun n : ↥(V₀ ∩ normalZero u.1) => (e₀ n).1) ⁻¹' N) :=
    hN.preimage (continuous_subtype_val.comp e₀.continuous)
  obtain ⟨A,hA,hAe⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.1 hopen
  have h0A : (0 : ↥(normalC u.1)) ∈ A := by
    change (n₀ : ↥(normalC u.1)) ∈ A
    rw [← Set.mem_preimage,hAe]
    change (e₀ n₀).1 ∈ N
    convert h0N using 1
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    exact add_zero _
  obtain ⟨Φ,_,_,_,_,hpatch⟩ := native_open_slice_chart_patches u hgood hpivot 0
  obtain ⟨V,hV,hVsub,hVT,hne,heq⟩ := hpatch (A ∩ V₀)
    ((hA.inter hV₀).mem_nhds ⟨h0A,h0V₀⟩)
  obtain ⟨U,hU,hUn,⟨e⟩⟩ := ten_block_patch 0 Φ V hV hVT hne heq
  let Q := sliceNormal u.1 W ⁻¹' V
  have hQ : IsOpen Q := hV.preimage (continuous_sliceNormal u.1 W)
  let ev := normalPatchHomeo V (fun n hn => (hVsub hn).2)
  refine ⟨U,hU,hUn,Q,hQ,?_,⟨e.trans ev⟩⟩
  intro s hs
  let n : ↥(V₀ ∩ normalZero u.1) := ⟨sliceNormal u.1 W s,(hVsub hs).2,by
    change literalCfg u.1 + ((s.1 : Cfg) - literalCfg u.1) ∈ zeroSet
    simpa only [add_sub_cancel] using s.1.2⟩
  have hnA : (n : ↥(normalC u.1)) ∈ A := (hVsub hs).1
  have hnN : (e₀ n).1 ∈ N := by
    change n ∈ (fun n => (e₀ n).1) ⁻¹' N
    rw [← hAe]
    exact hnA
  have he : (e₀ n).1 = s := by
    apply Subtype.ext
    apply Subtype.ext
    exact add_sub_cancel _ _
  rwa [he] at hnN

#print axioms native_slice_ten_patches
end Option2.NativeStress.SliceTenPatchesA7

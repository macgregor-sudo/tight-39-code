module

public import NativeSliceTenPatches
public import GPCode

@[expose] public section

/-! Actual ten-dimensional open patches in CodeModuli, using whole-zero slice
charts and the proved dense locus of locally constant finite stabilizers.
 -/
noncomputable section
namespace Option2.NativeStress.NativeCodeTenPatchesA7
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeUnlabelledSlice CKM.NativeGoodPhase
open PhasePivotA6 PhasePivotLocusA6 SliceTenPatchesA7 TenBlockPatchA7
open Filter
open scoped Topology

/-- Native code patches in the explicit ten-parameter model. -/
theorem native_code_ten_param_patches (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus)
    {N : Set CodeModuli} (hN : IsOpen N) (hseed : codeClass u ∈ N) :
    ∃ P : Set TenParam, IsOpen P ∧ P.Nonempty ∧
      ∃ Q : Set CodeModuli, IsOpen Q ∧ Q ⊆ N ∧ Nonempty (P ≃ₜ Q) := by
  obtain ⟨W,hW,hPW,hInv,_,hemb,_⟩ := exists_sliceQuot_isOpenEmbedding u.1 hgood.1
  let c : sliceGerm u.1 W → CodeModuli := fun s =>
    unlabelledToCode (Quotient.mk bigSetoid (s : zeroSet))
  have hc : Continuous c := unlabelledHomeo.continuous.comp
    (continuous_quot_mk.comp continuous_subtype_val)
  have h0 : (⟨basePt u.1 hgood.1,hPW,by
      change literalCfg u.1 - literalCfg u.1 ∈ normalC u.1; simp⟩ : sliceGerm u.1 W) ∈ c ⁻¹' N :=
    hseed
  obtain ⟨U,hU,hUn,S,hS,hSN,⟨e⟩⟩ :=
    native_slice_ten_patches u hgood hpivot hW hPW (hN.preimage hc) h0
  have hSn : S.Nonempty := by
    obtain ⟨a,ha⟩ := hUn
    exact ⟨e ⟨a,ha⟩,(e ⟨a,ha⟩).2⟩
  obtain ⟨p,hpS,hpD⟩ :=
    (isOpen_dense_nativeRegularStabilizerLocus hgood.1 hInv).2.inter_open_nonempty S hS hSn
  obtain ⟨V,hV,hVS,hfix⟩ := exists_pointwise_stabilizer_nhds hgood.1 hInv hpD (hS.mem_nhds hpS)
  obtain ⟨A,hA,hpA,hAV,hAe⟩ := exists_open_unlabelled_patch hgood.1 hInv hemb p hV hfix
  have hAS : A ⊆ S := hAV.trans hVS
  let f : U → sliceGerm u.1 W := fun a => (e a).1
  have hf : Topology.IsOpenEmbedding f := hS.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
  have hArange : A ⊆ Set.range f := by
    intro s hs
    exact ⟨e.symm ⟨s,hAS hs⟩,by simp [f]⟩
  let B : Set U := f ⁻¹' A
  have hB : IsOpen B := hA.preimage hf.continuous
  let P : Set TenParam := Subtype.val '' B
  have hP : IsOpen P := hU.isOpenEmbedding_subtypeVal.isOpenMap _ hB
  let eb : B ≃ₜ A := hf.toIsEmbedding.homeomorphOfSubsetRange hArange
  let ep : P ≃ₜ A := (Topology.IsEmbedding.subtypeVal.homeomorphImage B).symm.trans eb
  let k : A → CodeModuli := fun a => c a.1
  have hk : Topology.IsOpenEmbedding k := unlabelledHomeo.isOpenEmbedding.comp hAe
  refine ⟨P,hP,⟨_,(ep.symm ⟨p,hpA⟩).2⟩,Set.range k,hk.isOpen_range,?_,
    ⟨ep.trans hk.toIsEmbedding.toHomeomorph⟩⟩
  rintro q ⟨a,rfl⟩
  exact hSN (hAS a.2)

/-- The actual code patch endpoint in the Euclidean ten-space used by the
invariance-of-dimension theorem. -/
theorem native_code_ten_patches (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus)
    {N : Set CodeModuli} (hN : IsOpen N) (hseed : codeClass u ∈ N) :
    ∃ P : Set (EuclideanSpace ℝ (Fin 10)), IsOpen P ∧ P.Nonempty ∧
      ∃ Q : Set CodeModuli, IsOpen Q ∧ Q ⊆ N ∧ Nonempty (P ≃ₜ Q) := by
  obtain ⟨U,hU,hUn,Q,hQ,hQN,⟨e⟩⟩ := native_code_ten_param_patches u hgood hpivot hN hseed
  let L : EuclideanSpace ℝ (Fin 10) ≃L[ℝ] TenParam :=
    (LinearEquiv.ofFinrankEq (EuclideanSpace ℝ (Fin 10)) TenParam (show Module.finrank ℝ (EuclideanSpace ℝ (Fin 10)) =
      Module.finrank ℝ TenParam by simp [TenParam,Module.finrank_prod])).toContinuousLinearEquiv
  have hrange : U ⊆ Set.range L := fun a _ => ⟨L.symm a,L.apply_symm_apply a⟩
  let eL := L.toHomeomorph.isEmbedding.homeomorphOfSubsetRange hrange
  obtain ⟨a,ha⟩ := hUn
  refine ⟨L ⁻¹' U,hU.preimage L.continuous,⟨L.symm a,?_⟩,Q,hQ,hQN,⟨eL.trans e⟩⟩
  simpa using ha

#print axioms native_code_ten_param_patches
#print axioms native_code_ten_patches
end Option2.NativeStress.NativeCodeTenPatchesA7

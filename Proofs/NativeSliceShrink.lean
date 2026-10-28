module

public import NativeLocalDimensionLower

@[expose] public section

/-! Shrinking the actual finite native slice chart while retaining an open
quotient embedding. No dimension bound is assumed or asserted here. -/
noncomputable section
namespace Option2.NativeStress.NativeLocalDimensionA7
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeUnlabelledSlice
open SliceTenPatchesA7
open scoped Topology

theorem native_invariant_open_within (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {W₀ : Set Cfg}
    (h0 : IsOpen W₀) (hP : literalCfg ξ ∈ W₀) :
    ∃ W : Set Cfg, IsOpen W ∧ literalCfg ξ ∈ W ∧ W ⊆ W₀ ∧
      ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W := by
  have := finite_stab ξ hξ
  refine ⟨⋂ γ : stab ξ, (fun C : Cfg => (γ : Big) • C) ⁻¹' W₀,
    isOpen_iInter_of_finite fun γ => h0.preimage (continuous_const_smul _), ?_, ?_, ?_⟩
  · simp only [Set.mem_iInter, Set.mem_preimage]
    intro γ
    rw [(mem_stab_iff ξ _).1 γ.2]
    exact hP
  · intro C hC
    have h1 := Set.mem_iInter.1 hC 1
    simpa using h1
  · intro δ hδ C
    simp only [Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h γ
      have h1 := h ⟨(γ : Big) * δ⁻¹, (stab ξ).mul_mem γ.2 ((stab ξ).inv_mem hδ)⟩
      rwa [mul_smul, inv_smul_smul] at h1
    · intro h γ
      rw [← mul_smul]
      exact h ⟨(γ : Big) * δ, (stab ξ).mul_mem γ.2 hδ⟩


/-- Restricting the actual slice quotient to an ambient-open subneighborhood
preserves its open embedding into the unlabelled quotient. -/
theorem sliceQuotMap_isOpenEmbedding_of_subset {ξ : Fin 4 → ℂ} {W V : Set Cfg}
    (hW : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W)
    (hemb : Topology.IsOpenEmbedding (sliceQuotMap ξ W))
    (hV : IsOpen V) (hVW : V ⊆ W) :
    Topology.IsOpenEmbedding (sliceQuotMap ξ V) := by
  let inc : sliceGerm ξ V → sliceGerm ξ W := fun s => ⟨s.1,hVW s.2.1,s.2.2⟩
  have hi : Topology.IsEmbedding inc :=
    (Topology.IsEmbedding.subtypeVal.of_comp_iff).1
      (show Topology.IsEmbedding (Subtype.val ∘ inc) from Topology.IsEmbedding.subtypeVal)
  have hirange : Set.range inc = {s : sliceGerm ξ W | (s.1 : Cfg) ∈ V} := by
    ext s
    constructor
    · rintro ⟨t,rfl⟩
      exact t.2.1
    · intro hs
      exact ⟨⟨s.1,hs,s.2.2⟩,rfl⟩
  have hio : Topology.IsOpenEmbedding inc := ⟨hi,by
    rw [hirange]
    exact hV.preimage (continuous_subtype_val.comp continuous_subtype_val)⟩
  let j : SliceQuot ξ V → SliceQuot ξ W :=
    Quotient.map inc (fun _ _ h => h)
  have hjc : Continuous j :=
    Continuous.quotient_lift (continuous_quot_mk.comp hi.continuous) _
  have hji : Function.Injective j := by
    intro x y hxy
    obtain ⟨s,rfl⟩ := Quotient.exists_rep x
    obtain ⟨t,rfl⟩ := Quotient.exists_rep y
    have hh : (stabSetoid ξ W).r (inc s) (inc t) := Quotient.exact hxy
    exact Quotient.sound hh
  have hjo : IsOpenMap j :=
    IsOpenMap.of_comp continuous_quot_mk (Quotient.mk_surjective)
      ((isOpenMap_sliceQuotMk hW).comp hio.isOpenMap)
  have hj : Topology.IsOpenEmbedding j := .of_continuous_injective_isOpenMap hjc hji hjo
  have he : (sliceQuotMap ξ W) ∘ j = sliceQuotMap ξ V := by
    funext q
    obtain ⟨s,rfl⟩ := Quotient.exists_rep q
    rfl
  rw [← he]
  exact hemb.comp hj

/-- The actual affine normal coordinate is an embedding of the whole
native zero-slice carrier, independent of any chart or model parametrization. -/
theorem isEmbedding_sliceNormal (ξ : Fin 4 → ℂ) (W : Set Cfg) :
    Topology.IsEmbedding (sliceNormal ξ W) := by
  let g : ↥(normalC ξ) → Cfg := fun n => literalCfg ξ + (n : Cfg)
  have hg : Continuous g := continuous_const.add continuous_subtype_val
  apply Topology.IsEmbedding.of_comp (continuous_sliceNormal ξ W) hg
  have he : g ∘ sliceNormal ξ W = fun s : sliceGerm ξ W => (s.1 : Cfg) := by
    funext s
    exact add_sub_cancel _ _
  rw [he]
  exact (show Topology.IsEmbedding (Subtype.val : zeroSet → Cfg) from
    Topology.IsEmbedding.subtypeVal).comp Topology.IsEmbedding.subtypeVal

#print axioms native_invariant_open_within
#print axioms sliceQuotMap_isOpenEmbedding_of_subset
#print axioms isEmbedding_sliceNormal
end Option2.NativeStress.NativeLocalDimensionA7

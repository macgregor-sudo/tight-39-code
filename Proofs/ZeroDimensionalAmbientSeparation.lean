module
public import ClosedStratumSeparation

/-! Ambient partitions avoiding an arbitrary zero-dimensional subspace. The
subspace need not be closed, and the resulting open sets need not have disjoint
closures. This is the separation input for the successor dimension argument. -/
@[expose] public section
noncomputable section
namespace SmallInductiveClosedSum
open Set Topology TopologicalSpace
variable {X : Type*} [TopologicalSpace X] [CompletelyNormalSpace X]
  [SecondCountableTopology X]

/-- Relative clopen complementary pieces have disjoint ambient neighborhoods
in a completely normal space. -/
theorem clopen_subspace_images_separated (M : Set X) (C : Set M) (hC : IsClopen C) :
    SeparatedNhds (Subtype.val '' C : Set X) (Subtype.val '' Cᶜ : Set X) := by
  apply separatedNhds_iff_disjoint.mpr
  apply completely_normal
  · apply disjoint_left.mpr
    rintro x hx ⟨y,hy,rfl⟩
    have hc : y ∈ closure C := by
      rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
      exact hx
    exact hy (hC.isClosed.closure_eq ▸ hc)
  · apply disjoint_left.mpr
    rintro x ⟨y,hy,rfl⟩ hx
    have hc : y ∈ closure Cᶜ := by
      rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
      exact hx
    exact (hC.compl.isClosed.closure_eq ▸ hc) hy

/-- For every disjoint closed pair, an ambient partition can avoid a prescribed
zero-dimensional subspace, even when that subspace is not closed. -/
theorem zero_dimensional_ambient_separation
    (M : Set X) (hdim : HasSmallInductiveDimensionLE ↥M 0)
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧
      M ⊆ U ∪ V ∧ Disjoint U V := by
  obtain ⟨U₀,V₀,hU₀,hV₀,hAU₀,hBV₀,hUV₀⟩ :=
    normal_separation_disjoint_closures A B hA hB hAB
  obtain ⟨C,hC,hAC,hCB⟩ := zero_dimensional_clopen_separator hdim
    (Subtype.val ⁻¹' closure U₀) (Subtype.val ⁻¹' closure V₀)
    (isClosed_closure.preimage continuous_subtype_val)
    (isClosed_closure.preimage continuous_subtype_val) (hUV₀.preimage Subtype.val)
  let L : Set X := Subtype.val '' C
  let R : Set X := Subtype.val '' Cᶜ
  have hLR : SeparatedNhds L R := clopen_subspace_images_separated M C hC
  have hUR : Disjoint U₀ R := by
    apply disjoint_left.mpr
    rintro x hx ⟨y,hy,rfl⟩
    exact hy (hAC (subset_closure hx))
  have hLV : Disjoint L V₀ := by
    apply disjoint_left.mpr
    rintro x ⟨y,hy,rfl⟩ hx
    exact hCB hy (subset_closure hx)
  have hAR : SeparatedNhds A R := by
    apply separatedNhds_iff_disjoint.mpr
    apply completely_normal
    · rw [hA.closure_eq]
      exact hUR.mono_left hAU₀
    · exact (hUR.closure_right hU₀).mono_left hAU₀
  have hLB : SeparatedNhds L B := by
    apply separatedNhds_iff_disjoint.mpr
    apply completely_normal
    · exact (hLV.closure_left hV₀).mono_right hBV₀
    · rw [hB.closure_eq]
      exact hLV.mono_right hBV₀
  have hsep : SeparatedNhds (A ∪ L) (B ∪ R) :=
    ((normal_separation hA hB hAB).union_right hAR).union_left (hLB.union_right hLR)
  obtain ⟨U,V,hU,hV,hLU,hRV,hUV⟩ := hsep
  refine ⟨U,V,hU,hV,(fun _ h => hLU (Or.inl h)),
    (fun _ h => hRV (Or.inl h)),?_,hUV⟩
  intro x hx
  by_cases hc : (⟨x,hx⟩ : M) ∈ C
  · exact Or.inl (hLU (Or.inr ⟨⟨x,hx⟩,hc,rfl⟩))
  · exact Or.inr (hRV (Or.inr ⟨⟨x,hx⟩,hc,rfl⟩))

end SmallInductiveClosedSum
#print axioms SmallInductiveClosedSum.zero_dimensional_ambient_separation

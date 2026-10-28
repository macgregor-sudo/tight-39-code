module

public import ULCode

@[expose] public section

/-!
# Native open patches in the finite unlabelled quotient

This proves the finite-action descent step of MASTER §6.12 directly for the
actual compensated stabilizer and actual equation-zero slice. A point whose
stabilizer fixes a slice neighborhood pointwise has arbitrarily small open
patches embedding into the finite quotient. No freeness, normality, group
order, dimension preservation, or real-zero exhaustion is assumed or claimed.
The hypothesis about a pointwise-fixed neighborhood remains a geometric
obligation for the dense smooth-sheet application. The finite separation and
quotient openness are proved here, rather than included as assumptions.

Uses mathlib's quotient-topology and Hausdorff separation APIs, imported
through the accepted native slice package; no upstream implementation copied.

-/

noncomputable section
namespace CKM.NativeUnlabelledSlice

open Glennie NativePolynomial CKM.NativeFirstOrder CKM.NativeGroupSlice
open scoped Topology

variable {ξ : Fin 4 → ℂ} {W : Set Cfg}

/-- The actual stabilizer action restricted to an invariant native slice. -/
def patchSliceAct
    (hW : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W)
    (γ : stab ξ) (s : sliceGerm ξ W) : sliceGerm ξ W :=
  ⟨zeroAct γ.1 s.1,
    (hW γ.1 γ.2 _).2 s.2.1,
    (smul_mem_sliceSet_iff γ.2 _).2 s.2.2⟩

theorem continuous_patchSliceAct
    (hW : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W)
    (γ : stab ξ) : Continuous (patchSliceAct hW γ) := by
  exact (((continuous_const_smul γ.1).comp
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).subtype_mk _

/-- Quotient openness holds on every invariant slice neighborhood. -/
theorem isOpenMap_sliceQuotMk
    (hW : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W) :
    IsOpenMap (Quotient.mk (stabSetoid ξ W)) := by
  intro U hU
  apply (isQuotientMap_quotient_mk' (s := stabSetoid ξ W)).isOpen_preimage.1
  have hs : Quotient.mk (stabSetoid ξ W) ⁻¹'
      (Quotient.mk (stabSetoid ξ W) '' U) =
      ⋃ γ : stab ξ, patchSliceAct hW γ ⁻¹' U := by
    ext s
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨t, ht, heq⟩
      obtain ⟨γ, hγ, hgt⟩ := Quotient.exact heq
      refine ⟨⟨γ⁻¹, (stab ξ).inv_mem hγ⟩, ?_⟩
      have hst : patchSliceAct hW ⟨γ⁻¹, (stab ξ).inv_mem hγ⟩ s = t := by
        apply Subtype.ext
        apply Subtype.ext
        change γ⁻¹ • ((s : zeroSet) : Cfg) = ((t : zeroSet) : Cfg)
        rw [← hgt, inv_smul_smul]
      rwa [hst]
    · rintro ⟨γ, hγ⟩
      refine ⟨patchSliceAct hW γ s, hγ, Quotient.sound ?_⟩
      refine ⟨γ.1⁻¹, (stab ξ).inv_mem γ.2, ?_⟩
      exact inv_smul_smul γ.1 ((s : zeroSet) : Cfg)
  change IsOpen (Quotient.mk (stabSetoid ξ W) ⁻¹'
    (Quotient.mk (stabSetoid ξ W) '' U))
  rw [hs]
  exact isOpen_iUnion fun γ => hU.preimage (continuous_patchSliceAct hW γ)

/-- Finite separation removes every stabilizer element which moves `p`.
This is a Hausdorff argument; an invariant Euclidean metric is unnecessary. -/
theorem exists_open_slice_separation (hξ : IsUnitPhase ξ)
    (hW : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W)
    (p : sliceGerm ξ W) {V : Set (sliceGerm ξ W)} (hV : V ∈ 𝓝 p) :
    ∃ U : Set (sliceGerm ξ W), IsOpen U ∧ p ∈ U ∧ U ⊆ V ∧
      ∀ γ : stab ξ, patchSliceAct hW γ p ≠ p →
        ∀ s ∈ U, ∀ t ∈ U, patchSliceAct hW γ s ≠ t := by
  let := finite_stab ξ hξ
  have hall : ∀ᶠ z : (sliceGerm ξ W) × (sliceGerm ξ W) in 𝓝 (p,p),
      ∀ γ : stab ξ, patchSliceAct hW γ p ≠ p → patchSliceAct hW γ z.1 ≠ z.2 := by
    apply Filter.eventually_all.2
    intro γ
    by_cases hγ : patchSliceAct hW γ p = p
    · exact Filter.Eventually.of_forall fun _ hn => (hn hγ).elim
    · exact Filter.Eventually.mono
        ((isOpen_ne_fun ((continuous_patchSliceAct hW γ).comp continuous_fst)
          continuous_snd).mem_nhds hγ) (fun _ h _ => h)
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 hall
  obtain ⟨U, hUsub, hU, hp⟩ := mem_nhds_iff.1
    (Filter.inter_mem (Filter.inter_mem hA hB) hV)
  refine ⟨U, hU, hp, fun s hs => (hUsub hs).2, ?_⟩
  intro γ hγ s hs t ht
  exact hAB (show (s,t) ∈ A ×ˢ B from
    ⟨(hUsub hs).1.1, (hUsub ht).1.2⟩) γ hγ

/-- If the stabilizer of `p` fixes a neighborhood pointwise, the quotient
has arbitrarily small open patches retaining all the topology upstairs. -/
theorem exists_open_sliceQuot_patch (hξ : IsUnitPhase ξ)
    (hW : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W)
    (p : sliceGerm ξ W) {V : Set (sliceGerm ξ W)} (hV : V ∈ 𝓝 p)
    (hfix : ∀ γ : stab ξ, patchSliceAct hW γ p = p →
      ∀ s ∈ V, patchSliceAct hW γ s = s) :
    ∃ U : Set (sliceGerm ξ W), IsOpen U ∧ p ∈ U ∧ U ⊆ V ∧
      Topology.IsOpenEmbedding
        (fun s : U => Quotient.mk (stabSetoid ξ W) (s : sliceGerm ξ W)) := by
  obtain ⟨U, hU, hp, hUV, hsep⟩ := exists_open_slice_separation hξ hW p hV
  refine ⟨U, hU, hp, hUV, .of_continuous_injective_isOpenMap
    (continuous_quot_mk.comp continuous_subtype_val) ?_
    ((isOpenMap_sliceQuotMk hW).comp hU.isOpenEmbedding_subtypeVal.isOpenMap)⟩
  intro s t heq
  obtain ⟨γ, hγ, hst⟩ := Quotient.exact heq
  have hast : patchSliceAct hW ⟨γ,hγ⟩ s.1 = t.1 :=
    Subtype.ext (Subtype.ext hst)
  by_cases hgp : patchSliceAct hW ⟨γ,hγ⟩ p = p
  · exact Subtype.ext ((hfix ⟨γ,hγ⟩ hgp s.1 (hUV s.2)).symm.trans hast)
  · exact (hsep ⟨γ,hγ⟩ hgp s.1 s.2 t.1 t.2 hast).elim

/-- Composing with the accepted native slice chart gives a patch in the
actual unlabelled orbit space, not an auxiliary abstract group quotient. -/
theorem exists_open_unlabelled_patch (hξ : IsUnitPhase ξ)
    (hW : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W)
    (hemb : Topology.IsOpenEmbedding (sliceQuotMap ξ W))
    (p : sliceGerm ξ W) {V : Set (sliceGerm ξ W)} (hV : V ∈ 𝓝 p)
    (hfix : ∀ γ : stab ξ, patchSliceAct hW γ p = p →
      ∀ s ∈ V, patchSliceAct hW γ s = s) :
    ∃ U : Set (sliceGerm ξ W), IsOpen U ∧ p ∈ U ∧ U ⊆ V ∧
      Topology.IsOpenEmbedding
        (fun s : U => Quotient.mk bigSetoid ((s : sliceGerm ξ W) : zeroSet)) := by
  obtain ⟨U, hU, hp, hUV, hpatch⟩ := exists_open_sliceQuot_patch hξ hW p hV hfix
  exact ⟨U,hU,hp,hUV, hemb.comp hpatch⟩

/-- The resulting patch is open in the actual optimal-code moduli space
and homeomorphic to the native slice patch. Its image contains the code of
`p`. No dimension statement is hidden in the definition of the patch. -/
theorem exists_open_code_patch_homeomorph (hξ : IsUnitPhase ξ)
    (hW : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W)
    (hemb : Topology.IsOpenEmbedding (sliceQuotMap ξ W))
    (p : sliceGerm ξ W) {V : Set (sliceGerm ξ W)} (hV : V ∈ 𝓝 p)
    (hfix : ∀ γ : stab ξ, patchSliceAct hW γ p = p →
      ∀ s ∈ V, patchSliceAct hW γ s = s) :
    ∃ U : Set (sliceGerm ξ W), IsOpen U ∧ p ∈ U ∧ U ⊆ V ∧
      ∃ Q : Set CodeModuli, IsOpen Q ∧
        unlabelledToCode (Quotient.mk bigSetoid (p : zeroSet)) ∈ Q ∧
        Nonempty (U ≃ₜ Q) := by
  obtain ⟨U,hU,hp,hUV,hu⟩ := exists_open_unlabelled_patch hξ hW hemb p hV hfix
  let f : U → CodeModuli := fun s =>
    unlabelledToCode (Quotient.mk bigSetoid ((s : sliceGerm ξ W) : zeroSet))
  have hf : Topology.IsOpenEmbedding f := unlabelledHomeo.isOpenEmbedding.comp hu
  exact ⟨U,hU,hp,hUV,Set.range f,hf.isOpen_range,
    ⟨⟨p,hp⟩,rfl⟩,⟨hf.toIsEmbedding.toHomeomorph⟩⟩

#print axioms isOpenMap_sliceQuotMk
#print axioms exists_open_slice_separation
#print axioms exists_open_sliceQuot_patch
#print axioms exists_open_unlabelled_patch
#print axioms exists_open_code_patch_homeomorph

end CKM.NativeUnlabelledSlice

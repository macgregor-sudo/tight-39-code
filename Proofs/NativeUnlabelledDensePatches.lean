module

public import NativeUnlabelledOpenPatch

@[expose] public section

/-!
# Open dense native quotient patches

Remove the boundaries of the finitely many fixed-point sets in the actual
slice zero set. On the resulting open dense set the point stabilizer fixes a
neighborhood pointwise. Finite separation then gives genuine open patches in
the actual code quotient. The slice itself need not be smooth, and no dimension
claim follows from this topological result alone.

The argument uses mathlib's `interior_frontier`, `isClosed_eq` and finite
intersection of dense open sets. No analytic uniqueness or free action is
needed. 
-/

noncomputable section
namespace CKM.NativeUnlabelledSlice
open Glennie NativePolynomial CKM.NativeFirstOrder CKM.NativeGroupSlice
open scoped Topology

variable {ξ : Fin 4 → ℂ} {W : Set Cfg}

def patchFixedSet
    (hW : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W)
    (γ : stab ξ) : Set (sliceGerm ξ W) := {s | patchSliceAct hW γ s = s}

theorem isClosed_patchFixedSet
    (hW : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W)
    (γ : stab ξ) : IsClosed (patchFixedSet hW γ) :=
  isClosed_eq (continuous_patchSliceAct hW γ) continuous_id

/-- Explicit locus with locally constant stabilizer, defined on the whole
native slice zero set, rather than on a chosen constructed family. -/
def nativeRegularStabilizerLocus
    (hW : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W) :
    Set (sliceGerm ξ W) := ⋂ γ : stab ξ, (frontier (patchFixedSet hW γ))ᶜ

theorem isOpen_dense_nativeRegularStabilizerLocus (hξ : IsUnitPhase ξ)
    (hW : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W) :
    IsOpen (nativeRegularStabilizerLocus hW) ∧
      Dense (nativeRegularStabilizerLocus hW) := by
  classical
  let := finite_stab ξ hξ
  let := Fintype.ofFinite (stab ξ)
  have hfin : ∀ s : Finset (stab ξ),
      IsOpen (⋂ γ ∈ s, (frontier (patchFixedSet hW γ))ᶜ) ∧
      Dense (⋂ γ ∈ s, (frontier (patchFixedSet hW γ))ᶜ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert γ s hγ ih =>
      simp only [Finset.mem_insert, Set.iInter_iInter_eq_or_left]
      have hopen : IsOpen (frontier (patchFixedSet hW γ))ᶜ := isClosed_frontier.isOpen_compl
      have hdense : Dense (frontier (patchFixedSet hW γ))ᶜ :=
        interior_eq_empty_iff_dense_compl.1 (interior_frontier (isClosed_patchFixedSet hW γ))
      exact ⟨hopen.inter ih.1, hdense.inter_of_isOpen_left ih.2 hopen⟩
  simpa [nativeRegularStabilizerLocus] using hfin Finset.univ

/-- The previously explicit stabilizer-neighborhood premise is discharged
at every point of the open dense locus, inside any requested neighborhood. -/
theorem exists_pointwise_stabilizer_nhds (hξ : IsUnitPhase ξ)
    (hW : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W)
    {p : sliceGerm ξ W} (hp : p ∈ nativeRegularStabilizerLocus hW)
    {O : Set (sliceGerm ξ W)} (hO : O ∈ 𝓝 p) :
    ∃ V : Set (sliceGerm ξ W), V ∈ 𝓝 p ∧ V ⊆ O ∧
      ∀ γ : stab ξ, patchSliceAct hW γ p = p →
        ∀ s ∈ V, patchSliceAct hW γ s = s := by
  let := finite_stab ξ hξ
  let F : stab ξ → Set (sliceGerm ξ W) :=
    fun γ => {s | patchSliceAct hW γ p = p → patchSliceAct hW γ s = s}
  have hF : ∀ γ, F γ ∈ 𝓝 p := by
    intro γ
    by_cases hg : patchSliceAct hW γ p = p
    · have hn : p ∉ frontier (patchFixedSet hW γ) := Set.mem_iInter.1 hp γ
      have hi : p ∈ interior (patchFixedSet hW γ) := by
        by_contra hi
        exact hn ⟨(isClosed_patchFixedSet hW γ).closure_eq.symm ▸ hg, hi⟩
      exact Filter.mem_of_superset (isOpen_interior.mem_nhds hi)
        (fun s hs _ => (interior_subset (s := patchFixedSet hW γ)) hs)
    · exact Filter.Eventually.of_forall fun _ h => (hg h).elim
  refine ⟨O ∩ ⋂ γ, F γ, Filter.inter_mem hO (Filter.iInter_mem.2 hF),
    Set.inter_subset_left, ?_⟩
  intro γ hg s hs
  exact Set.mem_iInter.1 hs.2 γ hg

theorem regularStabilizerPoint_has_open_code_patches (hξ : IsUnitPhase ξ)
    (hW : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W)
    (hemb : Topology.IsOpenEmbedding (sliceQuotMap ξ W))
    {p : sliceGerm ξ W} (hp : p ∈ nativeRegularStabilizerLocus hW)
    {O : Set (sliceGerm ξ W)} (hO : O ∈ 𝓝 p) :
    ∃ U : Set (sliceGerm ξ W), IsOpen U ∧ p ∈ U ∧ U ⊆ O ∧
      ∃ Q : Set CodeModuli, IsOpen Q ∧
        unlabelledToCode (Quotient.mk bigSetoid (p : zeroSet)) ∈ Q ∧
        Nonempty (U ≃ₜ Q) := by
  obtain ⟨V,hV,hVO,hfix⟩ := exists_pointwise_stabilizer_nhds hξ hW hp hO
  obtain ⟨U,hU,hpU,hUV,hQ⟩ := exists_open_code_patch_homeomorph hξ hW hemb p hV hfix
  exact ⟨U,hU,hpU,hUV.trans hVO,hQ⟩

/-- Every unit phase has an actual finite-slice neighborhood containing an
explicit open dense locus of arbitrarily small open code quotient patches.
All native quotient hypotheses are supplied by the accepted slice theorem. -/
theorem native_dense_open_code_patches (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    ∃ W : Set Cfg, IsOpen W ∧ literalCfg ξ ∈ W ∧
      ∃ hW : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W,
        IsOpen (nativeRegularStabilizerLocus hW) ∧
        Dense (nativeRegularStabilizerLocus hW) ∧
        ∀ p ∈ nativeRegularStabilizerLocus hW,
          ∀ O : Set (sliceGerm ξ W), O ∈ 𝓝 p →
          ∃ U : Set (sliceGerm ξ W), IsOpen U ∧ p ∈ U ∧ U ⊆ O ∧
            ∃ Q : Set CodeModuli, IsOpen Q ∧
              unlabelledToCode (Quotient.mk bigSetoid (p : zeroSet)) ∈ Q ∧
              Nonempty (U ≃ₜ Q) := by
  obtain ⟨W,hWo,hP,hW,_,hemb,_⟩ := exists_sliceQuot_isOpenEmbedding ξ hξ
  have hD := isOpen_dense_nativeRegularStabilizerLocus hξ hW
  exact ⟨W,hWo,hP,hW,hD.1,hD.2,fun _ hp _ hO =>
    regularStabilizerPoint_has_open_code_patches hξ hW hemb hp hO⟩

#print axioms isOpen_dense_nativeRegularStabilizerLocus
#print axioms exists_pointwise_stabilizer_nhds
#print axioms regularStabilizerPoint_has_open_code_patches
#print axioms native_dense_open_code_patches
end CKM.NativeUnlabelledSlice

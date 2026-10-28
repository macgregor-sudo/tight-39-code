module
public import ZeroDimensionalSeparation
public import Mathlib.Topology.Separation.Regular

/-! Absorbing a closed zero-dimensional stratum into a separated pair of open
sets. This is the recursive step for the dimension-zero countable closed sum. -/
@[expose] public section
noncomputable section
namespace SmallInductiveClosedSum
open Set Topology TopologicalSpace
variable {X : Type*} [TopologicalSpace X] [NormalSpace X]

/-- Normal separation with disjoint closures of the open neighborhoods. -/
theorem normal_separation_disjoint_closures (A B : Set X)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧
      Disjoint (closure U) (closure V) := by
  obtain ⟨U₀,V₀,hU₀,hV₀,hAU₀,hBV₀,hUV₀⟩ := normal_separation hA hB hAB
  obtain ⟨U,hU,hAU,hcU⟩ := normal_exists_closure_subset hA hU₀ hAU₀
  obtain ⟨V,hV,hBV,hcV⟩ := normal_exists_closure_subset hB hV₀ hBV₀
  exact ⟨U,V,hU,hV,hAU,hBV,hUV₀.mono hcU hcV⟩

/-- A closed zero-dimensional stratum can be absorbed while retaining separated
closures. The old closed sets need not be contained in the stratum. -/
theorem absorb_closed_zero_dimensional [SecondCountableTopology X]
    (F : Set X) (hF : IsClosed F) (hdim : HasSmallInductiveDimensionLE ↥F 0)
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ B ⊆ V ∧
      F ⊆ U ∪ V ∧ Disjoint (closure U) (closure V) := by
  obtain ⟨C,hC,hAC,hCB⟩ := zero_dimensional_clopen_separator hdim
    (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' B)
    (hA.preimage continuous_subtype_val) (hB.preimage continuous_subtype_val)
    (hAB.preimage Subtype.val)
  let L : Set X := A ∪ Subtype.val '' C
  let R : Set X := B ∪ Subtype.val '' Cᶜ
  have hL : IsClosed L := hA.union (hF.isClosedMap_subtype_val C hC.isClosed)
  have hR : IsClosed R := hB.union (hF.isClosedMap_subtype_val Cᶜ hC.compl.isClosed)
  have hLR : Disjoint L R := by
    apply disjoint_left.mpr
    intro x hx hy
    rcases hx with hx | ⟨a,ha,rfl⟩
    · rcases hy with hy | ⟨b,hb,rfl⟩
      · exact disjoint_left.mp hAB hx hy
      · exact hb (hAC hx)
    · rcases hy with hy | ⟨b,hb,hab⟩
      · exact hCB ha hy
      · have he : b = a := Subtype.ext hab
        exact hb (he.symm ▸ ha)
  obtain ⟨U,V,hU,hV,hLU,hRV,hUV⟩ := normal_separation_disjoint_closures L R hL hR hLR
  refine ⟨U,V,hU,hV,(fun _ h => hLU (Or.inl h)),
    (fun _ h => hRV (Or.inl h)),?_,hUV⟩
  intro x hx
  by_cases hc : (⟨x,hx⟩ : F) ∈ C
  · exact Or.inl (hLU (Or.inr ⟨⟨x,hx⟩,hc,rfl⟩))
  · exact Or.inr (hRV (Or.inr ⟨⟨x,hx⟩,hc,rfl⟩))

end SmallInductiveClosedSum
#print axioms SmallInductiveClosedSum.absorb_closed_zero_dimensional

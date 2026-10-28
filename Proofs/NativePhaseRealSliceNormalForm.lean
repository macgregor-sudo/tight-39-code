module

public import NativePhaseAnalyticBranches

@[expose] public section

/-! Exact real-parameter interpretation of the four constructed native
branches, and the simultaneous normal form of their retained real slice
families. This does not identify all real zeros or invoke an unproved
analytic-component/minimal-prime correspondence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Option2.NativeStress.PhaseRealSliceNormalFormA6
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open PhaseEntireFamilyA6 PhaseAnalyticBranchesA6 PhaseHilbertA6
open Filter
open scoped Topology

/-- The actual complex branch restricted to its real parameters is the
same centered A5 raw family, with the explicit 62-coordinate reindexing. -/
theorem branch_real_parameters (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (x : Fin 62 → ℝ) :
    branch H ξ hξ (fun k => (x k : ℂ)) =
      (fun k => ((NativePolynomial.PartialAction.pack
        (rawMap62 ξ hξ H (realParam (fun j => x (paramIndexEquiv j)))) k : ℝ) : ℂ)) -
      AnalyticDerivative.complexPack (literalCfg ξ) := by
  unfold branch
  have hc : paramCoordinatesCLM (fun k => (x k : ℂ)) =
      (fun j => ((x (paramIndexEquiv j) : ℝ) : ℂ)) := rfl
  rw [hc, PhaseEntireFamiliesA6.rawExtension_real]

/-- A single analytic chart identifies the union of the four actual slice
families with arbitrary common R4 coordinates, at most one active R6 block,
and zero complementary coordinate. Every sufficiently small prescribed
parameter neighbourhood is retained, and the target neighbourhood may shrink. -/
theorem retained_real_slice_union_normal_form {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    ∃ Φ : OpenPartialHomeomorph SliceModel (normalC ξ),
      ∃ V₀ : Fin 4 → Set SliceParam,
      (0 : SliceModel) ∈ Φ.source ∧ Φ 0 = 0 ∧
      AnalyticOnNhd ℝ Φ Φ.source ∧ AnalyticOnNhd ℝ Φ.symm Φ.target ∧
      (∀ H, V₀ H ∈ 𝓝 (0 : SliceParam)) ∧
      ∀ V : Fin 4 → Set SliceParam,
        (∀ H, V H ∈ 𝓝 (0 : SliceParam)) → (∀ H, V H ⊆ V₀ H) →
        ∀ᶠ n : normalC ξ in 𝓝 0, n ∈ Φ.target ∧
          (n ∈ ⋃ H : Fin 4, (sliceFam ξ hξ.1 H) '' V H ↔
            ∃ H : Fin 4,
              (∀ j : Fin 4, j ≠ H → (Φ.symm n).2.1 j = 0) ∧
              (Φ.symm n).2.2 = 0) := by
  obtain ⟨Φ, hsource, hzero, hΦ, hΦsymm, hcommon, hfamily, hinter⟩ := exists_slice_chart hξ
  choose V₀ hV₀ hgerm using hfamily
  refine ⟨Φ,V₀,hsource,hzero,hΦ,hΦsymm,hV₀,?_⟩
  intro V hV hsub
  have htarget : Φ.target ∈ 𝓝 (0 : normalC ξ) := by
    apply Φ.open_target.mem_nhds
    simpa only [hzero] using Φ.map_source hsource
  have hall : ∀ᶠ n : normalC ξ in 𝓝 0, ∀ H : Fin 4,
      n ∈ (sliceFam ξ hξ.1 H) '' V H ↔
        n ∈ Φ '' (Φ.source ∩ familyBlock (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H) := by
    apply Filter.eventually_all.mpr
    intro H
    filter_upwards [hgerm H (V H) (hV H) (hsub H)] with n hn
    exact Iff.of_eq hn
  have hmem (H : Fin 4) (n : normalC ξ) (hn : n ∈ Φ.target) :
      n ∈ Φ '' (Φ.source ∩ familyBlock (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H) ↔
        (∀ j : Fin 4, j ≠ H → (Φ.symm n).2.1 j = 0) ∧ (Φ.symm n).2.2 = 0 := by
    change n ∈ Φ '' (Φ.source ∩ familyBlock (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H) ↔
      Φ.symm n ∈ familyBlock (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H
    constructor
    · rintro ⟨p,⟨hp,hblock⟩,rfl⟩
      rwa [Φ.left_inv hp]
    · intro hblock
      exact ⟨Φ.symm n,⟨Φ.map_target hn,hblock⟩,Φ.right_inv hn⟩
  filter_upwards [htarget,hall] with n hn halln
  refine ⟨hn,?_⟩
  simp only [Set.mem_iUnion]
  exact exists_congr fun H => (halln H).trans (hmem H n hn)

#print axioms Option2.NativeStress.PhaseRealSliceNormalFormA6.branch_real_parameters
#print axioms Option2.NativeStress.PhaseRealSliceNormalFormA6.retained_real_slice_union_normal_form
end Option2.NativeStress.PhaseRealSliceNormalFormA6

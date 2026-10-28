module

public import NativePhaseRealSheetIsolation

@[expose] public section

/-! Preserve any prescribed real parameter neighborhood through the actual
complex retraction and the local real-locus theorem.  -/

noncomputable section
namespace Option2.NativeStress.PhaseRealSheetWithinA7
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open PhasePivotA6 PhasePivotLocusA6 PhaseHilbertA6 PhaseJetBoundA6
open PhaseAnalyticBranchesA6 PhaseBranchNeighborhoodA7 PhaseRealLocusA6
open PhaseRealSliceNormalFormA6 PhaseEntireFamilyA6
open NativePolynomial NativePolynomial.ConfigurationResiduals
open ConvergentResidualJets Filter
open PhaseRealSheetIsolationA7
open scoped Topology

theorem native_real_sheet_isolation_within (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) (H : Fin 4)
    (A : Set (Fin 62 → ℝ)) (hA : A ∈ 𝓝 0) :
    ∃ κ : (Fin 1053 → ℂ) → ℂ, AnalyticAt ℂ κ 0 ∧
      ¬ ((fun y => κ (branch H u.1 hgood.1 y)) =ᶠ[𝓝 0] 0) ∧
      ∃ P : Set (Fin 62 → ℂ), P ∈ 𝓝 0 ∧
      (∀ z ∈ P, (fun j => (z j).re) ∈ A) ∧
      ∃ V : Set (Fin 1053 → ℝ), IsOpen V ∧ 0 ∈ V ∧
        ∀ x ∈ V, κ (fun j => (x j : ℂ)) ≠ 0 →
          (Option2.NativeStress.originalF (PartialAction.pack (literalCfg u.1) + x) = 0 ↔
            ∃ a : Fin 62 → ℝ, (fun j => (a j : ℂ)) ∈ P ∧
              x = nativeRealBranch H u.1 hgood.1 a) := by
  obtain ⟨κ,hκ,hnz,ρ,hρ,hρ0,_,U,hU,h0U,hiso⟩ :=
    native_complex_sheet_isolation u hgood hpivot H
  obtain ⟨P₀,hP₀,hreal₀⟩ := branch_real_iff_locally H u.1 hgood.1
  have hre : Continuous (fun z : Fin 62 → ℂ => fun j => (z j).re) :=
    continuous_pi fun j => Complex.continuous_re.comp (continuous_apply j)
  have hAr : (fun z : Fin 62 → ℂ => fun j => (z j).re) ⁻¹' A ∈ 𝓝 0 :=
    hre.continuousAt.preimage_mem_nhds (by change A ∈ 𝓝 (0 : Fin 62 → ℝ); exact hA)
  let P := P₀ ∩ (fun z : Fin 62 → ℂ => fun j => (z j).re) ⁻¹' A
  have hP : P ∈ 𝓝 0 := inter_mem hP₀ hAr
  have hreal : ∀ z ∈ P, (∀ j, (branch H u.1 hgood.1 z j).im = 0) ↔
      (∀ j, (z j).im = 0) := fun z hz => hreal₀ z hz.1
  have hρP : ρ ⁻¹' P ∈ 𝓝 (0 : Fin 1053 → ℂ) := by
    apply hρ.continuousAt.preimage_mem_nhds
    rwa [hρ0]
  have hcast : Continuous (fun x : Fin 1053 → ℝ => fun j => (x j : ℂ)) :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)
  have hcast0 : (fun j => ((0 : Fin 1053 → ℝ) j : ℂ)) = 0 := by ext j; rfl
  have hN : (fun x : Fin 1053 → ℝ => fun j => (x j : ℂ)) ⁻¹' (U ∩ ρ ⁻¹' P) ∈ 𝓝 0 := by
    apply hcast.continuousAt.preimage_mem_nhds
    rw [hcast0]
    exact inter_mem (hU.mem_nhds h0U) hρP
  obtain ⟨V,hVsub,hV,h0V⟩ := mem_nhds_iff.1 hN
  refine ⟨κ,hκ,hnz,P,hP,fun _ hz => hz.2,V,hV,h0V,?_⟩
  intro x hx hkx
  have hxU := (hVsub hx).1
  have hxP := (hVsub hx).2
  constructor
  · intro hz
    have he := (hiso _ hxU hkx).1 ((nativeComplexZero_real_iff u.1 x).2 hz)
    have hzreal : ∀ j, (ρ (fun k => (x k : ℂ)) j).im = 0 := by
      apply (hreal _ hxP).1
      intro k
      rw [← he]
      exact Complex.ofReal_im _
    let a : Fin 62 → ℝ := fun j => (ρ (fun k => (x k : ℂ)) j).re
    have ha : (fun j => (a j : ℂ)) = ρ (fun k => (x k : ℂ)) := by
      funext j
      apply Complex.ext
      · rfl
      · exact (hzreal j).symm
    refine ⟨a,ha.symm ▸ hxP,?_⟩
    have he' : (fun j => (x j : ℂ)) =
        (fun j => (nativeRealBranch H u.1 hgood.1 a j : ℂ)) := by
      rw [nativeRealBranch_complex,ha]
      exact he
    funext j
    exact Complex.ofReal_injective (congrFun he' j)
  · rintro ⟨a,_,rfl⟩
    apply (nativeComplexZero_real_iff u.1 _).1
    rw [nativeRealBranch_complex]
    exact fun r => branch_original_rows H u.1 hgood.1 r _


#print axioms native_real_sheet_isolation_within
end Option2.NativeStress.PhaseRealSheetWithinA7

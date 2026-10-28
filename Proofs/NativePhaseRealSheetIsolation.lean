module

public import NativePhaseBranchNeighborhood
public import NativePhaseRealLocus

@[expose] public section

/-! Restrict the proved complex isolation to the actual real original-F
equations. Real branch parameters follow only after shrinking into the proved
local real-locus chart. No density of nonvanishing multiplier is asserted.
 -/

noncomputable section
namespace Option2.NativeStress.PhaseRealSheetIsolationA7
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open PhasePivotA6 PhasePivotLocusA6 PhaseHilbertA6 PhaseJetBoundA6
open PhaseAnalyticBranchesA6 PhaseBranchNeighborhoodA7 PhaseRealLocusA6
open PhaseRealSliceNormalFormA6 PhaseEntireFamilyA6
open NativePolynomial NativePolynomial.ConfigurationResiduals
open ConvergentResidualJets Filter
open scoped Topology

def nativeRealBranch (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (a : Fin 62 → ℝ) : Fin 1053 → ℝ :=
  PartialAction.pack (rawMap62 ξ hξ H (realParam (fun j => a (paramIndexEquiv j)))) -
    PartialAction.pack (literalCfg ξ)

theorem nativeRealBranch_complex (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (a : Fin 62 → ℝ) :
    (fun j => (nativeRealBranch H ξ hξ a j : ℂ)) =
      branch H ξ hξ (fun j => (a j : ℂ)) := by
  rw [branch_real_parameters]
  ext j
  simp [nativeRealBranch,AnalyticDerivative.complexPack]

theorem nativeRows_real_eval (ξ : Fin 4 → ℂ) (x : Fin 1053 → ℝ) (r : Fin 2184) :
    MvPolynomial.eval (fun j => (x j : ℂ)) (nativeRows ξ r) =
      (Option2.NativeStress.originalF (PartialAction.pack (literalCfg ξ) + x) r : ℂ) := by
  unfold nativeRows PolynomialJets.translate
  rw [← MvPolynomial.eval_assoc]
  have he : MvPolynomial.eval (fun j => (x j : ℂ)) ∘
      (fun j => MvPolynomial.X j + MvPolynomial.C
        ((PartialAction.pack (literalCfg ξ) j : ℝ) : ℂ)) =
      (fun j => ((PartialAction.pack (literalCfg ξ) + x) j : ℂ)) := by
    funext j
    simp [add_comm]
  rw [he,NativeH.Reproduction.originalF_complex,QuarticCertificate.RowBridge.eval_fRow]

theorem nativeComplexZero_real_iff (ξ : Fin 4 → ℂ) (x : Fin 1053 → ℝ) :
    NativeComplexZero ξ (fun j => (x j : ℂ)) ↔
      Option2.NativeStress.originalF (PartialAction.pack (literalCfg ξ) + x) = 0 := by
  simp only [NativeComplexZero,nativeRows_real_eval,Complex.ofReal_eq_zero]
  exact ⟨fun h => funext h, fun h r => congrFun h r⟩

/-- On an actual real neighborhood, away from the same holomorphic
multiplier, the original real zeros are exactly the retained real A5 branch.
The parameter neighborhood is retained in the conclusion. -/
theorem native_real_sheet_isolation (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) (H : Fin 4) :
    ∃ κ : (Fin 1053 → ℂ) → ℂ, AnalyticAt ℂ κ 0 ∧
      ¬ ((fun y => κ (branch H u.1 hgood.1 y)) =ᶠ[𝓝 0] 0) ∧
      ∃ P : Set (Fin 62 → ℂ), P ∈ 𝓝 0 ∧
      ∃ V : Set (Fin 1053 → ℝ), IsOpen V ∧ 0 ∈ V ∧
        ∀ x ∈ V, κ (fun j => (x j : ℂ)) ≠ 0 →
          (Option2.NativeStress.originalF (PartialAction.pack (literalCfg u.1) + x) = 0 ↔
            ∃ a : Fin 62 → ℝ, (fun j => (a j : ℂ)) ∈ P ∧
              x = nativeRealBranch H u.1 hgood.1 a) := by
  obtain ⟨κ,hκ,hnz,ρ,hρ,hρ0,_,U,hU,h0U,hiso⟩ :=
    native_complex_sheet_isolation u hgood hpivot H
  obtain ⟨P,hP,hreal⟩ := branch_real_iff_locally H u.1 hgood.1
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
  refine ⟨κ,hκ,hnz,P,hP,V,hV,h0V,?_⟩
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

#print axioms nativeRows_real_eval
#print axioms native_real_sheet_isolation
end Option2.NativeStress.PhaseRealSheetIsolationA7

module

public import NativePhaseRealSheetIsolation
public import LocalRealSliceDensity

@[expose] public section

/-! The actual branch multiplier is nonzero on an open dense set of small
real parameters, all lying inside the proved real isolation neighborhood.
This is a raw-sheet statement, not yet orbit transport or a smooth10 quotient
chart.  -/

noncomputable section
namespace Option2.NativeStress.PhaseRealSheetDensityA7
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open PhasePivotA6 PhasePivotLocusA6 PhaseAnalyticBranchesA6
open PhaseRealSheetIsolationA7 LocalRealSliceA7 NativePolynomial Filter
open scoped Topology

private theorem continuous_nativeRealBranch (H : Fin 4) (ξ : Fin 4 → ℂ)
    (hξ : IsUnitPhase ξ) : Continuous (nativeRealBranch H ξ hξ) := by
  have hc : Continuous (fun a : Fin 62 → ℝ => fun j => (a j : ℂ)) :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)
  have hb := (branch_entire H ξ hξ).continuous.comp hc
  have hr := continuous_pi fun j => Complex.continuous_re.comp ((continuous_apply j).comp hb)
  convert hr using 1
  funext a j
  exact congrArg Complex.re (congrFun (nativeRealBranch_complex H ξ hξ a) j)

private theorem nativeRealBranch_zero (H : Fin 4) (ξ : Fin 4 → ℂ)
    (hξ : IsUnitPhase ξ) : nativeRealBranch H ξ hξ 0 = 0 := by
  have h := nativeRealBranch_complex H ξ hξ 0
  simp only [Pi.zero_apply,Complex.ofReal_zero] at h
  change (fun j => (nativeRealBranch H ξ hξ 0 j : ℂ)) = branch H ξ hξ 0 at h
  rw [branch_zero] at h
  funext j
  exact Complex.ofReal_injective (congrFun h j)

theorem native_real_sheet_isolation_dense_parameters (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) (H : Fin 4) :
    ∃ κ : (Fin 1053 → ℂ) → ℂ, AnalyticAt ℂ κ 0 ∧
      ∃ r : ℝ, 0 < r ∧
        IsOpen {a : Fin 62 → ℝ | a ∈ Metric.ball 0 r ∧
          κ (fun j => (nativeRealBranch H u.1 hgood.1 a j : ℂ)) ≠ 0} ∧
        Metric.ball (0 : Fin 62 → ℝ) r ⊆
          closure {a : Fin 62 → ℝ | a ∈ Metric.ball 0 r ∧
            κ (fun j => (nativeRealBranch H u.1 hgood.1 a j : ℂ)) ≠ 0} ∧
        ∃ P : Set (Fin 62 → ℂ), P ∈ 𝓝 0 ∧
        ∃ V : Set (Fin 1053 → ℝ), IsOpen V ∧ 0 ∈ V ∧
          (∀ a ∈ Metric.ball (0 : Fin 62 → ℝ) r,
            (fun j => (a j : ℂ)) ∈ P ∧ nativeRealBranch H u.1 hgood.1 a ∈ V) ∧
          ∀ x ∈ V, κ (fun j => (x j : ℂ)) ≠ 0 →
            (Option2.NativeStress.originalF (PartialAction.pack (literalCfg u.1) + x) = 0 ↔
              ∃ a : Fin 62 → ℝ, (fun j => (a j : ℂ)) ∈ P ∧
                x = nativeRealBranch H u.1 hgood.1 a) := by
  obtain ⟨κ,hκ,hnz,P,hP,V,hV,h0V,hiso⟩ := native_real_sheet_isolation u hgood hpivot H
  have hf := hκ.comp_of_eq (branch_analyticAt H u.1 hgood.1) (branch_zero H u.1 hgood.1)
  obtain ⟨r,hr,hopen,hdense⟩ :=
    exists_real_ball_open_dense_nonzero (κ ∘ branch H u.1 hgood.1) hf hnz
  simp only [Function.comp_apply,← nativeRealBranch_complex] at hopen hdense
  have hc : Continuous (fun a : Fin 62 → ℝ => fun j => (a j : ℂ)) :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)
  have hP' : (fun a : Fin 62 → ℝ => fun j => (a j : ℂ)) ⁻¹' P ∈ 𝓝 0 := by
    apply hc.continuousAt.preimage_mem_nhds
    change P ∈ 𝓝 (0 : Fin 62 → ℂ)
    exact hP
  have hV' : nativeRealBranch H u.1 hgood.1 ⁻¹' V ∈ 𝓝 0 := by
    apply (continuous_nativeRealBranch H u.1 hgood.1).continuousAt.preimage_mem_nhds
    rw [nativeRealBranch_zero]
    exact hV.mem_nhds h0V
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.1 (inter_mem hP' hV')
  let s := min r δ
  have hs : 0 < s := lt_min hr hδ
  have hsr : Metric.ball (0 : Fin 62 → ℝ) s ⊆ Metric.ball 0 r :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hsδ : Metric.ball (0 : Fin 62 → ℝ) s ⊆ Metric.ball 0 δ :=
    Metric.ball_subset_ball (min_le_right _ _)
  have hopen' : IsOpen {a : Fin 62 → ℝ | a ∈ Metric.ball 0 s ∧
      κ (fun j => (nativeRealBranch H u.1 hgood.1 a j : ℂ)) ≠ 0} := by
    convert Metric.isOpen_ball.inter hopen using 1
    ext a
    exact ⟨fun h => ⟨h.1,hsr h.1,h.2⟩,fun h => ⟨h.1,h.2.2⟩⟩
  have hdense' : Metric.ball (0 : Fin 62 → ℝ) s ⊆
      closure {a : Fin 62 → ℝ | a ∈ Metric.ball 0 s ∧
        κ (fun j => (nativeRealBranch H u.1 hgood.1 a j : ℂ)) ≠ 0} := by
    intro a ha
    have h : a ∈ closure (Metric.ball (0 : Fin 62 → ℝ) s ∩
        {a : Fin 62 → ℝ | a ∈ Metric.ball 0 r ∧
          κ (fun j => (nativeRealBranch H u.1 hgood.1 a j : ℂ)) ≠ 0}) :=
      (show IsOpen (Metric.ball (0 : Fin 62 → ℝ) s) from Metric.isOpen_ball).inter_closure
        (show a ∈ Metric.ball (0 : Fin 62 → ℝ) s ∩ closure
          {a : Fin 62 → ℝ | a ∈ Metric.ball 0 r ∧
            κ (fun j => (nativeRealBranch H u.1 hgood.1 a j : ℂ)) ≠ 0} from
          ⟨ha,hdense (hsr ha)⟩)
    refine closure_mono ?_ h
    intro x hx
    exact ⟨hx.1,hx.2.2⟩
  exact ⟨κ,hκ,s,hs,hopen',hdense',P,hP,V,hV,h0V,
    fun a ha => hδsub (hsδ ha),hiso⟩

#print axioms native_real_sheet_isolation_dense_parameters
end Option2.NativeStress.PhaseRealSheetDensityA7

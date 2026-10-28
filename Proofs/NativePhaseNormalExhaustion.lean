module

public import NativePhaseFullNormalBound

@[expose] public section

/-! Exact normal zero exhaustion by the four genuine local native families.
The reverse inclusion uses the original native family residual germ; it does
not infer membership from vanishing distance to a possibly nonclosed image. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.PhaseNormalExhaustion
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeSliceNormalSplitting CKM.NativeSliceImplicitReduction
open BookHT PhaseSheetChart PhaseRangeReduction PhaseSheetDistance PhaseFullNormalBound
open Filter Topology
variable {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)

theorem local_normal_zero_iff_family :
    ∃ V0 : Fin 4 → Set SliceParam, (∀ i, V0 i ∈ 𝓝 0) ∧
      ∀ (V : Fin 4 → Set SliceParam), (∀ i, V i ∈ 𝓝 0) → (∀ i, V i ⊆ V0 i) →
        ∃ δ : ℝ, 0 < δ ∧ ∀ n : Normal ξ, ‖n‖ < δ → n ∈ (reducedPH hξ).target ∧
          (AnalyticDerivative.originalF (literalCfg ξ + (n : Cfg)) = 0 ↔
            literalCfg ξ + (n : Cfg) ∈ actualFamilyUnion hξ V) := by
  let V0 : Fin 4 → Set SliceParam := fun i =>
    {p | AnalyticDerivative.originalF (literalCfg ξ + (sliceFam ξ hξ.1 i p : Cfg)) = 0}
  have hV0 (i : Fin 4) : V0 i ∈ 𝓝 0 := eventually_originalF_sliceFam hξ.1 i
  refine ⟨V0,hV0,?_⟩
  intro V hV hsub
  obtain ⟨r,hr,hzero⟩ := local_normal_zero_iff hξ
  have ht : Tendsto (fun n : Normal ξ => ((reducedPH hξ).symm n).1) (𝓝 0) (𝓝 0) := by
    simpa only [reducedPH_symm_zero,Prod.fst_zero] using
      (reducedPH_symm_C2 hξ).continuousAt.fst.tendsto
  have hfamilies : ∀ᶠ n : Normal ξ in 𝓝 0, ∀ i : Fin 4,
      FourBlock.OnAxis i ((reducedPH hξ).symm n).1.2 →
        ambientMap hξ ((reducedPH hξ).symm n).1 ∈
          (fun p => literalCfg ξ + (sliceFam ξ hξ.1 i p : Cfg)) '' V i :=
    ht.eventually (Filter.eventually_all.mpr fun i => axis_image_near hξ i (V i) (hV i))
  have hnear : ∀ᶠ n : Normal ξ in 𝓝 0, n ∈ (reducedPH hξ).target ∧
      (AnalyticDerivative.originalF (literalCfg ξ + (n : Cfg)) = 0 ↔
        literalCfg ξ + (n : Cfg) ∈ actualFamilyUnion hξ V) := by
    filter_upwards [Metric.ball_mem_nhds (0 : Normal ξ) hr,hfamilies] with n hn hf
    obtain ⟨hnt,hz⟩ := hzero n (by simpa only [Metric.mem_ball,dist_zero_right] using hn)
    refine ⟨hnt,?_,?_⟩
    · intro h
      obtain ⟨hq,i,hi⟩ := hz.mp h
      have he : (((reducedPH hξ).symm n).1,(0 : normalRange ξ)) = (reducedPH hξ).symm n :=
        Prod.ext rfl hq.symm
      have ha : ambientMap hξ ((reducedPH hξ).symm n).1 = literalCfg ξ + (n : Cfg) := by
        change literalCfg ξ + (reducedPH hξ (((reducedPH hξ).symm n).1,0) : Cfg) = _
        rw [he,(reducedPH hξ).right_inv hnt]
      exact Set.mem_iUnion.mpr ⟨i,ha ▸ hf i hi⟩
    · intro h
      obtain ⟨i,p,hp,hpn⟩ := Set.mem_iUnion.mp h
      have hp0 : AnalyticDerivative.originalF (literalCfg ξ + (sliceFam ξ hξ.1 i p : Cfg)) = 0 :=
        hsub i hp
      exact (congrArg AnalyticDerivative.originalF hpn).symm.trans hp0
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp hnear
  exact ⟨δ,hδ,fun n hn => hd (by simpa only [Metric.mem_ball,dist_zero_right] using hn)⟩

end Option2.NativeStress.PhaseNormalExhaustion
#print axioms Option2.NativeStress.PhaseNormalExhaustion.local_normal_zero_iff_family

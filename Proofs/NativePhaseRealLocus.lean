module

public import NativePhaseRealSliceNormalForm
public import Mathlib.Analysis.Calculus.FDeriv.Star

@[expose] public section

/-! The actual centered branch has real output locally exactly at real
parameters. Conjugation symmetry comes from the proved entire real slice;
the converse uses the existing local inverse chart, not global injectivity.
Only the retained branch image is identified with the actual real family. -/

noncomputable section
namespace Option2.NativeStress.PhaseRealLocusA6
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open PhaseEntireFamilyA6 PhaseAnalyticBranchesA6 PhaseRealSliceNormalFormA6
open Filter Set
open scoped Topology

private theorem star_eq_of_im_zero {σ : Type*} (z : σ → ℂ)
    (hz : ∀ j, (z j).im = 0) : star z = z := by
  funext j
  exact Complex.conj_eq_iff_im.mpr (hz j)

private theorem ofReal_re_eq_of_im_zero {σ : Type*} (z : σ → ℂ)
    (hz : ∀ j, (z j).im = 0) : (fun j => ((z j).re : ℂ)) = z := by
  funext j
  apply Complex.ext
  · rfl
  · exact (hz j).symm

private theorem entire_realSlice_commutes_star {σ τ : Type*} [Fintype σ] [Fintype τ]
    (F : (σ → ℂ) → (τ → ℂ)) (hF : Differentiable ℂ F)
    (hreal : ∀ x : σ → ℝ, ∀ j, (F (fun i => (x i : ℂ)) j).im = 0)
    (z : σ → ℂ) : F (star z) = star (F z) := by
  have hs : Differentiable ℂ (star ∘ F ∘ star) := by
    intro w
    simpa only [star_star] using (hF (star w)).star_star
  have he (w : σ → ℂ) : F w = star (F (star w)) := by
    funext j
    apply sub_eq_zero.mp
    apply EntireRealSliceA6.entire_zero_of_real_slice
      (fun v => F v j - (star (F (star v))) j) ?_ ?_ w
    · exact ((ContinuousLinearMap.proj j).differentiable.comp hF).sub
        ((ContinuousLinearMap.proj j).differentiable.comp hs)
    · intro x
      have hx : star (fun i => (x i : ℂ)) = (fun i => (x i : ℂ)) := by
        funext i
        simp
      rw [hx, star_eq_of_im_zero _ (hreal x)]
      exact sub_self _
  simpa only [star_star] using he (star z)

theorem branch_real_ofReal (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (x : Fin 62 → ℝ) : ∀ k, (branch H ξ hξ (fun j => (x j : ℂ)) k).im = 0 := by
  intro k
  rw [branch_real_parameters]
  simp only [Pi.sub_apply, Complex.sub_im, Complex.ofReal_im,
    AnalyticDerivative.complexPack, sub_self]

theorem branch_star (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (z : Fin 62 → ℂ) : branch H ξ hξ (star z) = star (branch H ξ hξ z) :=
  entire_realSlice_commutes_star (branch H ξ hξ) (branch_entire H ξ hξ)
    (branch_real_ofReal H ξ hξ) z

/-- Each actual branch is real-valued near zero exactly at real parameters. -/
theorem branch_real_iff_locally (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    ∃ U : Set (Fin 62 → ℂ), U ∈ 𝓝 0 ∧
      ∀ z ∈ U, (∀ k, (branch H ξ hξ z k).im = 0) ↔ ∀ j, (z j).im = 0 := by
  obtain ⟨L,hL⟩ := branchDerivative_leftInverse H ξ hξ
  let e := AnalyticPullback.chart (branch H ξ hξ) (branch_analyticAt H ξ hξ)
    (branch_hasFDerivAt H ξ hξ) hL
  have he0 : (0 : Fin 62 → ℂ) ∈ e.source :=
    AnalyticPullback.zero_mem_chart_source _ _ _ hL
  have hsource : e.source ∈ 𝓝 (0 : Fin 62 → ℂ) := e.open_source.mem_nhds he0
  have hstar : Tendsto (star : (Fin 62 → ℂ) → (Fin 62 → ℂ)) (𝓝 0) (𝓝 0) := by
    simpa only [star_zero] using tendsto_star (0 : Fin 62 → ℂ)
  refine ⟨e.source ∩ star ⁻¹' e.source, inter_mem hsource (hstar hsource), ?_⟩
  intro z hz
  constructor
  · intro hreal
    have hb : branch H ξ hξ (star z) = branch H ξ hξ z :=
      (branch_star H ξ hξ z).trans (star_eq_of_im_zero _ hreal)
    have heq : e (star z) = e z := by
      change L (branch H ξ hξ (star z)) = L (branch H ξ hξ z)
      exact congrArg L hb
    have hzstar : star z = z := e.injOn hz.2 hz.1 heq
    intro j
    exact Complex.conj_eq_iff_im.mp (congrFun hzstar j)
  · intro hreal
    have hzreal := ofReal_re_eq_of_im_zero z hreal
    rw [← hzreal]
    exact branch_real_ofReal H ξ hξ (fun j => (z j).re)

/-- The real locus of the retained local branch image is exactly the actual
centered packed A5 raw family at the retained real parameters. -/
theorem branch_local_real_locus_eq_real_family
    (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    ∃ U : Set (Fin 62 → ℂ), U ∈ 𝓝 0 ∧
      (branch H ξ hξ '' U) ∩ {y : Fin 1053 → ℂ | ∀ k, (y k).im = 0} =
        (fun x : Fin 62 → ℝ =>
          (fun k => ((NativePolynomial.PartialAction.pack
            (rawMap62 ξ hξ H (realParam (fun j => x (paramIndexEquiv j)))) k : ℝ) : ℂ)) -
            AnalyticDerivative.complexPack (literalCfg ξ)) ''
          {x : Fin 62 → ℝ | (fun j => (x j : ℂ)) ∈ U} := by
  obtain ⟨U,hU,hiff⟩ := branch_real_iff_locally H ξ hξ
  refine ⟨U,hU,?_⟩
  ext y
  constructor
  · rintro ⟨⟨z,hz,rfl⟩,hreal⟩
    have hzreal := (hiff z hz).mp hreal
    have hx := ofReal_re_eq_of_im_zero z hzreal
    refine ⟨(fun j => (z j).re), ?_, ?_⟩
    · change (fun j => ((z j).re : ℂ)) ∈ U
      rw [hx]
      exact hz
    · exact (branch_real_parameters H ξ hξ (fun j => (z j).re)).symm.trans
        (congrArg (branch H ξ hξ) hx)
  · rintro ⟨x,hx,rfl⟩
    have hr := branch_real_parameters H ξ hξ x
    refine ⟨⟨(fun j => (x j : ℂ)),hx,hr⟩,?_⟩
    simp only [Set.mem_setOf_eq]
    rw [← hr]
    exact branch_real_ofReal H ξ hξ x

#print axioms Option2.NativeStress.PhaseRealLocusA6.branch_star
#print axioms Option2.NativeStress.PhaseRealLocusA6.branch_real_iff_locally
#print axioms Option2.NativeStress.PhaseRealLocusA6.branch_local_real_locus_eq_real_family
end Option2.NativeStress.PhaseRealLocusA6

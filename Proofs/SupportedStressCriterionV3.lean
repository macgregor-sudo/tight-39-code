module

public import FirstBlockLimitV3
public import NearestBlockGeometry
public import SecondNormalLimitV2
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# Quantitative supported-stress local criterion

Source-only assembly of the original FULL-CRITERION-CONTRACT.md target.
FirstBlockLimitV3, NearestBlockGeometry and SecondNormalLimitV2 supply the
two limit arguments and nearest-block geometry. No native chart is assumed implicitly.
-/

open Filter
open scoped Topology

namespace SupportedStress

theorem supported_stress_local_criterion
    {ι C E Z : Type*} [Fintype ι]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (W : ι → Submodule ℝ E)
    (horth : Pairwise (fun i j => (W i).IsOrtho (W j)))
    (hspan : (⨆ i, W i) = ⊤)
    (f : C × E → Z) (U : Set (C × E))
    (hU : IsOpen U) (hOrigin : (0 : C × E) ∈ U)
    (hf : ContDiffOn ℝ 2 f U)
    (hsheets : ∀ (i : ι) (c : C) (a : E),
      (c, a) ∈ U → a ∈ W i → f (c, a) = 0)
    (hcone : ∀ a : E,
      transverseQuadraticPart f a = 0 ↔ a ∈ blockUnion W)
    (hstress : ∀ (i : ι) (w : W i), ‖w‖ = 1 →
      ∃ V : Set (C × W i), IsOpen V ∧ (0 : C × W i) ∈ V ∧
        (∀ p ∈ V, (p.1, (p.2 : E)) ∈ U) ∧
        ∃ ell : C × W i → Z →L[ℝ] ℝ,
          ContinuousOn ell V ∧
          (∀ p ∈ V, ∀ n ∈ (W i).orthogonal,
            ell p ((fderiv ℝ f (p.1, (p.2 : E))) (0, n)) = 0) ∧
          (∀ v ∈ (W i).orthogonal, v ≠ 0 →
            (fderiv ℝ (transverseQuadraticPart f) (w : E)) v = 0 →
            0 < ell (0 : C × W i) (transverseQuadraticPart f v))) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      ∀ (c : C) (u : E), ‖c‖ < r → ‖u‖ < r →
        (c, u) ∈ U ∧
        Metric.infDist u (blockUnion W) ^ 2 ≤ M * ‖f (c, u)‖ ∧
        (f (c, u) = 0 ↔ u ∈ blockUnion W) := by
  classical
  let S : Set E := blockUnion W
  have hSzero : (0 : E) ∈ S := by
    apply (hcone 0).mp
    change (1 / 2 : ℝ) • (fderiv ℝ (fderiv ℝ f) (0 : C × E))
      (0 : C × E) (0 : C × E) = 0
    simp only [map_zero, zero_apply, smul_zero]
  have hSnonempty : S.Nonempty := ⟨0, hSzero⟩
  have hQcontinuous : Continuous (transverseQuadraticPart f) := by
    let H : (C × E) →L[ℝ] (C × E) →L[ℝ] Z :=
      fderiv ℝ (fderiv ℝ f) (0 : C × E)
    have hI : Continuous (fun a : E => ((0 : C), a)) :=
      continuous_const.prodMk continuous_id
    change Continuous (fun a : E => (1 / 2 : ℝ) • H (0, a) (0, a))
    exact continuous_const.smul ((H.continuous.comp hI).clm_apply hI)
  have hSclosed : IsClosed S := by
    have heq : S = (transverseQuadraticPart f) ⁻¹' ({0} : Set Z) := by
      ext a
      change a ∈ S ↔ transverseQuadraticPart f a = 0
      exact (hcone a).symm
    rw [heq]
    exact isClosed_singleton.preimage hQcontinuous
  have hzero : ∀ c : C, (c, (0 : E)) ∈ U → f (c, 0) = 0 := by
    have hz : (0 : E) ∈ ⋃ i, (W i : Set E) := hSzero
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    intro c hc
    exact hsheets i c 0 hc hi
  have hpartial : ∀ c : C, (c, (0 : E)) ∈ U →
      ∀ v : E, (fderiv ℝ f (c, 0)) (0, v) = 0 := by
    intro c hc
    let D : E →L[ℝ] Z :=
      (fderiv ℝ f (c, 0)).comp (ContinuousLinearMap.inr ℝ C E)
    have hDF : HasFDerivAt f (fderiv ℝ f (c, 0)) (c, 0) :=
      ((hf.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hc)).hasFDerivAt
    have hWi : ∀ i, W i ≤ LinearMap.ker D.toLinearMap := by
      intro i v hv
      change D v = 0
      let J : W i →L[ℝ] C × E :=
        (0 : W i →L[ℝ] C).prod (W i).subtypeL
      have hinc : HasFDerivAt (fun y : W i => (c, (y : E))) J (0 : W i) :=
        (hasFDerivAt_const c (0 : W i)).prodMk ((W i).subtypeL.hasFDerivAt)
      have hslice : HasFDerivAt (fun y : W i => f (c, (y : E)))
          ((fderiv ℝ f (c, 0)).comp J) (0 : W i) := by
        simpa only [Function.comp_def] using hDF.comp (0 : W i) hinc
      have hlocal : (fun y : W i => f (c, (y : E))) =ᶠ[𝓝 (0 : W i)]
          (fun _ => (0 : Z)) := by
        have hcont : Continuous (fun y : W i => (c, (y : E))) :=
          continuous_const.prodMk continuous_subtype_val
        filter_upwards [(hcont.tendsto (0 : W i)).eventually (hU.mem_nhds hc)] with y hy
        exact hsheets i c y hy y.property
      have hflat : HasFDerivAt (fun y : W i => f (c, (y : E)))
          (0 : W i →L[ℝ] Z) (0 : W i) :=
        hasFDerivAt_zero_of_eventually_const (0 : Z) hlocal
      have heq := hslice.unique hflat
      have heval := congrArg (fun L : W i →L[ℝ] Z => L ⟨v, hv⟩) heq
      change (fderiv ℝ f (c, 0)) (0, v) = 0 at heval
      exact heval
    have hker : (⨆ i, W i) ≤ LinearMap.ker D.toLinearMap := iSup_le hWi
    rw [hspan] at hker
    intro v
    exact hker (Submodule.mem_top : v ∈ (⊤ : Submodule ℝ E))
  have hBound : ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      ∀ (c : C) (u : E), ‖c‖ < r → ‖u‖ < r →
        Metric.infDist u S ^ 2 ≤ M * ‖f (c, u)‖ := by
    by_contra hNo
    have hbad : ∀ r : ℝ, 0 < r → ∀ M : ℝ, 0 < M →
        ∃ c : C, ∃ u : E, ‖c‖ < r ∧ ‖u‖ < r ∧
          M * ‖f (c, u)‖ < Metric.infDist u S ^ 2 := by
      intro r hr M hM
      by_contra hnone
      apply hNo
      refine ⟨r, M, hr, hM, ?_⟩
      intro c u hc hu
      by_contra hfail
      exact hnone ⟨c, u, hc, hu, lt_of_not_ge hfail⟩
    let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
    have hεpos : ∀ k, 0 < ε k := by
      intro k
      exact one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) zero_lt_one)
    have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    choose c u hcu using fun k =>
      hbad (ε k) (hεpos k) (1 / ε k) (one_div_pos.mpr (hεpos k))
    have hc : Tendsto c atTop (𝓝 (0 : C)) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr
        (squeeze_zero (fun k => norm_nonneg (c k)) (fun k => (hcu k).1.le) hε)
    have hu : Tendsto u atTop (𝓝 (0 : E)) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr
        (squeeze_zero (fun k => norm_nonneg (u k)) (fun k => (hcu k).2.1.le) hε)
    have haway : ∀ k, u k ∉ S := by
      intro k hk
      have hdist := Metric.infDist_zero_of_mem hk
      have hbadk := (hcu k).2.2
      have hnonneg : 0 ≤ (1 / ε k) * ‖f (c k, u k)‖ :=
        mul_nonneg (one_div_nonneg.mpr (hεpos k).le) (norm_nonneg _)
      have hbadzero : (1 / ε k) * ‖f (c k, u k)‖ < 0 := by
        simpa only [hdist, pow_two, zero_mul] using hbadk
      exact (not_lt_of_ge hnonneg) hbadzero
    have hne : ∀ k, u k ≠ 0 := by
      intro k hk
      apply haway k
      simpa only [hk] using hSzero
    have hdistPos : ∀ k, 0 < Metric.infDist (u k) S := fun k =>
      (hSclosed.notMem_iff_infDist_pos hSnonempty).mp (haway k)
    have hratio : ∀ k, ‖f (c k, u k)‖ / Metric.infDist (u k) S ^ 2 < ε k := by
      intro k
      have hdiv : ‖f (c k, u k)‖ / ε k < Metric.infDist (u k) S ^ 2 := by
        simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using (hcu k).2.2
      have hnum := (div_lt_iff₀ (hεpos k)).mp hdiv
      apply (div_lt_iff₀ (pow_pos (hdistPos k) 2)).mpr
      simpa only [mul_comm] using hnum
    have hresidual : Tendsto (fun k =>
        ‖f (c k, u k)‖ / Metric.infDist (u k) S ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun k => div_nonneg (norm_nonneg _) (sq_nonneg _))
        (fun k => (hratio k).le) hε
    obtain ⟨i, w, hwi, hwunit, φ, hφ, hfirst⟩ :=
      nonlinear_residual_first_block_limit W f U hU hOrigin hf hzero hpartial
        hcone c u hc hu haway hresidual
    let u₁ : ℕ → E := fun k => u (φ k)
    let c₁ : ℕ → C := fun k => c (φ k)
    have hu₁ : Tendsto u₁ atTop (𝓝 (0 : E)) := hu.comp hφ.tendsto_atTop
    have hc₁ : Tendsto c₁ atTop (𝓝 (0 : C)) := hc.comp hφ.tendsto_atTop
    have hne₁ : ∀ k, u₁ k ≠ 0 := fun k => hne (φ k)
    obtain ⟨hnearest, hnormalRatio, hprojected, hnormalMem⟩ :=
      eventually_nearest_block_and_normal_rescaling W horth i w hwi hwunit u₁ hne₁ hfirst
    let P : E →L[ℝ] E := (W i).starProjection
    let A : ℕ → E := fun k => P (u₁ k)
    let N : ℕ → E := fun k => u₁ k - A k
    let α : ℕ → ℝ := fun k => ‖A k‖ / ‖u₁ k‖
    have hA : Tendsto A atTop (𝓝 (0 : E)) := by
      simpa only [Function.comp_def, A, map_zero] using
        (P.continuous.tendsto (0 : E)).comp hu₁
    have hN : Tendsto N atTop (𝓝 (0 : E)) := by
      simpa only [Pi.sub_def, N, sub_zero] using hu₁.sub hA
    have hα : Tendsto α atTop (𝓝 (1 : ℝ)) := by
      simpa only [α, norm_smul, norm_inv, norm_norm, hwunit, div_eq_mul_inv, mul_comm]
        using hprojected.norm
    have hAevent : ∀ᶠ k in atTop, A k ≠ 0 := by
      filter_upwards [hα.eventually (Ioi_mem_nhds zero_lt_one)] with k hk
      have hpos : 0 < ‖A k‖ / ‖u₁ k‖ := hk
      intro hzeroA
      rw [hzeroA, norm_zero, zero_div] at hpos
      exact (lt_irrefl (0 : ℝ)) hpos
    have hNne : ∀ k, N k ≠ 0 := by
      intro k hk
      apply haway (φ k)
      have heq : u₁ k = A k := sub_eq_zero.mp hk
      change u₁ k ∈ blockUnion W
      rw [heq]
      exact Set.mem_iUnion.mpr ⟨i, (W i).starProjection_apply_mem (u₁ k)⟩
    have hgood : ∀ᶠ k in atTop,
        A k ≠ 0 ∧ Metric.infDist (u₁ k) S = ‖N k‖ := by
      filter_upwards [hAevent, hnearest] with k hkA hkNear
      exact ⟨hkA, hkNear.2⟩
    obtain ⟨ψ, hψ, hψgood⟩ := extraction_of_eventually_atTop hgood
    let a₂ : ℕ → W i := fun k =>
      ⟨A (ψ k), (W i).starProjection_apply_mem (u₁ (ψ k))⟩
    let n₂ : ℕ → E := fun k => N (ψ k)
    let c₂ : ℕ → C := fun k => c₁ (ψ k)
    have ha₂ : Tendsto a₂ atTop (𝓝 (0 : W i)) :=
      tendsto_subtype_rng.mpr (hA.comp hψ.tendsto_atTop)
    have hn₂ : Tendsto n₂ atTop (𝓝 (0 : E)) := hN.comp hψ.tendsto_atTop
    have hc₂ : Tendsto c₂ atTop (𝓝 (0 : C)) := hc₁.comp hψ.tendsto_atTop
    have ha₂ne : ∀ k, (a₂ k : E) ≠ 0 := fun k => (hψgood k).1
    have hn₂ne : ∀ k, n₂ k ≠ 0 := fun k => hNne (ψ k)
    have hn₂mem : ∀ k, n₂ k ∈ (W i).orthogonal := fun k => hnormalMem (ψ k)
    have hdir₂ : Tendsto (fun k => (‖(a₂ k : E)‖⁻¹ : ℝ) • (a₂ k : E))
        atTop (𝓝 w) := by
      have h := ((hα.inv₀ one_ne_zero).smul hprojected).comp hψ.tendsto_atTop
      have h' : Tendsto (fun k => (α (ψ k))⁻¹ •
          ((‖u₁ (ψ k)‖⁻¹ : ℝ) • A (ψ k))) atTop (𝓝 w) := by
        simpa only [Function.comp_def, inv_one, one_smul] using h
      apply h'.congr'
      exact Filter.Eventually.of_forall (fun k => by
        change (α (ψ k))⁻¹ • ((‖u₁ (ψ k)‖⁻¹ : ℝ) • A (ψ k)) =
          (‖A (ψ k)‖⁻¹ : ℝ) • A (ψ k)
        rw [smul_smul]
        congr 1
        dsimp [α]
        field_simp [norm_ne_zero_iff.mpr (hne₁ (ψ k)),
          norm_ne_zero_iff.mpr (hψgood k).1])
    have hsep₂ : Tendsto (fun k => ‖n₂ k‖ / ‖(a₂ k : E)‖) atTop (𝓝 0) := by
      have h := (hnormalRatio.div hα one_ne_zero).comp hψ.tendsto_atTop
      have h' : Tendsto (fun k => (‖N (ψ k)‖ / ‖u₁ (ψ k)‖) /
          (‖A (ψ k)‖ / ‖u₁ (ψ k)‖)) atTop (𝓝 (0 : ℝ)) := by
        simpa only [Function.comp_def, Pi.div_def, α, zero_div] using h
      apply h'.congr'
      exact Filter.Eventually.of_forall (fun k => by
        change (‖N (ψ k)‖ / ‖u₁ (ψ k)‖) / (‖A (ψ k)‖ / ‖u₁ (ψ k)‖) =
          ‖N (ψ k)‖ / ‖A (ψ k)‖
        field_simp [norm_ne_zero_iff.mpr (hne₁ (ψ k)),
          norm_ne_zero_iff.mpr (hψgood k).1])
    have hres₂ : Tendsto (fun k =>
        ‖f (c₂ k, (a₂ k : E) + n₂ k)‖ / ‖n₂ k‖ ^ 2) atTop (𝓝 0) := by
      have h := (hresidual.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
      apply h.congr'
      exact Filter.Eventually.of_forall (fun k => by
        have hsum : (a₂ k : E) + n₂ k = u₁ (ψ k) := by
          change A (ψ k) + (u₁ (ψ k) - A (ψ k)) = u₁ (ψ k)
          module
        change ‖f (c₁ (ψ k), u₁ (ψ k))‖ / Metric.infDist (u₁ (ψ k)) S ^ 2 =
          ‖f (c₂ k, (a₂ k : E) + n₂ k)‖ / ‖n₂ k‖ ^ 2
        rw [(hψgood k).2, hsum])
    obtain ⟨V, hV, hVzero, hVU, ell, hell, hann, hpositive⟩ :=
      hstress i ⟨w, hwi⟩ hwunit
    have hsheet : ∀ p ∈ V, f (p.1, (p.2 : E)) = 0 := by
      intro p hp
      exact hsheets i p.1 p.2 (hVU p hp) p.2.property
    exact second_normal_limit_stress_contradiction (W i) f U hU hOrigin hf hpartial
      w hwi hwunit V hV hVzero hsheet ell hell hann hpositive
      c₂ a₂ n₂ hc₂ ha₂ hn₂ ha₂ne hn₂ne hn₂mem hdir₂ hsep₂ hres₂
  obtain ⟨r₀, M, hr₀, hM, hestimate⟩ := hBound
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hOrigin)
  refine ⟨min r₀ ρ, M, lt_min hr₀ hρ, hM, ?_⟩
  intro c u hc hu
  have hc₀ : ‖c‖ < r₀ := hc.trans_le (min_le_left r₀ ρ)
  have hu₀ : ‖u‖ < r₀ := hu.trans_le (min_le_left r₀ ρ)
  have hmem : (c, u) ∈ U := by
    apply hρU
    change dist (c, u) (0 : C × E) < ρ
    rw [dist_zero_right, Prod.norm_mk]
    exact max_lt (hc.trans_le (min_le_right r₀ ρ)) (hu.trans_le (min_le_right r₀ ρ))
  have hbound := hestimate c u hc₀ hu₀
  refine ⟨hmem, hbound, ?_⟩
  constructor
  · intro hzeroF
    have hdist0 : Metric.infDist u S = 0 := by
      rw [hzeroF, norm_zero, mul_zero] at hbound
      nlinarith [sq_nonneg (Metric.infDist u S)]
    exact (hSclosed.mem_iff_infDist_zero hSnonempty).mpr hdist0
  · intro huS
    obtain ⟨i, hui⟩ := Set.mem_iUnion.mp huS
    exact hsheets i c u hmem hui

end SupportedStress

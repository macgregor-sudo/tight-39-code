module

public import MovingBaseC2Remainder
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Topology.Sequences
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Second normal limit and the supported-stress contradiction

Lean 4.35.0-rc2 / Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
The moving-base C² estimate supplies the Taylor remainder in the second normal limit.
The sequence premises are the output interface after nearest-block selection
and tail restriction. No kernel limit, Taylor error limit or stress conclusion
is assumed. The common transverse derivative-zero premise remains preparatory.
-/

open Filter Asymptotics
open scoped Topology

namespace SupportedStress

theorem second_normal_limit_stress_contradiction
    {C E Z : Type*}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (K : Submodule ℝ E) (F : C × E → Z) (U : Set (C × E))
    (hU : IsOpen U) (hOrigin : (0 : C × E) ∈ U) (hF : ContDiffOn ℝ 2 F U)
    (hpartial : ∀ c : C, (c, (0 : E)) ∈ U →
      ∀ v : E, (fderiv ℝ F (c, 0)) (0, v) = 0)
    (w : E) (hw : w ∈ K) (hwunit : ‖w‖ = 1)
    (V : Set (C × K)) (hV : IsOpen V) (hVzero : (0 : C × K) ∈ V)
    (hsheet : ∀ p ∈ V, F (p.1, (p.2 : E)) = 0)
    (ell : C × K → Z →L[ℝ] ℝ) (hell : ContinuousOn ell V)
    (hann : ∀ p ∈ V, ∀ v ∈ K.orthogonal,
      ell p ((fderiv ℝ F (p.1, (p.2 : E))) (0, v)) = 0)
    (hpositive : ∀ v ∈ K.orthogonal, v ≠ 0 →
      (fderiv ℝ (fun x : E => (1 / 2 : ℝ) •
        (fderiv ℝ (fderiv ℝ F) (0 : C × E)) (0, x) (0, x)) w) v = 0 →
      0 < ell (0 : C × K) ((1 / 2 : ℝ) •
        (fderiv ℝ (fderiv ℝ F) (0 : C × E)) (0, v) (0, v)))
    (c : ℕ → C) (a : ℕ → K) (n : ℕ → E)
    (hc : Tendsto c atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 0))
    (hn : Tendsto n atTop (𝓝 0))
    (hane : ∀ k, (a k : E) ≠ 0) (hnne : ∀ k, n k ≠ 0)
    (hnormal : ∀ k, n k ∈ K.orthogonal)
    (hadir : Tendsto (fun k => (‖(a k : E)‖⁻¹ : ℝ) • (a k : E)) atTop (𝓝 w))
    (hsep : Tendsto (fun k => ‖n k‖ / ‖(a k : E)‖) atTop (𝓝 0))
    (hresidual : Tendsto (fun k => ‖F (c k, (a k : E) + n k)‖ / ‖n k‖ ^ 2)
      atTop (𝓝 0)) : False := by
  let H : (C × E) →L[ℝ] (C × E) →L[ℝ] Z :=
    fderiv ℝ (fderiv ℝ F) (0 : C × E)
  let Q : E → Z := fun x => (1 / 2 : ℝ) • H (0, x) (0, x)
  let t : ℕ → ℝ := fun k => ‖(a k : E)‖
  let s : ℕ → ℝ := fun k => ‖n k‖
  let A : ℕ → E := fun k => (t k)⁻¹ • (a k : E)
  let N : ℕ → E := fun k => (s k)⁻¹ • n k
  let b : ℕ → C × E := fun k => (c k, (a k : E))
  let d : ℕ → C × E := fun k => (0, n k)
  let p : ℕ → C × K := fun k => (c k, a k)
  have htpos : ∀ k, 0 < t k := fun k => norm_pos_iff.mpr (hane k)
  have hspos : ∀ k, 0 < s k := fun k => norm_pos_iff.mpr (hnne k)
  have hInorm : ∀ x : E, ‖((0 : C), x)‖ = ‖x‖ := by
    intro x
    simp [Prod.norm_mk]
  have haE : Tendsto (fun k => (a k : E)) atTop (𝓝 (0 : E)) :=
    (continuous_subtype_val.tendsto (0 : K)).comp ha
  have hb : Tendsto b atTop (𝓝 (0 : C × E)) := hc.prodMk_nhds haE
  have hd : Tendsto d atTop (𝓝 (0 : C × E)) := tendsto_const_nhds.prodMk_nhds hn
  have hp : Tendsto p atTop (𝓝 (0 : C × K)) := hc.prodMk_nhds ha
  have hpV : ∀ᶠ k in atTop, p k ∈ V := hp.eventually (hV.mem_nhds hVzero)
  have hcb : Tendsto (fun k => (c k, (0 : E))) atTop (𝓝 (0 : C × E)) :=
    hc.prodMk_nhds tendsto_const_nhds
  have hcbU : ∀ᶠ k in atTop, (c k, (0 : E)) ∈ U :=
    hcb.eventually (hU.mem_nhds hOrigin)
  have hFd : ContDiffOn ℝ 1 (fderiv ℝ F) U :=
    hF.fderiv_of_isOpen hU (by norm_num)
  have hstrict : HasStrictFDerivAt (fderiv ℝ F) H (0 : C × E) :=
    (hFd.contDiffAt (hU.mem_nhds hOrigin)).hasStrictFDerivAt one_ne_zero
  have hsym : ∀ x y : C × E, H x y = H y x :=
    (hF.contDiffAt (hU.mem_nhds hOrigin)).isSymmSndFDerivAt (by simp)
  have hQcont : Continuous Q :=
    continuous_const.smul
      ((H.continuous.comp (continuous_const.prodMk continuous_id)).clm_apply
        (continuous_const.prodMk continuous_id))
  have hQhom : ∀ (r : ℝ) (x : E), Q (r • x) = r ^ 2 • Q x := by
    intro r x
    have hi : ((0 : C), r • x) = r • ((0 : C), x) := by simp
    dsimp [Q]
    simp only [hi, map_smul, ContinuousLinearMap.smul_apply, smul_smul]
    congr 1
    ring
  have hQscale : ∀ k, (s k ^ 2)⁻¹ • Q (n k) = Q (N k) := by
    intro k
    dsimp [N]
    rw [hQhom, inv_pow]
  let err : ℕ → Z := fun k => F (c k, (a k : E) + n k) - F (b k) -
    (fderiv ℝ F (b k)) (d k) - Q (n k)
  have herrSmall : err =o[atTop] (fun k => s k ^ 2) := by
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    obtain ⟨r, hr, hrem⟩ := local_c2_uniform_moving_base_remainder
      F U hU hOrigin hF ε hε
    have hbr := hb.eventually (Metric.ball_mem_nhds (0 : C × E) hr)
    have hdr := hd.eventually (Metric.ball_mem_nhds (0 : C × E) hr)
    filter_upwards [hbr, hdr] with k hbk hdk
    have hbkn : ‖b k‖ < r := by
      simpa only [Metric.mem_ball, dist_zero_right] using hbk
    have hdkn : ‖d k‖ < r := by
      simpa only [Metric.mem_ball, dist_zero_right] using hdk
    have hremk := hrem (b k) (d k) hbkn hdkn
    have hbd : b k + d k = (c k, (a k : E) + n k) := by simp [b, d]
    have habs : |‖n k‖ ^ 2| = ‖n k‖ ^ 2 := abs_of_nonneg (sq_nonneg (‖n k‖ : ℝ))
    simpa only [hbd, d, hInorm, err, Q, H, s, Real.norm_eq_abs,
      habs] using hremk
  let R : ℕ → Z := fun k => (s k ^ 2)⁻¹ • err k
  let Y : ℕ → Z := fun k => (s k ^ 2)⁻¹ • F (c k, (a k : E) + n k)
  let L : ℕ → Z := fun k => (s k ^ 2)⁻¹ • (fderiv ℝ F (b k)) (d k)
  let X : ℕ → Z := fun k => (t k)⁻¹ • (fderiv ℝ F (b k)) (0, N k)
  have hR : Tendsto R atTop (𝓝 (0 : Z)) := herrSmall.tendsto_inv_smul_nhds_zero
  have hY : Tendsto Y atTop (𝓝 (0 : Z)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have habs : ∀ k : ℕ, |‖n k‖ ^ 2| = ‖n k‖ ^ 2 :=
      fun k => abs_of_nonneg (sq_nonneg (‖n k‖ : ℝ))
    simpa only [Y, norm_smul, norm_inv, Real.norm_eq_abs, s,
      habs, div_eq_mul_inv, mul_comm] using hresidual
  have hdecomp : ∀ᶠ k in atTop, Y k = L k + Q (N k) + R k := by
    filter_upwards [hpV] with k hk
    have hzero : F (b k) = 0 := hsheet (p k) hk
    rw [← hQscale k]
    dsimp [Y, L, R, err]
    rw [hzero]
    module
  have hXL : ∀ k, X k = (s k / t k) • L k := by
    intro k
    have hi : ((0 : C), N k) = (s k)⁻¹ • d k := by simp [N, d]
    dsimp [X, L]
    rw [hi, map_smul, smul_smul, smul_smul]
    congr 1
    field_simp [ne_of_gt (hspos k), ne_of_gt (htpos k)] <;> ring
  have hNunit : ∀ k, N k ∈ Metric.sphere (0 : E) 1 := by
    intro k
    rw [Metric.mem_sphere, dist_zero_right]
    exact norm_smul_inv_norm (hnne k)
  obtain ⟨v, hvSphere, φ, hφ, hNlim⟩ :=
    (isCompact_sphere (0 : E) 1).tendsto_subseq hNunit
  have hvunit : ‖v‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hvSphere
  have hvne : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hvunit]; exact one_ne_zero)
  have hvnormal : v ∈ K.orthogonal :=
    K.isClosed_orthogonal.mem_of_tendsto hNlim
      (Filter.Eventually.of_forall (fun k =>
        K.orthogonal.smul_mem ((s (φ k))⁻¹) (hnormal (φ k))))
  have hAlim : Tendsto (fun k => A (φ k)) atTop (𝓝 w) :=
    hadir.comp hφ.tendsto_atTop
  have hQlim : Tendsto (fun k => Q (N (φ k))) atTop (𝓝 (Q v)) :=
    (hQcont.tendsto v).comp hNlim
  have hYlim := hY.comp hφ.tendsto_atTop
  have hRlim := hR.comp hφ.tendsto_atTop
  have hLlim : Tendsto (fun k => L (φ k)) atTop (𝓝 (-Q v)) := by
    have h := (hYlim.sub hQlim).sub hRlim
    have heq : (fun k => L (φ k)) =ᶠ[atTop]
        (fun k => Y (φ k) - Q (N (φ k)) - R (φ k)) := by
      filter_upwards [hφ.tendsto_atTop.eventually hdecomp] with k hk
      rw [hk]
      module
    have h' : Tendsto (fun k => Y (φ k) - Q (N (φ k)) - R (φ k))
        atTop (𝓝 (-Q v)) := by
      simpa only [Function.comp_def, zero_sub, sub_zero] using h
    exact h'.congr' heq.symm
  have hXzero : Tendsto (fun k => X (φ k)) atTop (𝓝 (0 : Z)) := by
    have hsep' : Tendsto (fun k => s (φ k) / t (φ k)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def, s, t] using hsep.comp hφ.tendsto_atTop
    have h : Tendsto (fun k => (s (φ k) / t (φ k)) • L (φ k))
        atTop (𝓝 (0 : Z)) := by
      simpa only [zero_smul] using hsep'.smul hLlim
    exact h.congr (fun k => (hXL (φ k)).symm)
  let G : ℕ → (C × E) →L[ℝ] Z := fun k =>
    fderiv ℝ F (b k) - fderiv ℝ F (c k, 0) - H (0, (a k : E))
  have hdiff : ∀ k, b k - (c k, (0 : E)) = (0, (a k : E)) := by
    intro k
    simp [b]
  have hGsmall : G =o[atTop] t := by
    have hstrictO :
        (fun z : (C × E) × (C × E) =>
          fderiv ℝ F z.1 - fderiv ℝ F z.2 - H (z.1 - z.2))
        =o[𝓝 ((0 : C × E), (0 : C × E))]
        (fun z : (C × E) × (C × E) => z.1 - z.2) :=
      (hasStrictFDerivAt_iff_isLittleO (𝕜 := ℝ) (f := fderiv ℝ F)
        (f' := H) (x := (0 : C × E))).mp hstrict
    have hpair : Tendsto (fun k => (b k, (c k, (0 : E)))) atTop
        (𝓝 ((0 : C × E), (0 : C × E))) := hb.prodMk_nhds hcb
    have hcomp := hstrictO.comp_tendsto hpair
    have h := hcomp.norm_right
    simpa only [Function.comp_def, hdiff, hInorm, G, t] using h
  have hGzero : Tendsto (fun k => (t k)⁻¹ • G k) atTop
      (𝓝 (0 : (C × E) →L[ℝ] Z)) := by
    letI : NormSMulClass ℝ ((C × E) →L[ℝ] Z) :=
      NormedSpace.toNormSMulClass (𝕜 := ℝ) (E := (C × E) →L[ℝ] Z)
    exact Asymptotics.IsLittleO.tendsto_inv_smul_nhds_zero
      (𝕜 := ℝ) (E' := (C × E) →L[ℝ] Z) (f := G) (g := t) (l := atTop) hGsmall
  have heval : Continuous (fun z : ((C × E) →L[ℝ] Z) × (C × E) => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  have hGapply : Tendsto (fun k => ((t (φ k))⁻¹ • G (φ k)) (0, N (φ k)))
      atTop (𝓝 (0 : Z)) := by
    have h := (heval.tendsto (0, ((0 : C), v))).comp
      ((hGzero.comp hφ.tendsto_atTop).prodMk_nhds
        (tendsto_const_nhds.prodMk_nhds hNlim))
    simpa only [Function.comp_def, ContinuousLinearMap.zero_apply] using h
  have hHcont : Continuous (fun z : E × E => H (0, z.1) (0, z.2)) :=
    (H.continuous.comp (continuous_const.prodMk continuous_fst)).clm_apply
      (continuous_const.prodMk continuous_snd)
  have hHlim : Tendsto (fun k => H (0, A (φ k)) (0, N (φ k)))
      atTop (𝓝 (H (0, w) (0, v))) :=
    (hHcont.tendsto (w, v)).comp (hAlim.prodMk_nhds hNlim)
  have hXlimit : Tendsto (fun k => X (φ k)) atTop (𝓝 (H (0, w) (0, v))) := by
    have heq : (fun k => X (φ k)) =ᶠ[atTop]
        (fun k => ((t (φ k))⁻¹ • G (φ k)) (0, N (φ k)) +
          H (0, A (φ k)) (0, N (φ k))) := by
      filter_upwards [hφ.tendsto_atTop.eventually hcbU] with k hk
      have hzero := hpartial (c (φ k)) hk (N (φ k))
      have hi : ((0 : C), A (φ k)) = (t (φ k))⁻¹ • ((0 : C), (a (φ k) : E)) := by
        simp [A]
      dsimp [X, G]
      rw [hi]
      simp only [map_smul, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.sub_apply, hzero, sub_zero, smul_sub]
      module
    have h : Tendsto (fun k => ((t (φ k))⁻¹ • G (φ k)) (0, N (φ k)) +
        H (0, A (φ k)) (0, N (φ k))) atTop (𝓝 (H (0, w) (0, v))) := by
      simpa only [zero_add] using hGapply.add hHlim
    exact h.congr' heq.symm
  have hkernelH : H (0, w) (0, v) = 0 := tendsto_nhds_unique hXlimit hXzero
  have hDQ : fderiv ℝ Q w =
      (H (0, w)).comp (ContinuousLinearMap.inr ℝ C E) := by
    have hi : HasFDerivAt (fun x : E => ((0 : C), x))
        (ContinuousLinearMap.inr ℝ C E) w := hasFDerivAt_prodMk_right 0 w
    have hq := (H.hasFDerivAt_of_bilinear hi hi).const_smul (1 / 2 : ℝ)
    have hq' : HasFDerivAt Q ((H (0, w)).comp (ContinuousLinearMap.inr ℝ C E)) w := by
      apply hq.congr_fderiv
      refine ContinuousLinearMap.ext (fun (x : E) => ?_)
      change (1 / 2 : ℝ) • (H (0, w) (0, x) + H (0, x) (0, w)) = H (0, w) (0, x)
      rw [hsym (0, x) (0, w), ← two_smul ℝ, smul_smul]
      norm_num
    exact hq'.fderiv
  have hkernel : (fderiv ℝ Q w) v = 0 := by
    rw [hDQ]
    exact hkernelH
  have helllim : Tendsto (fun k => ell (p (φ k))) atTop (𝓝 (ell 0)) :=
    ((hell.continuousAt (hV.mem_nhds hVzero)).tendsto).comp (hp.comp hφ.tendsto_atTop)
  have hstressEval : Continuous (fun z : (Z →L[ℝ] ℝ) × Z => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  have hstressL : Tendsto (fun k => ell (p (φ k)) (L (φ k)))
      atTop (𝓝 (ell 0 (-Q v))) :=
    (hstressEval.tendsto (ell 0, -Q v)).comp (helllim.prodMk_nhds hLlim)
  have hstressZero : (fun k => ell (p (φ k)) (L (φ k))) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
    filter_upwards [hφ.tendsto_atTop.eventually hpV] with k hk
    have hzero := hann (p (φ k)) hk (n (φ k)) (hnormal (φ k))
    dsimp [L, d, b, p]
    rw [map_smul, hzero, smul_zero]
  have hstressValue : ell 0 (-Q v) = 0 :=
    tendsto_nhds_unique hstressL (tendsto_const_nhds.congr' hstressZero.symm)
  have hpos : 0 < ell 0 (Q v) := hpositive v hvnormal hvne hkernel
  have hzero : ell 0 (Q v) = 0 := by
    simpa only [map_neg, neg_eq_zero] using hstressValue
  exact (ne_of_gt hpos) hzero

end SupportedStress

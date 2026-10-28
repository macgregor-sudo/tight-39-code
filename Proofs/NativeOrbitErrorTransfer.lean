module

public import A5Raw
public import GSResidual
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-! Actual compact-group transfer of an explicit native normal-local estimate and exhaustion.
The normal-local estimate and exhaustion remain explicit hypotheses. -/
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace CKM.NativeOrbitErrorTransfer
open NativeFirstOrder NativeGroupSlice NativeFourFamily
open Option2.NativeStress.AnalyticDerivative
open Filter Topology

def sliceUnion (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (V : Fin 4 → Set SliceParam) : Set Cfg :=
  ⋃ i, (fun p => literalCfg ξ + (sliceFam ξ hξ i p : Cfg)) '' V i

def saturation (S : Set Cfg) : Set Cfg := ⋃ A : autC, (actC A.1) '' S

def nativeOrbit (ξ : Fin 4 → ℂ) : Set Cfg := saturation {literalCfg ξ}

theorem mem_saturation (S : Set Cfg) (y : Cfg) :
    y ∈ saturation S ↔ ∃ A ∈ autC, ∃ x ∈ S, actC A x = y := by
  simp [saturation]

theorem inverse_action_cancel {A : CEnd} (hA : A ∈ autC) (x : Cfg) :
    actC (Ring.inverse A) (actC A x) = x := by
  change ((actC (Ring.inverse A)).comp (actC A)) x = x
  rw [← actC_mul, (mul_inverse_of_mem_autOf hA).2, actC_one]
  rfl

def actionLinearEquiv (A : CEnd) (hA : A ∈ autC) : Cfg ≃ₗ[ℝ] Cfg :=
  LinearEquiv.ofBijective (actC A).toLinearMap ⟨
    fun x y h => (inverse_action_cancel hA x).symm.trans
      ((congrArg (actC (Ring.inverse A)) h).trans (inverse_action_cancel hA y)),
    fun y => ⟨actC (Ring.inverse A) y, by
      change ((actC A).comp (actC (Ring.inverse A))) y = y
      rw [← actC_mul, (mul_inverse_of_mem_autOf hA).1, actC_one]
      rfl⟩⟩

def actionEquiv (A : CEnd) (hA : A ∈ autC) : Cfg ≃L[ℝ] Cfg where
  toLinearEquiv := actionLinearEquiv A hA
  continuous_toFun := (actC A).continuous
  continuous_invFun := (actionLinearEquiv A hA).symm.toLinearMap.continuous_of_finiteDimensional

theorem isOpen_saturation {S : Set Cfg} (hS : IsOpen S) : IsOpen (saturation S) := by
  apply isOpen_iUnion
  intro A
  exact (actionEquiv A.1 A.2).toHomeomorph.isOpenMap S hS

/-- Uniform bounds in the existing coordinate norms, including the inverse residual action. -/
theorem compact_operator_bounds :
    ∃ K B : ℝ, 0 < K ∧ 0 < B ∧ ∀ A ∈ autC,
      ‖actC A‖ ≤ K ∧ ‖rowAction A‖ ≤ B ∧ ‖rowAction (Ring.inverse A)‖ ≤ B := by
  have ha : Continuous (fun A : CEnd => ‖actC A‖) := continuous_norm.comp actC.continuous
  have hr : Continuous (fun A : CEnd => ‖rowAction A‖) :=
    continuous_norm.comp (continuous_iff_continuousAt.mpr fun A => (analyticAt_rowAction A).continuousAt)
  obtain ⟨a, ha⟩ := isCompact_autC.bddAbove_image ha.continuousOn
  obtain ⟨b, hb⟩ := isCompact_autC.bddAbove_image hr.continuousOn
  refine ⟨|a| + 1, |b| + 1, by positivity, by positivity, ?_⟩
  intro A hA
  have h1 : ‖actC A‖ ≤ a := ha (Set.mem_image_of_mem _ hA)
  have h2 : ‖rowAction A‖ ≤ b := hb (Set.mem_image_of_mem _ hA)
  have h3 : ‖rowAction (Ring.inverse A)‖ ≤ b := hb (Set.mem_image_of_mem _ (inverse_mem_autOf hA))
  exact ⟨by linarith [le_abs_self a], by linarith [le_abs_self b], by linarith [le_abs_self b]⟩

/-- Correct inverse direction: recover the slice residual from the transformed residual. -/
theorem residual_inverse_bound {A : CEnd} (hA : A ∈ autC) (x : Cfg) :
    ‖originalF x‖ ≤ ‖rowAction (Ring.inverse A)‖ * ‖originalF (actC A x)‖ := by
  have h : originalF x = rowAction (Ring.inverse A) (originalF (actC A x)) := by
    rw [originalF_actC hA]
    change originalF x = (rowAction (Ring.inverse A) * rowAction A) (originalF x)
    rw [(rowAction_inverse hA).2]
    rfl
  rw [h]
  exact (rowAction (Ring.inverse A)).le_opNorm _

/-- Quantitative saturation comparison, retaining the required nonempty source set. -/
theorem infDist_action_saturation_le (S : Set Cfg) (hS : S.Nonempty)
    {A : CEnd} (hA : A ∈ autC) (K : ℝ) (hK : 0 < K) (hAK : ‖actC A‖ ≤ K) (x : Cfg) :
    Metric.infDist (actC A x) (saturation S) ≤ K * Metric.infDist x S := by
  have h : Metric.infDist (actC A x) (saturation S) / K ≤ Metric.infDist x S := by
    apply (Metric.le_infDist hS).mpr
    intro y hy
    apply (div_le_iff₀ hK).mpr
    have hm : actC A y ∈ saturation S := (mem_saturation S _).mpr ⟨A, hA, y, hy, rfl⟩
    calc
      _ ≤ dist (actC A x) (actC A y) := Metric.infDist_le_dist_of_mem hm
      _ = ‖actC A (x-y)‖ := by rw [dist_eq_norm, map_sub]
      _ ≤ ‖actC A‖ * ‖x-y‖ := (actC A).le_opNorm _
      _ ≤ K * dist x y := by rw [dist_eq_norm]; exact mul_le_mul_of_nonneg_right hAK (norm_nonneg _)
      _ = dist x y * K := mul_comm _ _
  simpa only [mul_comm] using (div_le_iff₀ hK).mp h

theorem sliceUnion_nonempty (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (V : Fin 4 → Set SliceParam) (hV : ∀ i, V i ∈ 𝓝 0) : (sliceUnion ξ hξ V).Nonempty := by
  refine ⟨literalCfg ξ, Set.mem_iUnion.mpr ⟨0, 0, mem_of_mem_nhds (hV 0), ?_⟩⟩
  simp [sliceFam_zero]

/-- Each native slice family solves all original rows on an actual parameter neighborhood. -/
theorem zero_family_neighborhoods (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    ∃ V0 : Fin 4 → Set SliceParam, (∀ i, V0 i ∈ 𝓝 0) ∧
      ∀ V : Fin 4 → Set SliceParam, (∀ i, V i ⊆ V0 i) →
        ∀ x ∈ sliceUnion ξ hξ V, originalF x = 0 := by
  let V0 : Fin 4 → Set SliceParam := fun i =>
    {p | originalF (literalCfg ξ + (sliceFam ξ hξ i p : Cfg)) = 0}
  refine ⟨V0, fun i => eventually_originalF_sliceFam hξ i, ?_⟩
  intro V hV x hx
  obtain ⟨i, p, hp, rfl⟩ := Set.mem_iUnion.mp hx
  exact hV i hp

/-- Actual orbit-neighborhood transfer. The normal-local estimate and exhaustion are visible
inputs on the exact native slice union; no ambient estimate or metric equality is assumed. -/
theorem orbit_transfer (ξ : Fin 4 → ℂ) (hξ : IsGoodPhase ξ)
    (V : Fin 4 → Set SliceParam) (hV : ∀ i, V i ∈ 𝓝 0)
    (hzero : ∀ x ∈ sliceUnion ξ hξ.1 V, originalF x = 0)
    (r C : ℝ) (hr : 0 < r) (hC : 0 < C)
    (hnormal : ∀ n : normalC ξ, ‖n‖ < r →
      Metric.infDist (literalCfg ξ + (n : Cfg)) (sliceUnion ξ hξ.1 V)^2 ≤
        C * ‖originalF (literalCfg ξ + (n : Cfg))‖ ∧
      (originalF (literalCfg ξ + (n : Cfg)) = 0 ↔ literalCfg ξ + (n : Cfg) ∈ sliceUnion ξ hξ.1 V)) :
    ∃ U : Set Cfg, IsOpen U ∧ nativeOrbit ξ ⊆ U ∧ ∃ M : ℝ, 0 < M ∧
      ∀ y ∈ U, Metric.infDist y (saturation (sliceUnion ξ hξ.1 V))^2 ≤ M * ‖originalF y‖ ∧
        (originalF y = 0 ↔ y ∈ saturation (sliceUnion ξ hξ.1 V)) := by
  obtain ⟨K, B, hK, hB, hop⟩ := compact_operator_bounds
  let φ := slicePH ξ hξ.1
  let W0 : Set Cfg := φ '' (φ.source ∩ {p | ‖p.2‖ < r})
  have hW0 : IsOpen W0 := φ.isOpen_image_source_inter (isOpen_lt continuous_snd.norm continuous_const)
  have hP : literalCfg ξ ∈ W0 := by
    refine ⟨0, ⟨zero_mem_slicePH_source ξ hξ.1, ?_⟩, ?_⟩
    · simpa using hr
    · exact sliceChart_zero ξ
  let U := saturation W0
  have hOrbit : nativeOrbit ξ ⊆ U := by
    apply Set.iUnion_mono
    intro A
    exact Set.image_mono (Set.singleton_subset_iff.mpr hP)
  have hAllZero : ∀ y ∈ saturation (sliceUnion ξ hξ.1 V), originalF y = 0 := by
    intro y hy
    obtain ⟨A, hA, x, hx, rfl⟩ := (mem_saturation _ _).mp hy
    exact (originalF_actC_eq_zero_iff hA x).mpr (hzero x hx)
  refine ⟨U, isOpen_saturation hW0, hOrbit, K^2 * C * B, by positivity, ?_⟩
  intro y hy
  obtain ⟨A, hA, x, ⟨p, ⟨hp, hpn⟩, rfl⟩, rfl⟩ := (mem_saturation _ _).mp hy
  let D : CEnd := A * groupChart p.1
  have hD : D ∈ autC := mul_mem_autOf hA (groupChart_mem_autC p.1)
  have he : actC A (φ p) = actC D (literalCfg ξ + (p.2 : Cfg)) := by
    rw [actC_mul]
    rfl
  rw [he]
  obtain ⟨hd, hz⟩ := hnormal p.2 hpn
  have hi := infDist_action_saturation_le (sliceUnion ξ hξ.1 V) (sliceUnion_nonempty ξ hξ.1 V hV)
    hD K hK (hop D hD).1 (literalCfg ξ + (p.2 : Cfg))
  have hres : ‖originalF (literalCfg ξ + (p.2 : Cfg))‖ ≤ B * ‖originalF (actC D (literalCfg ξ + (p.2 : Cfg)))‖ :=
    (residual_inverse_bound hD _).trans
      (mul_le_mul_of_nonneg_right (hop D hD).2.2 (norm_nonneg _))
  constructor
  · calc
      _ ≤ (K * Metric.infDist (literalCfg ξ + (p.2 : Cfg)) (sliceUnion ξ hξ.1 V))^2 :=
        pow_le_pow_left₀ Metric.infDist_nonneg hi 2
      _ = K^2 * Metric.infDist (literalCfg ξ + (p.2 : Cfg)) (sliceUnion ξ hξ.1 V)^2 := by ring
      _ ≤ K^2 * (C * ‖originalF (literalCfg ξ + (p.2 : Cfg))‖) := mul_le_mul_of_nonneg_left hd (sq_nonneg K)
      _ ≤ K^2 * (C * (B * ‖originalF (actC D (literalCfg ξ + (p.2 : Cfg)))‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hres hC.le) (sq_nonneg K)
      _ = (K^2 * C * B) * ‖originalF (actC D (literalCfg ξ + (p.2 : Cfg)))‖ := by ring
  · constructor
    · intro h
      have hx := hz.mp ((originalF_actC_eq_zero_iff hD _).mp h)
      exact (mem_saturation _ _).mpr ⟨D, hD, _, hx, rfl⟩
    · exact hAllZero _

/-- The zero-set premise in orbit_transfer is supplied by a native parameter shrink. -/
theorem orbit_transfer_with_family_shrink (ξ : Fin 4 → ℂ) (hξ : IsGoodPhase ξ) :
    ∃ V0 : Fin 4 → Set SliceParam, (∀ i, V0 i ∈ 𝓝 0) ∧
      ∀ (V : Fin 4 → Set SliceParam), (∀ i, V i ∈ 𝓝 0) → (∀ i, V i ⊆ V0 i) →
        ∀ r C : ℝ, 0 < r → 0 < C →
          (∀ n : normalC ξ, ‖n‖ < r →
            Metric.infDist (literalCfg ξ + (n : Cfg)) (sliceUnion ξ hξ.1 V)^2 ≤
              C * ‖originalF (literalCfg ξ + (n : Cfg))‖ ∧
            (originalF (literalCfg ξ + (n : Cfg)) = 0 ↔ literalCfg ξ + (n : Cfg) ∈ sliceUnion ξ hξ.1 V)) →
          ∃ U : Set Cfg, IsOpen U ∧ nativeOrbit ξ ⊆ U ∧ ∃ M : ℝ, 0 < M ∧
            ∀ y ∈ U, Metric.infDist y (saturation (sliceUnion ξ hξ.1 V))^2 ≤ M * ‖originalF y‖ ∧
              (originalF y = 0 ↔ y ∈ saturation (sliceUnion ξ hξ.1 V)) := by
  obtain ⟨V0, hV0, hz⟩ := zero_family_neighborhoods ξ hξ.1
  exact ⟨V0, hV0, fun V hV hsub r C hr hC hn =>
    orbit_transfer ξ hξ V hV (hz V hsub) r C hr hC hn⟩

def rawUnion (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (U : Fin 4 → Set RawParam62) : Set Cfg :=
  ⋃ i, rawMap62 ξ hξ i '' U i

/-- The exact neighborhoods delivered by accepted rawFamily_descends identify the actual
four-family raw germ with the actual saturation. Further neighborhood compatibility with a
normal estimate must retain these explicit parameters; no arbitrary shrink is asserted. -/
theorem raw_saturation_germ (ξ : Fin 4 → ℂ) (hξ : IsGoodPhase ξ) :
    ∃ (U : Fin 4 → Set RawParam62) (V : Fin 4 → Set SliceParam),
      (∀ i, U i ∈ 𝓝 0) ∧ (∀ i, V i ∈ 𝓝 0) ∧
      (∀ x ∈ sliceUnion ξ hξ.1 V, originalF x = 0) ∧
      rawUnion ξ hξ.1 U =ᶠ[𝓝 (literalCfg ξ)] saturation (sliceUnion ξ hξ.1 V) := by
  classical
  choose W hW hP hEmbed U hU V hV hz hg using fun i => rawFamily_descends hξ i
  refine ⟨U, V, hU, hV, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, p, hp, rfl⟩ := Set.mem_iUnion.mp hx
    exact (hz i p hp).2
  · rw [Filter.eventuallyEqSet_iff]
    filter_upwards [Filter.eventually_all.mpr hg] with y hy
    constructor
    · intro h
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
      obtain ⟨p, hp, A, hA, he⟩ := (hy i).mp hi
      exact (mem_saturation _ y).mpr ⟨A, hA, _, Set.mem_iUnion.mpr ⟨i, p, hp, rfl⟩, he⟩
    · intro h
      obtain ⟨A, hA, x, hx, he⟩ := (mem_saturation _ y).mp h
      obtain ⟨i, p, hp, hpx⟩ := Set.mem_iUnion.mp hx
      apply Set.mem_iUnion.mpr
      refine ⟨i, (hy i).mpr ⟨p, hp, A, hA, ?_⟩⟩
      exact (congrArg (actC A) hpx).trans he

/-- Compatibility with a smaller normal-input parameter neighborhood. Enlarging to a
zero-valued native family union weakens the distance estimate and preserves exhaustion. -/
theorem orbit_transfer_from_smaller_family (ξ : Fin 4 → ℂ) (hξ : IsGoodPhase ξ)
    (Vsmall V : Fin 4 → Set SliceParam) (hsmall : ∀ i, Vsmall i ∈ 𝓝 0)
    (hsub : ∀ i, Vsmall i ⊆ V i)
    (hzero : ∀ x ∈ sliceUnion ξ hξ.1 V, originalF x = 0)
    (r C : ℝ) (hr : 0 < r) (hC : 0 < C)
    (hnormal : ∀ n : normalC ξ, ‖n‖ < r →
      Metric.infDist (literalCfg ξ + (n : Cfg)) (sliceUnion ξ hξ.1 Vsmall)^2 ≤
        C * ‖originalF (literalCfg ξ + (n : Cfg))‖ ∧
      (originalF (literalCfg ξ + (n : Cfg)) = 0 ↔ literalCfg ξ + (n : Cfg) ∈ sliceUnion ξ hξ.1 Vsmall)) :
    ∃ U : Set Cfg, IsOpen U ∧ nativeOrbit ξ ⊆ U ∧ ∃ M : ℝ, 0 < M ∧
      ∀ y ∈ U, Metric.infDist y (saturation (sliceUnion ξ hξ.1 V))^2 ≤ M * ‖originalF y‖ ∧
        (originalF y = 0 ↔ y ∈ saturation (sliceUnion ξ hξ.1 V)) := by
  have hV : ∀ i, V i ∈ 𝓝 0 := fun i => mem_of_superset (hsmall i) (hsub i)
  have hs : sliceUnion ξ hξ.1 Vsmall ⊆ sliceUnion ξ hξ.1 V :=
    Set.iUnion_mono fun i => Set.image_mono (hsub i)
  apply orbit_transfer ξ hξ V hV hzero r C hr hC
  intro n hn
  obtain ⟨hd, hz⟩ := hnormal n hn
  refine ⟨?_, ⟨fun h => hs (hz.mp h), fun h => hzero _ h⟩⟩
  exact (pow_le_pow_left₀ Metric.infDist_nonneg
    (Metric.infDist_le_infDist_of_subset hs (sliceUnion_nonempty ξ hξ.1 Vsmall hsmall)) 2).trans hd

/-- One conditional raw/slice/orbit endpoint. The exact raw neighborhoods are selected by
accepted descent. The normal estimate may use any smaller genuine parameter neighborhoods,
so it can be supplied after intersecting them with an independent normal-local neighborhood. -/
theorem raw_orbit_transfer (ξ : Fin 4 → ℂ) (hξ : IsGoodPhase ξ) :
    ∃ (Uraw : Fin 4 → Set RawParam62) (Vraw : Fin 4 → Set SliceParam),
      (∀ i, Uraw i ∈ 𝓝 0) ∧ (∀ i, Vraw i ∈ 𝓝 0) ∧
      rawUnion ξ hξ.1 Uraw =ᶠ[𝓝 (literalCfg ξ)] saturation (sliceUnion ξ hξ.1 Vraw) ∧
      ∀ (V : Fin 4 → Set SliceParam), (∀ i, V i ∈ 𝓝 0) → (∀ i, V i ⊆ Vraw i) →
        ∀ r C : ℝ, 0 < r → 0 < C →
          (∀ n : normalC ξ, ‖n‖ < r →
            Metric.infDist (literalCfg ξ + (n : Cfg)) (sliceUnion ξ hξ.1 V)^2 ≤
              C * ‖originalF (literalCfg ξ + (n : Cfg))‖ ∧
            (originalF (literalCfg ξ + (n : Cfg)) = 0 ↔ literalCfg ξ + (n : Cfg) ∈ sliceUnion ξ hξ.1 V)) →
          ∃ U : Set Cfg, IsOpen U ∧ nativeOrbit ξ ⊆ U ∧ ∃ M : ℝ, 0 < M ∧
            ∀ y ∈ U, Metric.infDist y (saturation (sliceUnion ξ hξ.1 Vraw))^2 ≤ M * ‖originalF y‖ ∧
              (originalF y = 0 ↔ y ∈ saturation (sliceUnion ξ hξ.1 Vraw)) := by
  obtain ⟨Uraw, Vraw, hUraw, hVraw, hz, hg⟩ := raw_saturation_germ ξ hξ
  exact ⟨Uraw, Vraw, hUraw, hVraw, hg, fun V hV hsub r C hr hC hn =>
    orbit_transfer_from_smaller_family ξ hξ V Vraw hV hsub hz r C hr hC hn⟩

end CKM.NativeOrbitErrorTransfer

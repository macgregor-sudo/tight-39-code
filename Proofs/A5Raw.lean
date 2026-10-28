module

public import A5SliceChart
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

@[expose] public section

/-!
# The raw simultaneous chart, raw germs and descent to the slice (piece RAW)

Near `P` the group/slice chart `slicePH : derC × N → Cfg` is an analytic product chart, and the raw
families are `G`-saturated: `rawMap62 H` (and the full seventy-parameter `rawMap H`, whose extra
right-gauge directions are absorbed by `nativeRightMultiply`) has the same germ as
`slicePH (derC-small × M_H)`. Composing `slicePH` with `id × Φ_slice` and the linear identification
`derC × ℝ⁴ ≃ ℝ⁵⁶` (`finrank_derC = 52`) gives the raw chart `ℝ⁵⁶ × (ℝ⁶)⁴ × ℝ⁹⁷³ → Cfg`. The slice
family germ is the raw family germ intersected with the slice, and every raw family point near `P` is
`G`-related to a point of the slice germ (the labelled quotient statement, through the group/slice
package's open embedding `sliceToOrbit`).
-/

noncomputable section

open CKM.NativeFirstOrder CKM.NativeGroupSlice CompactAlbert UnitaryErrorBases
open scoped Matrix Topology

namespace CKM.NativeFourFamily

open Filter

/-! ## Generic germ criterion -/

/-- A germ-image criterion: the image of one neighbourhood lies in `S` near `x`, and `S` lies near `x`
in the image of every neighbourhood. -/
private theorem raw_isGermImage_of {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {S : Set X} {x : X} {f : P → X} {p : P} {U₀ : Set P} (hU₀ : U₀ ∈ 𝓝 p)
    (h1 : ∀ᶠ y in 𝓝 x, y ∈ f '' U₀ → y ∈ S)
    (h2 : ∀ U ∈ 𝓝 p, ∀ᶠ y in 𝓝 x, y ∈ S → y ∈ f '' U) : IsGermImage S x f p := by
  refine ⟨U₀, hU₀, fun U hU hUU₀ => ?_⟩
  rw [eventuallyEqSet_iff]
  filter_upwards [h1, h2 U hU] with y hy1 hy2
  exact ⟨fun hy => hy1 (Set.image_mono hUU₀ hy), hy2⟩

/-! ## The slice chart near `P` -/

section SliceChart

variable {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀)

private theorem raw_gc_neg_mul (D : ↥derC) : groupChart (-D) * groupChart D = 1 := by
  show NormedSpace.exp ((-D : ↥derC) : CEnd) * NormedSpace.exp (D : CEnd) = 1
  rw [Submodule.coe_neg]
  exact exp_neg_mul_exp _

private theorem raw_actC_cancel (D : ↥derC) (C : Cfg) :
    actC (groupChart (-D)) (actC (groupChart D) C) = C := by
  rw [← ContinuousLinearMap.comp_apply, ← actC_mul, raw_gc_neg_mul, actC_one]
  rfl

include hξ₀ in
private theorem raw_target_mem : (slicePH ξ₀ hξ₀).target ∈ 𝓝 (literalCfg ξ₀) :=
  (slicePH ξ₀ hξ₀).open_target.mem_nhds (literalCfg_mem_slicePH_target ξ₀ hξ₀)

private theorem raw_mem_sliceSet (n : ↥(normalC ξ₀)) : literalCfg ξ₀ + ↑n ∈ sliceSet ξ₀ := by
  show literalCfg ξ₀ + ↑n - literalCfg ξ₀ ∈ normalC ξ₀
  rw [add_sub_cancel_left]
  exact n.2

private theorem raw_decomp {y : Cfg} (hy : y ∈ (slicePH ξ₀ hξ₀).target) :
    actC (groupChart ((slicePH ξ₀ hξ₀).symm y).1) (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ y)) = y := by
  have h := (slicePH ξ₀ hξ₀).right_inv hy
  rw [slicePH_coe] at h
  exact h

private theorem raw_undecomp {y : Cfg} (hy : y ∈ (slicePH ξ₀ hξ₀).target) :
    actC (groupChart (-((slicePH ξ₀ hξ₀).symm y).1)) y =
      literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ y) := by
  have h := raw_actC_cancel (((slicePH ξ₀ hξ₀).symm y).1) (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ y))
  rw [raw_decomp hξ₀ hy] at h
  exact h

private theorem raw_tendsto_fst :
    Tendsto (fun y => ((slicePH ξ₀ hξ₀).symm y).1) (𝓝 (literalCfg ξ₀)) (𝓝 0) := by
  have h := (continuous_fst.continuousAt.comp
    ((slicePH ξ₀ hξ₀).continuousAt_symm (literalCfg_mem_slicePH_target ξ₀ hξ₀))).tendsto
  rw [Function.comp_apply, slicePH_symm_literalCfg] at h
  exact h

private theorem raw_tendsto_rep :
    Tendsto (sliceRep ξ₀ hξ₀) (𝓝 (literalCfg ξ₀)) (𝓝 0) := by
  have h := (continuous_snd.continuousAt.comp
    ((slicePH ξ₀ hξ₀).continuousAt_symm (literalCfg_mem_slicePH_target ξ₀ hξ₀))).tendsto
  rw [Function.comp_apply, slicePH_symm_literalCfg] at h
  exact h

private theorem raw_tendsto_add {α : Type*} {l : Filter α} {f : α → ↥(normalC ξ₀)}
    (hf : Tendsto f l (𝓝 0)) :
    Tendsto (fun a => literalCfg ξ₀ + ↑(f a)) l (𝓝 (literalCfg ξ₀)) := by
  have h := (tendsto_const_nhds (x := literalCfg ξ₀)).add
    ((continuous_subtype_val.tendsto (0 : ↥(normalC ξ₀))).comp hf)
  rw [Submodule.coe_zero, add_zero] at h
  exact h

/-- Local orbit relation in slice coordinates: a point near `P` that is `G`-related to a slice point
`P + n` near `P` has slice coordinate `n` (`exists_local_orbit_injective`). -/
private theorem raw_orbit_rep :
    ∃ Wl ∈ 𝓝 (literalCfg ξ₀), ∀ᶠ y in 𝓝 (literalCfg ξ₀), ∀ n : ↥(normalC ξ₀),
      literalCfg ξ₀ + ↑n ∈ Wl → ∀ A ∈ autC, actC A (literalCfg ξ₀ + ↑n) = y →
        sliceRep ξ₀ hξ₀ y = n := by
  obtain ⟨Wl, hWl, hinj⟩ := exists_local_orbit_injective ξ₀ hξ₀
  refine ⟨Wl, hWl, ?_⟩
  filter_upwards [raw_target_mem hξ₀, hWl,
    (raw_tendsto_add (raw_tendsto_rep hξ₀)).eventually_mem hWl] with y hyT hyW hyW' n hn A hA hAy
  have hA' : groupChart (-((slicePH ξ₀ hξ₀).symm y).1) * A ∈ autC :=
    mul_mem_autOf (groupChart_mem_autC _) hA
  have h := hinj _ ⟨hn, raw_mem_sliceSet n⟩ _ ⟨hyW', raw_mem_sliceSet _⟩ _ hA'
    (by rw [actC_mul, ContinuousLinearMap.comp_apply, hAy, raw_undecomp hξ₀ hyT])
  exact (Subtype.ext (add_left_cancel h)).symm

/-- Near `P`, a slice point is `P` plus its slice coordinate. -/
private theorem raw_slice_points :
    ∀ᶠ y in 𝓝 (literalCfg ξ₀), y ∈ sliceSet ξ₀ → literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ y) = y := by
  obtain ⟨Wl, hWl, h⟩ := raw_orbit_rep hξ₀
  filter_upwards [h, hWl] with y hy hyW hys
  have hn : literalCfg ξ₀ + ((⟨y - literalCfg ξ₀, hys⟩ : ↥(normalC ξ₀)) : Cfg) = y :=
    add_sub_cancel _ _
  have h1 := hy ⟨y - literalCfg ξ₀, hys⟩ (by rw [hn]; exact hyW) 1 (one_mem_autOf _)
    (by rw [hn, actC_one]; rfl)
  rw [h1]
  exact hn

/-- Products `χ(D₁) χ(-D₂)` of small group-chart elements are small group-chart elements
(`exists_groupChart_local`). -/
private theorem raw_mul_small {B : Set ↥derC} (hB : B ∈ 𝓝 (0 : ↥derC)) :
    ∃ B' ∈ 𝓝 (0 : ↥derC), ∀ D₁ ∈ B', ∀ D₂ ∈ B', ∃ D ∈ B,
      groupChart D = groupChart D₁ * groupChart (-D₂) := by
  obtain ⟨U, W, inv, -, h0U, hWo, h1W, -, -, hinvg, hinvD, hinvan⟩ := exists_groupChart_local
  have hinv1 : inv 1 = 0 := by
    have := hinvD 0 h0U
    rwa [groupChart_zero] at this
  let m : ↥derC × ↥derC → CEnd := fun z => groupChart z.1 * groupChart (-z.2)
  have hm : ContinuousAt m ((0 : ↥derC), (0 : ↥derC)) :=
    ((analyticAt_groupChart _).continuousAt.comp continuous_fst.continuousAt).mul
      (ContinuousAt.comp (g := fun D : ↥derC => groupChart (-D))
        (AnalyticAt.comp (g := groupChart) (f := fun D : ↥derC => -D) (analyticAt_groupChart _)
          analyticAt_id.neg).continuousAt
        continuous_snd.continuousAt)
  have hm0 : m ((0 : ↥derC), (0 : ↥derC)) = 1 := by
    have hneg0 : groupChart (-(0 : ↥derC)) = 1 := by
      rw [show (-(0 : ↥derC)) = 0 from
        Subtype.ext (by rw [Submodule.coe_neg, Submodule.coe_zero, neg_zero]), groupChart_zero]
    show groupChart 0 * groupChart (-(0 : ↥derC)) = 1
    rw [hneg0, groupChart_zero, one_mul]
  have hf : ContinuousAt (fun z => inv (m z)) ((0 : ↥derC), (0 : ↥derC)) :=
    (hinvan 1 h1W).continuousAt.comp_of_eq hm hm0
  have hN : {z | m z ∈ W ∧ inv (m z) ∈ B} ∈ 𝓝 ((0 : ↥derC), (0 : ↥derC)) :=
    Filter.inter_mem (hm.preimage_mem_nhds (hWo.mem_nhds (by rw [hm0]; exact h1W)))
      (hf.preimage_mem_nhds (by show B ∈ 𝓝 (inv (m (0, 0))); rw [hm0, hinv1]; exact hB))
  obtain ⟨B₁, hB₁, B₂, hB₂, hsub⟩ := mem_nhds_prod_iff.1 hN
  refine ⟨B₁ ∩ B₂, Filter.inter_mem hB₁ hB₂, fun D₁ h₁ D₂ h₂ => ?_⟩
  obtain ⟨hmW, hmB⟩ := hsub (Set.mk_mem_prod h₁.1 h₂.2)
  have hmaut : m (D₁, D₂) ∈ autC := mul_mem_autOf (groupChart_mem_autC _) (groupChart_mem_autC _)
  exact ⟨_, hmB, (hinvg _ ⟨hmaut, hmW⟩).2⟩

variable {Q : Type*} [TopologicalSpace Q] {b : Q → Cfg} {q₀ : Q}

omit hξ₀ in
private theorem raw_tendsto_b (hb : ContinuousAt b q₀) (hb0 : b q₀ = literalCfg ξ₀) :
    Tendsto b (𝓝 q₀) (𝓝 (literalCfg ξ₀)) := hb0 ▸ hb.tendsto

/-- Lifting: a point near `P` with the slice coordinate of `b p` is `χ(D) • b p` with `D` small. -/
private theorem raw_lift (hb : ContinuousAt b q₀) (hb0 : b q₀ = literalCfg ξ₀) {B : Set ↥derC}
    (hB : B ∈ 𝓝 (0 : ↥derC)) :
    ∃ V ∈ 𝓝 q₀, ∀ᶠ y in 𝓝 (literalCfg ξ₀), ∀ p ∈ V,
      sliceRep ξ₀ hξ₀ y = sliceRep ξ₀ hξ₀ (b p) → ∃ D ∈ B, actC (groupChart D) (b p) = y := by
  obtain ⟨B', hB', hmul⟩ := raw_mul_small hB
  have hbt := raw_tendsto_b hb hb0
  refine ⟨{p | b p ∈ (slicePH ξ₀ hξ₀).target ∧ ((slicePH ξ₀ hξ₀).symm (b p)).1 ∈ B'},
    Filter.inter_mem (hbt.eventually_mem (raw_target_mem hξ₀))
      (((raw_tendsto_fst hξ₀).comp hbt).eventually_mem hB'), ?_⟩
  filter_upwards [raw_target_mem hξ₀, (raw_tendsto_fst hξ₀).eventually_mem hB'] with
    y hyT hyB p hp hrep
  obtain ⟨D, hD, hgD⟩ := hmul _ hyB _ hp.2
  refine ⟨D, hD, ?_⟩
  rw [hgD, actC_mul, ContinuousLinearMap.comp_apply, raw_undecomp hξ₀ hp.1, ← hrep,
    raw_decomp hξ₀ hyT]

/-- First half of the germ statement: `G`-translates of `b p` (for `p` near `q₀`) that are near `P`
have slice coordinates in the slice germ `M`. -/
private theorem raw_cover1 (hb : ContinuousAt b q₀) (hb0 : b q₀ = literalCfg ξ₀)
    {M : Set ↥(normalC ξ₀)} (hM : IsGermImage M 0 (fun q => sliceRep ξ₀ hξ₀ (b q)) q₀) :
    ∃ V ∈ 𝓝 q₀, ∀ᶠ y in 𝓝 (literalCfg ξ₀), ∀ p ∈ V, ∀ A ∈ autC, actC A (b p) = y →
      sliceRep ξ₀ hξ₀ y ∈ M := by
  obtain ⟨Wl, hWl, hrep⟩ := raw_orbit_rep hξ₀
  obtain ⟨Ug, hUg, hgerm⟩ := hM
  have h0 := hgerm Ug hUg subset_rfl
  rw [eventuallyEqSet_iff] at h0
  have hbt := raw_tendsto_b hb hb0
  have hσ : Tendsto (fun q => sliceRep ξ₀ hξ₀ (b q)) (𝓝 q₀) (𝓝 0) := (raw_tendsto_rep hξ₀).comp hbt
  have hV := (hbt.eventually_mem (raw_target_mem hξ₀)).and
    (((raw_tendsto_add hσ).eventually_mem hWl).and ((Filter.eventually_mem_set.2 hUg).and
      (hσ.eventually h0)))
  refine ⟨_, hV, ?_⟩
  filter_upwards [hrep] with y hy p hp A hA hAy
  obtain ⟨hpT, hpW, hpU, hpM⟩ := hp
  have h1 : sliceRep ξ₀ hξ₀ y = sliceRep ξ₀ hξ₀ (b p) :=
    hy _ hpW (A * groupChart ((slicePH ξ₀ hξ₀).symm (b p)).1)
      (mul_mem_autOf hA (groupChart_mem_autC _))
      (by rw [actC_mul, ContinuousLinearMap.comp_apply, raw_decomp hξ₀ hpT, hAy])
  rw [h1]
  exact hpM.1 ⟨p, hpU, rfl⟩

/-- Second half of the germ statement: near `P`, points with slice coordinate in `M` are
`χ(D) • b p` with `(D, p)` in any given neighbourhood of `(0, q₀)`. -/
private theorem raw_cover2 (hb : ContinuousAt b q₀) (hb0 : b q₀ = literalCfg ξ₀)
    {M : Set ↥(normalC ξ₀)} (hM : IsGermImage M 0 (fun q => sliceRep ξ₀ hξ₀ (b q)) q₀) :
    ∀ U ∈ 𝓝 ((0 : ↥derC), q₀), ∀ᶠ y in 𝓝 (literalCfg ξ₀), sliceRep ξ₀ hξ₀ y ∈ M →
      y ∈ (fun z : ↥derC × Q => actC (groupChart z.1) (b z.2)) '' U := by
  intro U hU
  obtain ⟨B, hB, VU, hVU, hsub⟩ := mem_nhds_prod_iff.1 hU
  obtain ⟨V, hV, hlift⟩ := raw_lift hξ₀ hb hb0 hB
  obtain ⟨Ug, hUg, hgerm⟩ := hM
  have h0 := hgerm (V ∩ VU ∩ Ug) (Filter.inter_mem (Filter.inter_mem hV hVU) hUg)
    Set.inter_subset_right
  rw [eventuallyEqSet_iff] at h0
  filter_upwards [hlift, (raw_tendsto_rep hξ₀).eventually h0] with y hy hy0 hyM
  obtain ⟨p, ⟨⟨hpV, hpVU⟩, -⟩, hp⟩ := hy0.2 hyM
  obtain ⟨D, hD, hDy⟩ := hy p hpV hp.symm
  exact ⟨(D, p), hsub (Set.mk_mem_prod hD hpVU), hDy⟩

/-- The saturated family `(D, q) ↦ χ(D) • b q` has germ `{y | sliceRep y ∈ M}` at `P`. -/
private theorem raw_germ (hb : ContinuousAt b q₀) (hb0 : b q₀ = literalCfg ξ₀)
    {M : Set ↥(normalC ξ₀)} (hM : IsGermImage M 0 (fun q => sliceRep ξ₀ hξ₀ (b q)) q₀)
    {Tg : Set Cfg} (hTg : Tg ∈ 𝓝 (literalCfg ξ₀)) :
    IsGermImage {y | y ∈ Tg ∧ sliceRep ξ₀ hξ₀ y ∈ M} (literalCfg ξ₀)
      (fun z : ↥derC × Q => actC (groupChart z.1) (b z.2)) ((0 : ↥derC), q₀) := by
  obtain ⟨V, hV, h1⟩ := raw_cover1 hξ₀ hb hb0 hM
  refine raw_isGermImage_of (U₀ := Set.univ ×ˢ V) (prod_mem_nhds Filter.univ_mem hV) ?_ ?_
  · filter_upwards [h1, hTg] with y hy hyT
    rintro ⟨z, ⟨-, hz⟩, rfl⟩
    exact ⟨hyT, hy z.2 hz _ (groupChart_mem_autC _) rfl⟩
  · intro U hU
    filter_upwards [raw_cover2 hξ₀ hb hb0 hM U hU] with y hy hyS using hy hyS.2

/-- The saturated germ intersected with the slice is the slice germ. -/
private theorem raw_germ_slice (hb : ContinuousAt b q₀) (hb0 : b q₀ = literalCfg ξ₀)
    {M : Set ↥(normalC ξ₀)} (hM : IsGermImage M 0 (fun q => sliceRep ξ₀ hξ₀ (b q)) q₀) :
    ∃ V₀ ∈ 𝓝 ((0 : ↥derC), q₀), ∀ U₀ ∈ 𝓝 ((0 : ↥derC), q₀), U₀ ⊆ V₀ →
      IsGermImage ((fun z : ↥derC × Q => actC (groupChart z.1) (b z.2)) '' U₀ ∩ sliceSet ξ₀)
        (literalCfg ξ₀) (fun q => literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (b q))) q₀ := by
  obtain ⟨V₀, hV₀, hgerm⟩ := raw_germ hξ₀ hb hb0 hM (raw_target_mem hξ₀)
  refine ⟨V₀, hV₀, fun U₀ hU₀ hsub => ?_⟩
  have hS := hgerm U₀ hU₀ hsub
  rw [eventuallyEqSet_iff] at hS
  obtain ⟨Ug, hUg, hM'⟩ := hM
  refine ⟨Ug, hUg, fun U hU hUU => ?_⟩
  have h0 := hM' U hU hUU
  rw [eventuallyEqSet_iff] at h0 ⊢
  filter_upwards [hS, raw_slice_points hξ₀, (raw_tendsto_rep hξ₀).eventually h0,
    raw_target_mem hξ₀] with y hyS hys hy0 hyT
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hsl := raw_mem_sliceSet (sliceRep ξ₀ hξ₀ (b p))
    have hr : sliceRep ξ₀ hξ₀ (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (b p))) =
        sliceRep ξ₀ hξ₀ (b p) := Subtype.ext (add_left_cancel (hys hsl))
    refine ⟨hyS.2 ⟨hyT, hy0.1 ?_⟩, hsl⟩
    rw [hr]
    exact ⟨p, hp, rfl⟩
  · rintro ⟨hyF, hys'⟩
    obtain ⟨p, hp, hpσ⟩ := hy0.2 (hyS.1 hyF).2
    refine ⟨p, hp, ?_⟩
    show literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (b p)) = y
    rw [show sliceRep ξ₀ hξ₀ (b p) = sliceRep ξ₀ hξ₀ y from hpσ]
    exact hys hys'

/-- Generic descent of a saturated family to its slice germ. -/
private theorem raw_descends (hb : ContinuousAt b q₀) (hb0 : b q₀ = literalCfg ξ₀)
    (hz : ∀ᶠ q in 𝓝 q₀, literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (b q)) ∈ zeroSet) :
    ∃ W : Set Cfg, IsOpen W ∧ literalCfg ξ₀ ∈ W ∧ Topology.IsOpenEmbedding (sliceToOrbit ξ₀ W) ∧
      ∃ U₀ ∈ 𝓝 ((0 : ↥derC), q₀), ∃ V₀ ∈ 𝓝 q₀,
        (∀ p ∈ V₀, literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (b p)) ∈ W ∩ sliceSet ξ₀ ∩ zeroSet) ∧
        ∀ᶠ y in 𝓝 (literalCfg ξ₀),
          (y ∈ (fun z : ↥derC × Q => actC (groupChart z.1) (b z.2)) '' U₀ ↔
            ∃ p ∈ V₀, ∃ A ∈ autC, actC A (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (b p))) = y) := by
  obtain ⟨W, hWo, hPW, hemb⟩ := exists_sliceToOrbit_isOpenEmbedding ξ₀ hξ₀
  obtain ⟨Wl, hWl, hrep⟩ := raw_orbit_rep hξ₀
  obtain ⟨V, hV, hlift⟩ := raw_lift hξ₀ hb hb0 (Filter.univ_mem : Set.univ ∈ 𝓝 (0 : ↥derC))
  have hbt := raw_tendsto_b hb hb0
  have hσ : Tendsto (fun q => sliceRep ξ₀ hξ₀ (b q)) (𝓝 q₀) (𝓝 0) := (raw_tendsto_rep hξ₀).comp hbt
  have hPσ := raw_tendsto_add hσ
  let V₀ : Set Q := {p | b p ∈ (slicePH ξ₀ hξ₀).target} ∩
    ({p | literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (b p)) ∈ W} ∩
      ({p | literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (b p)) ∈ Wl} ∩
        ({p | literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (b p)) ∈ zeroSet} ∩ V)))
  have hV₀ : V₀ ∈ 𝓝 q₀ :=
    Filter.inter_mem (hbt.eventually_mem (raw_target_mem hξ₀))
      (Filter.inter_mem (hPσ.eventually_mem (hWo.mem_nhds hPW))
        (Filter.inter_mem (hPσ.eventually_mem hWl) (Filter.inter_mem hz hV)))
  refine ⟨W, hWo, hPW, hemb, Set.univ ×ˢ V₀, prod_mem_nhds Filter.univ_mem hV₀, V₀, hV₀,
    fun p hp => ⟨⟨hp.2.1, raw_mem_sliceSet _⟩, hp.2.2.2.1⟩, ?_⟩
  filter_upwards [hrep, hlift] with y hy1 hy2
  constructor
  · rintro ⟨z, ⟨-, hz⟩, rfl⟩
    refine ⟨z.2, hz, groupChart z.1 * groupChart ((slicePH ξ₀ hξ₀).symm (b z.2)).1,
      mul_mem_autOf (groupChart_mem_autC _) (groupChart_mem_autC _), ?_⟩
    rw [actC_mul, ContinuousLinearMap.comp_apply, raw_decomp hξ₀ hz.1]
  · rintro ⟨p, hp, A, hA, hAy⟩
    obtain ⟨D, -, hD⟩ := hy2 p hp.2.2.2.2 (hy1 _ hp.2.2.1 A hA hAy)
    exact ⟨(D, p), ⟨trivial, hp⟩, hD⟩

end SliceChart

/-! ## The base families -/

/-- The slice-family embedding `(X, e) ↦ (X, 0, e)`. -/
private def raw_embed : SliceParam →L[ℝ] PreParam :=
  (ContinuousLinearMap.fst ℝ (Fin 8 → ℝ) (Fin 2 → ℝ)).prod
    ((0 : SliceParam →L[ℝ] (Fin 8 → ℝ)).prod (ContinuousLinearMap.snd ℝ (Fin 8 → ℝ) (Fin 2 → ℝ)))

private theorem raw_famb_cont {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    ContinuousAt (fun p : SliceParam => preMap ξ₀ hξ₀ H (p.1, 0, p.2)) 0 :=
  (analyticAt_preMap hξ₀ H).continuousAt.comp_of_eq raw_embed.continuous.continuousAt
    (map_zero raw_embed)

private theorem raw_famb_zero {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    preMap ξ₀ hξ₀ H ((0 : SliceParam).1, 0, (0 : SliceParam).2) = literalCfg ξ₀ :=
  preMap_zero hξ₀ H

private theorem raw_comb_cont {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    ContinuousAt (fun θ : Fin 4 → ℝ => literalCfg (commonPhase ξ₀ θ)) 0 :=
  (analyticAt_literalPhase hξ₀).continuousAt

private theorem raw_comb_zero (ξ₀ : Fin 4 → ℂ) :
    literalCfg (commonPhase ξ₀ 0) = literalCfg ξ₀ := by
  rw [commonPhase_zero]



/-! ## The right gauge is absorbed by the group -/

/-- The accepted right action fixes the quartet points and acts on the hidden points as `hW` says. -/
private theorem raw_nRM_stdAnchored (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W W' : Family) (Z : TitsComplexMatrix)
    (hW : ∀ (k : ℕ) (l : Label), nativeRightMultiply Z (nativeComplementaryPoint
      ((UnitaryErrorBases.ThreeCycleFourier.omega ^ k) • W l)) =
        nativeComplementaryPoint ((UnitaryErrorBases.ThreeCycleFourier.omega ^ k) • W' l))
    (i : Fin 39) :
    nativeRightMultiply Z (stdAnchored q W i) = stdAnchored q W' i := by
  unfold stdAnchored
  split_ifs
  · exact nativeRightMultiply_includeHermitianMatrix _ _
  · exact hW _ _

/-- Right multiplication by `hᴴ` moves the hidden matrices of `h₁ = 1` to those of `h`. -/
private theorem raw_hid_right (ξ₀ : Fin 4 → ℂ) (H : Fin 4) (g : Mat) (h₁ h : TitsComplexMatrix)
    (hh₁ : h₁ = 1) (d : PhaseTriple) (k : ℕ) (l : Label) :
    nativeRightMultiply hᴴ (nativeComplementaryPoint
      ((UnitaryErrorBases.ThreeCycleFourier.omega ^ k) • hidFamily ξ₀ H g h₁ d l)) =
      nativeComplementaryPoint
        ((UnitaryErrorBases.ThreeCycleFourier.omega ^ k) • hidFamily ξ₀ H g h d l) := by
  subst hh₁
  refine (nativeRightMultiply_complementaryPoint _ _).trans (congrArg nativeComplementaryPoint ?_)
  have key : ∀ (A B : Mat) (c : ℂ),
      ((UnitaryErrorBases.ThreeCycleFourier.omega ^ k) • (c • (A * (1 : Mat)ᴴ))) * B =
        (UnitaryErrorBases.ThreeCycleFourier.omega ^ k) • (c • (A * B)) := by
    intro A B c
    rw [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul]
  exact key (g * gaugeLeft ξ₀ H * monomialFamily d (gaugeLabel H l) * gaugeRight ξ₀ H) hᴴ
    (gaugeScalar H l)

/-- `preCfg g h d = actC (Ψ⁻¹ R_{hᴴ} Ψ) (preCfg g 1 d)` (`nativeRightMultiply_includeHermitianMatrix`,
`nativeRightMultiply_complementaryPoint`). -/
private theorem raw_preCfg_gauge (ξ₀ : Fin 4 → ℂ) (H : Fin 4) (g : Mat) (h : TitsComplexMatrix)
    (d : PhaseTriple) :
    preCfg ξ₀ H g h d =
      actC (coordEnd (anchorΨinv H ∘ₗ nativeRightMultiply hᴴ ∘ₗ anchorΨ H))
        (preCfg ξ₀ H g (suExp 0) d) := by
  funext i
  rw [actC_apply, coordEnd_apply]
  show NativePolynomial.upperCoordinates (prePoint ξ₀ H g h d i) =
    NativePolynomial.upperCoordinates ((anchorΨinv H ∘ₗ nativeRightMultiply hᴴ ∘ₗ anchorΨ H)
      (NativePolynomial.fromUpperCoordinates
        (NativePolynomial.upperCoordinates (prePoint ξ₀ H g (suExp 0) d i))))
  rw [NativePolynomial.fromUpperCoordinates_upperCoordinates]
  congr 1
  simp only [prePoint, LinearMap.comp_apply]
  rw [show anchorΨ H (anchorΨinv H (stdAnchored (anchorQuartet ξ₀ H) (hidFamily ξ₀ H g (suExp 0) d)
      ((anchorRelabel H).symm i))) = _ from LinearMap.congr_fun (anchorΨ_comp_anchorΨinv H) _,
    LinearMap.id_apply, raw_nRM_stdAnchored _ _ _ _ (raw_hid_right ξ₀ H g _ h suExp_zero d)]

/-- The transported right action of a special unitary `Z` is in `G`
(`nativeRightMultiply_jordan`, `nativeRightMultiply_trace`). -/
private theorem raw_gauge_mem_autC (H : Fin 4) {Z : TitsComplexMatrix} (hu : Z * Zᴴ = 1)
    (hd : Z.det = 1) :
    coordEnd (anchorΨinv H ∘ₗ nativeRightMultiply Zᴴ ∘ₗ anchorΨ H) ∈ autC := by
  rw [mem_autC_iff_isNativeAut, AlgEquiv.symm_apply_apply]
  have hu' : Zᴴ * Z = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hu
  have hΨ : ∀ x, anchorΨ H (anchorΨinv H x) = x :=
    fun x => LinearMap.congr_fun (anchorΨ_comp_anchorΨinv H) x
  have hΨ' : ∀ x, anchorΨinv H (anchorΨ H x) = x :=
    fun x => LinearMap.congr_fun (anchorΨinv_comp_anchorΨ H) x
  have hR : IsNativeAut (nativeRightMultiply Zᴴ) :=
    ⟨nativeRightMultiply_jordan Zᴴ (by rw [Matrix.conjTranspose_conjTranspose]; exact hu')
      (by rw [Matrix.det_conjTranspose, hd, star_one]), nativeRightMultiply_trace Zᴴ⟩
  refine ⟨?_, (anchorΨinv_isNativeAut H).comp (hR.comp (anchorΨ_isNativeAut H))⟩
  refine Function.bijective_iff_has_inverse.2
    ⟨anchorΨinv H ∘ₗ nativeRightMultiply Z ∘ₗ anchorΨ H, fun x => ?_, fun x => ?_⟩
  · simp only [LinearMap.comp_apply]
    rw [hΨ, nativeRightMultiply_comp, hu', nativeRightMultiply_one, hΨ']
  · simp only [LinearMap.comp_apply]
    rw [hΨ, nativeRightMultiply_comp, hu, nativeRightMultiply_one, hΨ']

/-- Every point of the seventy-parameter family is a `G`-translate of the `h = 1` family. -/
private theorem raw_rawMap_eq {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (p : RawParam) :
    ∃ A ∈ autC, rawMap ξ₀ hξ₀ H p = actC A (preMap ξ₀ hξ₀ H (p.2.1, 0, p.2.2.2)) := by
  refine ⟨groupChart p.1 *
      coordEnd (anchorΨinv H ∘ₗ nativeRightMultiply (suExp p.2.2.1)ᴴ ∘ₗ anchorΨ H),
    mul_mem_autOf (groupChart_mem_autC _)
      (raw_gauge_mem_autC H (suExp_mul_conjTranspose _) (suExp_det _)), ?_⟩
  rw [actC_mul, ContinuousLinearMap.comp_apply]
  exact congrArg (actC (groupChart p.1))
    (raw_preCfg_gauge ξ₀ H (suExp p.2.1) (suExp p.2.2.1) (torusPhase (anchorTriple ξ₀ hξ₀ H) p.2.2.2))

/-- The seventy-parameter family has the same germ as the sixty-two-parameter one: every point is a
`G`-translate of an `h = 1` point (`raw_rawMap_eq`), and `h = 1` is a sub-family. -/
private theorem raw_germ70 {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4)
    {M : Set ↥(normalC ξ₀)} (hM : IsGermImage M 0 (sliceFam ξ₀ hξ₀ H) 0) {Tg : Set Cfg}
    (hTg : Tg ∈ 𝓝 (literalCfg ξ₀)) :
    IsGermImage {y | y ∈ Tg ∧ sliceRep ξ₀ hξ₀ y ∈ M} (literalCfg ξ₀) (rawMap ξ₀ hξ₀ H) 0 := by
  have hb := raw_famb_cont hξ₀ H
  have hb0 := raw_famb_zero hξ₀ H
  obtain ⟨V, hV, h1⟩ := raw_cover1 hξ₀ hb hb0 hM
  let π : RawParam → SliceParam := fun z => (z.2.1, z.2.2.2)
  have hπ : Continuous π := (continuous_fst.comp continuous_snd).prodMk
    (continuous_snd.comp (continuous_snd.comp continuous_snd))
  refine raw_isGermImage_of (U₀ := π ⁻¹' V) (hπ.continuousAt.preimage_mem_nhds hV) ?_ ?_
  · filter_upwards [h1, hTg] with y hy hyT
    rintro ⟨z, hz, rfl⟩
    obtain ⟨A, hA, hAz⟩ := raw_rawMap_eq hξ₀ H z
    exact ⟨hyT, hy (π z) hz A hA hAz.symm⟩
  · intro U hU
    let ι : RawParam62 → RawParam := fun z => (z.1, z.2.1, 0, z.2.2)
    have hι : Continuous ι := continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
      (continuous_const.prodMk (continuous_snd.comp continuous_snd)))
    have hU' : ι ⁻¹' U ∈ 𝓝 ((0 : ↥derC), (0 : SliceParam)) := hι.continuousAt.preimage_mem_nhds hU
    filter_upwards [raw_cover2 hξ₀ hb hb0 hM _ hU'] with y hy hyS
    obtain ⟨z, hz, hzy⟩ := hy hyS.2
    exact ⟨ι z, hz, hzy⟩

/-! ## The raw chart -/

/-- Linear maps out of finite-dimensional normed spaces are analytic (stated through `→ₗ` so that only
the norm topologies are involved). -/
private theorem raw_analyticAt_linear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E →ₗ[ℝ] F) (x : E) :
    AnalyticAt ℝ f x :=
  (LinearMap.toContinuousLinearMap f).analyticAt x

private theorem raw_analyticAt_isLinear {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : IsLinearMap ℝ f) (x : E) : AnalyticAt ℝ f x :=
  raw_analyticAt_linear (IsLinearMap.mk' f hf) x

private theorem raw_finrank :
    Module.finrank ℝ (Fin 56 → ℝ) = Module.finrank ℝ (↥derC × (Fin 4 → ℝ)) := by
  have : Module.Free ℝ ↥derC := Module.Free.of_divisionRing ℝ ↥derC
  rw [Module.finrank_prod, finrank_derC, Module.finrank_fin_fun, Module.finrank_fin_fun]

/-- `ℝ⁵⁶ ≃ derC × ℝ⁴` (`finrank_derC = 52`). -/
private def raw_L : (Fin 56 → ℝ) ≃L[ℝ] (↥derC × (Fin 4 → ℝ)) :=
  ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := Fin 56 → ℝ) (F := ↥derC × (Fin 4 → ℝ))
    raw_finrank

/-- Regrouping `ℝ⁵⁶ × (ℝ⁶)⁴ × ℝ⁹⁷³ ≃ derC × (ℝ⁴ × (ℝ⁶)⁴ × ℝ⁹⁷³)`: the common coordinate `ℝ⁴` of the
slice model sits in the `ℝ⁵⁶` block. -/
private def raw_E : RawModel ≃L[ℝ] (↥derC × SliceModel) :=
  (raw_L.prodCongr (ContinuousLinearEquiv.refl ℝ ((Fin 4 → Fin 6 → ℝ) × (Fin 973 → ℝ)))).trans
    (ContinuousLinearEquiv.prodAssoc ℝ ↥derC (Fin 4 → ℝ) ((Fin 4 → Fin 6 → ℝ) × (Fin 973 → ℝ)))

/-- The group/slice chart restricted to where its inverse is analytic. -/
private def rawT (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) :
    OpenPartialHomeomorph (↥derC × ↥(normalC ξ₀)) Cfg :=
  ((slicePH ξ₀ hξ₀).symm.restrOpen {y | AnalyticAt ℝ (slicePH ξ₀ hξ₀).symm y}
    (isOpen_analyticAt ℝ _)).symm

/-- The raw chart `(L × id × id) ≫ (id × Φs) ≫ slicePH`. -/
private def rawChart {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀)
    (Φs : OpenPartialHomeomorph SliceModel ↥(normalC ξ₀)) : OpenPartialHomeomorph RawModel Cfg :=
  raw_E.toHomeomorph.toOpenPartialHomeomorph.trans
    (((OpenPartialHomeomorph.refl ↥derC).prod Φs).trans (rawT ξ₀ hξ₀))

section Chart

variable {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (Φs : OpenPartialHomeomorph SliceModel ↥(normalC ξ₀))

private theorem raw_chart_apply (z : RawModel) :
    rawChart hξ₀ Φs z = sliceChart ξ₀ ((raw_E z).1, Φs (raw_E z).2) := by
  rw [← slicePH_coe ξ₀ hξ₀]
  rfl

private theorem raw_chart_symm_apply (y : Cfg) :
    (rawChart hξ₀ Φs).symm y =
      raw_E.symm (((slicePH ξ₀ hξ₀).symm y).1, Φs.symm ((slicePH ξ₀ hξ₀).symm y).2) := rfl

private theorem raw_mem_chart_source (z : RawModel) :
    z ∈ (rawChart hξ₀ Φs).source ↔
      (raw_E z).2 ∈ Φs.source ∧ ((raw_E z).1, Φs (raw_E z).2) ∈ (rawT ξ₀ hξ₀).source := by
  simp [rawChart]

private theorem raw_chart_target {y : Cfg} (hy : y ∈ (rawChart hξ₀ Φs).target) :
    y ∈ (rawT ξ₀ hξ₀).target ∧ ((slicePH ξ₀ hξ₀).symm y).2 ∈ Φs.target := by
  rw [rawChart, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.trans_target] at hy
  exact ⟨hy.1.1, hy.1.2.2⟩

include hξ₀ in
private theorem raw_rawT_target_mem : (rawT ξ₀ hξ₀).target ∈ 𝓝 (literalCfg ξ₀) :=
  Filter.inter_mem (raw_target_mem hξ₀)
    ((isOpen_analyticAt ℝ _).mem_nhds (analyticAt_slicePH_symm ξ₀ hξ₀))

/-- The chart image of a block `{z | z.2 ∈ R}` is the set of points whose slice coordinate lies in the
slice chart image of the corresponding slice block. -/
private theorem raw_chart_image (R : Set ((Fin 4 → Fin 6 → ℝ) × (Fin 973 → ℝ))) :
    rawChart hξ₀ Φs '' ((rawChart hξ₀ Φs).source ∩ {z | z.2 ∈ R}) =
      {y | y ∈ (rawT ξ₀ hξ₀).target ∧ sliceRep ξ₀ hξ₀ y ∈ Φs '' (Φs.source ∩ {s | s.2 ∈ R})} := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzs, hzR⟩, rfl⟩
    have hT := ((raw_mem_chart_source hξ₀ Φs z).1 hzs)
    refine ⟨(raw_chart_target hξ₀ Φs ((rawChart hξ₀ Φs).map_source hzs)).1, ?_⟩
    have hl := (rawT ξ₀ hξ₀).left_inv hT.2
    refine ⟨(raw_E z).2, ⟨hT.1, hzR⟩, ?_⟩
    show Φs (raw_E z).2 = ((rawT ξ₀ hξ₀).symm (rawT ξ₀ hξ₀ ((raw_E z).1, Φs (raw_E z).2))).2
    rw [hl]
  · rintro ⟨hyT, s, ⟨hs, hsR⟩, hsy⟩
    have hE : raw_E (raw_E.symm (((slicePH ξ₀ hξ₀).symm y).1, s)) =
        (((slicePH ξ₀ hξ₀).symm y).1, s) := raw_E.apply_symm_apply _
    have hw : (((slicePH ξ₀ hξ₀).symm y).1, Φs s) = (rawT ξ₀ hξ₀).symm y :=
      Prod.ext rfl hsy
    refine ⟨raw_E.symm (((slicePH ξ₀ hξ₀).symm y).1, s), ⟨?_, ?_⟩, ?_⟩
    · rw [raw_mem_chart_source, hE]
      exact ⟨hs, by rw [hw]; exact (rawT ξ₀ hξ₀).map_target hyT⟩
    · show (raw_E.symm (((slicePH ξ₀ hξ₀).symm y).1, s)).2 ∈ R
      have h2 : (raw_E (raw_E.symm (((slicePH ξ₀ hξ₀).symm y).1, s))).2.2 = s.2 := by rw [hE]
      have h3 : (raw_E.symm (((slicePH ξ₀ hξ₀).symm y).1, s)).2 = s.2 := h2
      rw [h3]
      exact hsR
    · show rawT ξ₀ hξ₀ ((raw_E (raw_E.symm (((slicePH ξ₀ hξ₀).symm y).1, s))).1,
        Φs (raw_E (raw_E.symm (((slicePH ξ₀ hξ₀).symm y).1, s))).2) = y
      rw [hE, hw]
      exact (rawT ξ₀ hξ₀).right_inv hyT

end Chart

/-- One analytic chart `ℝ⁵⁶ × (ℝ⁶)⁴ × ℝ⁹⁷³ → Cfg` straightening the four raw 62-dimensional family
germs and the common raw 56-dimensional germ. -/
theorem exists_raw_chart {ξ₀ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ₀) :
    ∃ Φ : OpenPartialHomeomorph RawModel Cfg,
      (0 : RawModel) ∈ Φ.source ∧ Φ 0 = literalCfg ξ₀ ∧
      AnalyticOnNhd ℝ Φ Φ.source ∧ AnalyticOnNhd ℝ Φ.symm Φ.target ∧
      IsGermImage (Φ '' (Φ.source ∩ commonBlock (Fin 4) (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ)))
        (literalCfg ξ₀) (commonMap ξ₀) 0 ∧
      (∀ H, IsGermImage (Φ '' (Φ.source ∩ familyBlock (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H))
        (literalCfg ξ₀) (rawMap62 ξ₀ hξ.1 H) 0) ∧
      (∀ H, IsGermImage (Φ '' (Φ.source ∩ familyBlock (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H))
        (literalCfg ξ₀) (rawMap ξ₀ hξ.1 H) 0) ∧
      (∀ H H', H ≠ H' →
        Φ '' (Φ.source ∩ familyBlock (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H) ∩
            Φ '' (Φ.source ∩ familyBlock (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H') =
          Φ '' (Φ.source ∩ commonBlock (Fin 4) (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ))) := by
  obtain ⟨Φs, h0s, hΦ0, hΦan, hΦsan, hcom, hfam, -⟩ := exists_slice_chart hξ
  have hTg := raw_rawT_target_mem hξ.1
  have hE0 : raw_E (0 : RawModel) = 0 := map_zero _
  have hfb : ∀ H : Fin 4, familyBlock (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H =
      {z : RawModel | z.2 ∈ {w : (Fin 4 → Fin 6 → ℝ) × (Fin 973 → ℝ) |
        (∀ j, j ≠ H → w.1 j = 0) ∧ w.2 = 0}} := fun H => rfl
  refine ⟨rawChart hξ.1 Φs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [raw_mem_chart_source, hE0]
    refine ⟨h0s, ?_⟩
    show ((0 : ↥derC), Φs 0) ∈ (rawT ξ₀ hξ.1).source
    rw [hΦ0]
    refine ⟨zero_mem_slicePH_source ξ₀ hξ.1, ?_⟩
    show AnalyticAt ℝ (slicePH ξ₀ hξ.1).symm (slicePH ξ₀ hξ.1 0)
    rw [slicePH_coe, sliceChart_zero]
    exact analyticAt_slicePH_symm ξ₀ hξ.1
  · rw [raw_chart_apply, hE0]
    show sliceChart ξ₀ (0, Φs 0) = _
    rw [hΦ0]
    exact sliceChart_zero ξ₀
  · intro z hz
    obtain ⟨hs, -⟩ := (raw_mem_chart_source hξ.1 Φs z).1 hz
    rw [show ⇑(rawChart hξ.1 Φs) = fun z => sliceChart ξ₀ ((raw_E z).1, Φs (raw_E z).2) from
      funext (raw_chart_apply hξ.1 Φs)]
    have hEa : AnalyticAt ℝ raw_E z :=
      raw_analyticAt_isLinear ⟨fun a b => map_add raw_E a b, fun c a => map_smul raw_E c a⟩ z
    have hE1 : AnalyticAt ℝ (fun z => (raw_E z).1) z := analyticAt_fst.comp hEa
    have hE2 : AnalyticAt ℝ (fun z => (raw_E z).2) z := analyticAt_snd.comp hEa
    have hE3 : AnalyticAt ℝ (fun z => Φs (raw_E z).2) z :=
      AnalyticAt.comp (g := Φs) (f := fun z => (raw_E z).2) (hΦan _ hs) hE2
    exact (analyticAt_sliceChart ξ₀ _).comp (hE1.prod hE3)
  · intro y hy
    obtain ⟨⟨-, hya'⟩, hyt⟩ := raw_chart_target hξ.1 Φs hy
    have hya : AnalyticAt ℝ (slicePH ξ₀ hξ.1).symm y := hya'
    rw [show ⇑(rawChart hξ.1 Φs).symm = fun y => raw_E.symm (((slicePH ξ₀ hξ.1).symm y).1,
        Φs.symm ((slicePH ξ₀ hξ.1).symm y).2) from funext (raw_chart_symm_apply hξ.1 Φs)]
    have h1 : AnalyticAt ℝ (fun y => ((slicePH ξ₀ hξ.1).symm y).1) y := analyticAt_fst.comp hya
    have h2 : AnalyticAt ℝ (fun y => ((slicePH ξ₀ hξ.1).symm y).2) y := analyticAt_snd.comp hya
    have h3 : AnalyticAt ℝ (fun y => Φs.symm ((slicePH ξ₀ hξ.1).symm y).2) y :=
      AnalyticAt.comp (g := Φs.symm) (f := fun y => ((slicePH ξ₀ hξ.1).symm y).2) (hΦsan _ hyt) h2
    exact (raw_analyticAt_linear raw_E.symm.toLinearEquiv.toLinearMap _).comp (h1.prod h3)
  · rw [show commonBlock (Fin 4) (Fin 56 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) =
      {z : RawModel | z.2 ∈ {w : (Fin 4 → Fin 6 → ℝ) × (Fin 973 → ℝ) | w.1 = 0 ∧ w.2 = 0}} from rfl,
      raw_chart_image]
    exact raw_germ hξ.1 (raw_comb_cont hξ.1) (raw_comb_zero ξ₀) hcom hTg
  · intro H
    rw [hfb, raw_chart_image]
    exact raw_germ hξ.1 (raw_famb_cont hξ.1 H) (raw_famb_zero hξ.1 H) (hfam H) hTg
  · intro H
    rw [hfb, raw_chart_image]
    exact raw_germ70 hξ.1 H (hfam H) hTg
  · intro H H' hne
    rw [← (rawChart hξ.1 Φs).injOn.image_inter Set.inter_subset_left Set.inter_subset_left]
    congr 1
    ext z
    simp only [Set.mem_inter_iff, familyBlock, commonBlock, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hz, h1, h2⟩, -, h1', -⟩
      refine ⟨hz, funext fun j => ?_, h2⟩
      by_cases hj : j = H
      · rw [hj]
        exact h1' H hne
      · exact h1 j hj
    · rintro ⟨hz, h1, h2⟩
      exact ⟨⟨hz, fun j _ => by rw [h1]; rfl, h2⟩, hz, fun j _ => by rw [h1]; rfl, h2⟩

/-- The slice family germ is the raw family germ intersected with the slice. -/
theorem sliceFam_germ_eq_raw_inter_slice {ξ₀ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ₀) (H : Fin 4) :
    ∃ V₀ ∈ 𝓝 (0 : RawParam62), ∀ U₀ ∈ 𝓝 (0 : RawParam62), U₀ ⊆ V₀ →
      IsGermImage (rawMap62 ξ₀ hξ.1 H '' U₀ ∩ sliceSet ξ₀) (literalCfg ξ₀)
        (fun p => literalCfg ξ₀ + ↑(sliceFam ξ₀ hξ.1 H p)) 0 := by
  obtain ⟨Φs, -, -, -, -, -, hfam, -⟩ := exists_slice_chart hξ
  exact raw_germ_slice hξ.1 (raw_famb_cont hξ.1 H) (raw_famb_zero hξ.1 H) (hfam H)

/-- The common slice germ is the common raw germ intersected with the slice. -/
theorem sliceCommon_germ_eq_raw_inter_slice {ξ₀ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ₀) :
    ∃ V₀ ∈ 𝓝 (0 : CommonParam), ∀ U₀ ∈ 𝓝 (0 : CommonParam), U₀ ⊆ V₀ →
      IsGermImage (commonMap ξ₀ '' U₀ ∩ sliceSet ξ₀) (literalCfg ξ₀)
        (fun θ => literalCfg ξ₀ + ↑(sliceCommon ξ₀ hξ.1 θ)) 0 := by
  obtain ⟨Φs, -, -, -, -, hcom, -, -⟩ := exists_slice_chart hξ
  exact raw_germ_slice hξ.1 (raw_comb_cont hξ.1) (raw_comb_zero ξ₀) hcom

/-- Labelled quotient: the raw family descends to its slice germ (inside the group/slice package's
open embedding of slice germs into the orbit space). -/
theorem rawFamily_descends {ξ₀ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ₀) (H : Fin 4) :
    ∃ W : Set Cfg, IsOpen W ∧ literalCfg ξ₀ ∈ W ∧ Topology.IsOpenEmbedding (sliceToOrbit ξ₀ W) ∧
      ∃ U₀ ∈ 𝓝 (0 : RawParam62), ∃ V₀ ∈ 𝓝 (0 : SliceParam),
        (∀ p ∈ V₀, literalCfg ξ₀ + ↑(sliceFam ξ₀ hξ.1 H p) ∈ W ∩ sliceSet ξ₀ ∩ zeroSet) ∧
        ∀ᶠ y in 𝓝 (literalCfg ξ₀), (y ∈ rawMap62 ξ₀ hξ.1 H '' U₀ ↔
          ∃ p ∈ V₀, ∃ A ∈ autC, actC A (literalCfg ξ₀ + ↑(sliceFam ξ₀ hξ.1 H p)) = y) :=
  raw_descends hξ.1 (raw_famb_cont hξ.1 H) (raw_famb_zero hξ.1 H)
    (eventually_originalF_sliceFam hξ.1 H)

/-- The same descent for the common germ. -/
theorem common_descends {ξ₀ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ₀) :
    ∃ W : Set Cfg, IsOpen W ∧ literalCfg ξ₀ ∈ W ∧ Topology.IsOpenEmbedding (sliceToOrbit ξ₀ W) ∧
      ∃ U₀ ∈ 𝓝 (0 : CommonParam), ∃ V₀ ∈ 𝓝 (0 : Fin 4 → ℝ),
        (∀ θ ∈ V₀, literalCfg ξ₀ + ↑(sliceCommon ξ₀ hξ.1 θ) ∈ W ∩ sliceSet ξ₀ ∩ zeroSet) ∧
        ∀ᶠ y in 𝓝 (literalCfg ξ₀), (y ∈ commonMap ξ₀ '' U₀ ↔
          ∃ θ ∈ V₀, ∃ A ∈ autC, actC A (literalCfg ξ₀ + ↑(sliceCommon ξ₀ hξ.1 θ)) = y) :=
  raw_descends hξ.1 (raw_comb_cont hξ.1) (raw_comb_zero ξ₀) (eventually_originalF_sliceCommon hξ.1)

end CKM.NativeFourFamily

#print axioms CKM.NativeFourFamily.exists_raw_chart
#print axioms CKM.NativeFourFamily.sliceFam_germ_eq_raw_inter_slice
#print axioms CKM.NativeFourFamily.sliceCommon_germ_eq_raw_inter_slice
#print axioms CKM.NativeFourFamily.rawFamily_descends
#print axioms CKM.NativeFourFamily.common_descends

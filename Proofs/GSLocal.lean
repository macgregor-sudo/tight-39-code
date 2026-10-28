module

public import GSResidual

@[expose] public section

/-!
# The full local orbit relation on the transverse slice

`sliceSet ξ = P + N(ξ)`. After shrinking, two slice points near `P` related by **any** element of
the full compact group `G` are equal.

Route (MASTER §6.8). Otherwise there are slice points `s_n, t_n → P`, `s_n ≠ t_n`, and `A_n ∈ G`
with `A_n • s_n = t_n`. By `isCompact_autC` a subsequence `A_n → A ∈ G`; continuity gives
`A • P = P`, so `A = 1` (`actC_literalCfg_eq_iff`). Hence eventually `A_n = groupChart D_n` with
`D_n → 0` (`exists_groupChart_local`, continuity of the analytic inverse chart), and
`slicePH (D_n, s_n - P) = t_n = slicePH (0, t_n - P)` with both points in the source; injectivity
on the source gives `s_n = t_n`, a contradiction.
-/

noncomputable section

namespace CKM.NativeGroupSlice

open Glennie NativePolynomial CKM.NativeFirstOrder
open scoped Topology

/-- The transverse affine slice `P + N(ξ)`. -/
def sliceSet (ξ : Fin 4 → ℂ) : Set Cfg := {C | C - literalCfg ξ ∈ normalC ξ}

theorem literalCfg_mem_sliceSet (ξ : Fin 4 → ℂ) : literalCfg ξ ∈ sliceSet ξ := by
  show literalCfg ξ - literalCfg ξ ∈ normalC ξ
  rw [sub_self]
  exact (normalC ξ).zero_mem

/-- Properness step: off a given open neighbourhood `W₁` of the identity, no group element moves a
point near `P` to a point near `P`. Uses compactness of `G \ W₁` and the trivial stabilizer. -/
private theorem local_eventually_ne_off_nhd (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {W₁ : Set CEnd}
    (hW₁ : IsOpen W₁) (h1 : (1 : CEnd) ∈ W₁) :
    ∀ᶠ x : Cfg × Cfg in 𝓝 (literalCfg ξ, literalCfg ξ), ∀ A ∈ autC \ W₁, actC A x.1 ≠ x.2 := by
  refine (isCompact_autC.diff hW₁).eventually_forall_of_forall_eventually ?_
  intro A hA
  have hne : actC A (literalCfg ξ) ≠ literalCfg ξ := by
    intro h
    exact hA.2 (((actC_literalCfg_eq_iff ξ hξ A).1 h) ▸ h1)
  have hcont : Continuous fun z : (Cfg × Cfg) × CEnd => (actC z.2 z.1.1, z.1.2) := by
    have h2 : Continuous fun z : (Cfg × Cfg) × CEnd => actC z.2 z.1.1 :=
      actC.continuous₂.comp (continuous_snd.prodMk (continuous_fst.comp continuous_fst))
    exact h2.prodMk (continuous_snd.comp continuous_fst)
  have hopen : IsOpen {p : Cfg × Cfg | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  exact (hcont.continuousAt (x := ((literalCfg ξ, literalCfg ξ), A))).preimage_mem_nhds
    (hopen.mem_nhds hne)

/-- **Full local orbit relation.** -/
theorem exists_local_orbit_injective (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    ∃ W ∈ 𝓝 (literalCfg ξ), ∀ s ∈ W ∩ sliceSet ξ, ∀ t ∈ W ∩ sliceSet ξ,
      ∀ A ∈ autC, actC A s = t → s = t := by
  set P := literalCfg ξ
  set e := slicePH ξ hξ
  obtain ⟨U, Wg, inv, -, h0U, hWg, h1Wg, -, -, hinvg, hinvD, hinvan⟩ := exists_groupChart_local
  -- a product neighbourhood of `0` inside the source of the slice chart
  have hS : e.source ∈ 𝓝 ((0 : derC), (0 : normalC ξ)) :=
    e.open_source.mem_nhds (zero_mem_slicePH_source ξ hξ)
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hS
  obtain ⟨ε, hε, hεv⟩ := Metric.mem_nhds_iff.1 hv
  -- the inverse chart is continuous at `1` with value `0`
  have hinv1 : inv 1 = 0 := by
    have := hinvD 0 h0U
    rwa [groupChart_zero] at this
  have hW₁ : Wg ∩ inv ⁻¹' u ∈ 𝓝 (1 : CEnd) := by
    refine Filter.inter_mem (hWg.mem_nhds h1Wg) ?_
    exact (hinvan 1 h1Wg).continuousAt.preimage_mem_nhds (by rw [hinv1]; exact hu)
  have hev := local_eventually_ne_off_nhd ξ hξ isOpen_interior (mem_interior_iff_mem_nhds.2 hW₁)
  obtain ⟨a, ha, b, hb, hab⟩ := mem_nhds_prod_iff.1 hev
  refine ⟨a ∩ b ∩ Metric.ball P ε, Filter.inter_mem (Filter.inter_mem ha hb)
    (Metric.ball_mem_nhds P hε), ?_⟩
  rintro s ⟨⟨⟨hsa, -⟩, hsε⟩, hsS⟩ t ⟨⟨⟨-, htb⟩, htε⟩, htS⟩ A hA hAst
  -- `A` lies in the chart neighbourhood of the identity
  have hAW : A ∈ Wg ∩ inv ⁻¹' u := by
    by_contra hAW
    have hAK : A ∈ autC \ interior (Wg ∩ inv ⁻¹' u) := ⟨hA, fun h => hAW (interior_subset h)⟩
    exact hab (Set.mk_mem_prod hsa htb) A hAK hAst
  obtain ⟨-, hgA⟩ := hinvg A ⟨hA, hAW.1⟩
  set ns : normalC ξ := ⟨s - P, hsS⟩
  set nt : normalC ξ := ⟨t - P, htS⟩
  have hns : ns ∈ v := hεv (by
    rw [mem_ball_zero_iff]
    show ‖s - P‖ < ε
    rwa [← dist_eq_norm])
  have hnt : nt ∈ v := hεv (by
    rw [mem_ball_zero_iff]
    show ‖t - P‖ < ε
    rwa [← dist_eq_norm])
  have h1src : (inv A, ns) ∈ e.source := huv (Set.mk_mem_prod hAW.2 hns)
  have h2src : ((0 : derC), nt) ∈ e.source := huv (Set.mk_mem_prod (mem_of_mem_nhds hu) hnt)
  have he1 : e (inv A, ns) = t := by
    show sliceChart ξ (inv A, ns) = t
    have hsP : literalCfg ξ + (s - P) = s := add_sub_cancel P s
    simp only [sliceChart, hgA, ns]
    rw [hsP, hAst]
  have he2 : e ((0 : derC), nt) = t := by
    show sliceChart ξ ((0 : derC), nt) = t
    rw [sliceChart_zero_left]
    exact add_sub_cancel P t
  have heq := e.injOn h1src h2src (he1.trans he2.symm)
  have hn : (s - P : Cfg) = t - P := congrArg Subtype.val (congrArg Prod.snd heq)
  exact sub_left_injective hn

/-- Every configuration near `P` is `G`-related, by an element of the chart, to a slice point near
`P`: for each neighbourhood `V` of `P` there is a neighbourhood `W` with
`C ∈ W → ∃ D, groupChart D • (slice point in V) = C`. -/
theorem exists_slice_representative (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {V : Set Cfg}
    (hV : V ∈ 𝓝 (literalCfg ξ)) :
    ∃ W ∈ 𝓝 (literalCfg ξ), ∀ C ∈ W, ∃ D : derC, ∃ s ∈ V ∩ sliceSet ξ, actC (groupChart D) s = C := by
  set P := literalCfg ξ
  set e := slicePH ξ hξ
  have hT : e.target ∈ 𝓝 P := e.open_target.mem_nhds (literalCfg_mem_slicePH_target ξ hξ)
  let g : Cfg → Cfg := fun C => P + ((e.symm C).2 : Cfg)
  have hg : ContinuousAt g P := by
    have hsymm : ContinuousAt e.symm P := e.continuousAt_symm (literalCfg_mem_slicePH_target ξ hξ)
    exact continuousAt_const.add
      (continuous_subtype_val.continuousAt.comp (continuous_snd.continuousAt.comp hsymm))
  have hgP : g P = P := by
    have h0 : e.symm P = 0 := slicePH_symm_literalCfg ξ hξ
    simp only [g, h0, Prod.snd_zero, ZeroMemClass.coe_zero, add_zero]
  have hgV : g ⁻¹' V ∈ 𝓝 P := hg.preimage_mem_nhds (by rw [hgP]; exact hV)
  refine ⟨e.target ∩ g ⁻¹' V, Filter.inter_mem hT hgV, ?_⟩
  rintro C ⟨hCT, hCV⟩
  refine ⟨(e.symm C).1, g C, ⟨hCV, ?_⟩, ?_⟩
  · show g C - P ∈ normalC ξ
    simp only [g, add_sub_cancel_left]
    exact (e.symm C).2.2
  · have h := e.right_inv hCT
    exact h

#print axioms literalCfg_mem_sliceSet
#print axioms exists_local_orbit_injective
#print axioms exists_slice_representative

end CKM.NativeGroupSlice

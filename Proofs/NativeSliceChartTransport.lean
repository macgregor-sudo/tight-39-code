module

public import NativeRawSolutionPatchesWithin
public import A5Main

@[expose] public section

/-! Local native orbit uniqueness transports sufficiently small raw family
parameters into the SAME A5 slice-chart block. The ambient product chart then
projects whole-solution open patches to whole-slice open patches.
 -/

noncomputable section
namespace Option2.NativeStress.SliceChartTransportA7
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open PhasePivotA6 PhasePivotLocusA6 RawSolutionPatchesWithinA7
open Filter
open scoped Topology

section NativeOrbit
variable {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀)
private theorem transport_gc_neg_mul (D : ↥derC) : groupChart (-D) * groupChart D = 1 := by
  show NormedSpace.exp ((-D : ↥derC) : CEnd) * NormedSpace.exp (D : CEnd) = 1
  rw [Submodule.coe_neg]
  exact exp_neg_mul_exp _

private theorem transport_actC_cancel (D : ↥derC) (C : Cfg) :
    actC (groupChart (-D)) (actC (groupChart D) C) = C := by
  rw [← ContinuousLinearMap.comp_apply, ← actC_mul, transport_gc_neg_mul, actC_one]
  rfl

include hξ₀ in
private theorem transport_target_mem : (slicePH ξ₀ hξ₀).target ∈ 𝓝 (literalCfg ξ₀) :=
  (slicePH ξ₀ hξ₀).open_target.mem_nhds (literalCfg_mem_slicePH_target ξ₀ hξ₀)

private theorem transport_mem_sliceSet (n : ↥(normalC ξ₀)) : literalCfg ξ₀ + ↑n ∈ sliceSet ξ₀ := by
  show literalCfg ξ₀ + ↑n - literalCfg ξ₀ ∈ normalC ξ₀
  rw [add_sub_cancel_left]
  exact n.2

private theorem transport_decomp {y : Cfg} (hy : y ∈ (slicePH ξ₀ hξ₀).target) :
    actC (groupChart ((slicePH ξ₀ hξ₀).symm y).1) (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ y)) = y := by
  have h := (slicePH ξ₀ hξ₀).right_inv hy
  rw [slicePH_coe] at h
  exact h

private theorem transport_undecomp {y : Cfg} (hy : y ∈ (slicePH ξ₀ hξ₀).target) :
    actC (groupChart (-((slicePH ξ₀ hξ₀).symm y).1)) y =
      literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ y) := by
  have h := transport_actC_cancel (((slicePH ξ₀ hξ₀).symm y).1) (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ y))
  rw [transport_decomp hξ₀ hy] at h
  exact h

private theorem transport_tendsto_fst :
    Tendsto (fun y => ((slicePH ξ₀ hξ₀).symm y).1) (𝓝 (literalCfg ξ₀)) (𝓝 0) := by
  have h := (continuous_fst.continuousAt.comp
    ((slicePH ξ₀ hξ₀).continuousAt_symm (literalCfg_mem_slicePH_target ξ₀ hξ₀))).tendsto
  rw [Function.comp_apply, slicePH_symm_literalCfg] at h
  exact h

private theorem transport_tendsto_rep :
    Tendsto (sliceRep ξ₀ hξ₀) (𝓝 (literalCfg ξ₀)) (𝓝 0) := by
  have h := (continuous_snd.continuousAt.comp
    ((slicePH ξ₀ hξ₀).continuousAt_symm (literalCfg_mem_slicePH_target ξ₀ hξ₀))).tendsto
  rw [Function.comp_apply, slicePH_symm_literalCfg] at h
  exact h

private theorem transport_tendsto_add {α : Type*} {l : Filter α} {f : α → ↥(normalC ξ₀)}
    (hf : Tendsto f l (𝓝 0)) :
    Tendsto (fun a => literalCfg ξ₀ + ↑(f a)) l (𝓝 (literalCfg ξ₀)) := by
  have h := (tendsto_const_nhds (x := literalCfg ξ₀)).add
    ((continuous_subtype_val.tendsto (0 : ↥(normalC ξ₀))).comp hf)
  rw [Submodule.coe_zero, add_zero] at h
  exact h

/-- Local orbit relation in slice coordinates: a point near `P` that is `G`-related to a slice point
`P + n` near `P` has slice coordinate `n` (`exists_local_orbit_injective`). -/
private theorem transport_orbit_rep :
    ∃ Wl ∈ 𝓝 (literalCfg ξ₀), ∀ᶠ y in 𝓝 (literalCfg ξ₀), ∀ n : ↥(normalC ξ₀),
      literalCfg ξ₀ + ↑n ∈ Wl → ∀ A ∈ autC, actC A (literalCfg ξ₀ + ↑n) = y →
        sliceRep ξ₀ hξ₀ y = n := by
  obtain ⟨Wl, hWl, hinj⟩ := exists_local_orbit_injective ξ₀ hξ₀
  refine ⟨Wl, hWl, ?_⟩
  filter_upwards [transport_target_mem hξ₀, hWl,
    (transport_tendsto_add (transport_tendsto_rep hξ₀)).eventually_mem hWl] with y hyT hyW hyW' n hn A hA hAy
  have hA' : groupChart (-((slicePH ξ₀ hξ₀).symm y).1) * A ∈ autC :=
    mul_mem_autOf (groupChart_mem_autC _) hA
  have h := hinj _ ⟨hn, transport_mem_sliceSet n⟩ _ ⟨hyW', transport_mem_sliceSet _⟩ _ hA'
    (by rw [actC_mul, ContinuousLinearMap.comp_apply, hAy, transport_undecomp hξ₀ hyT])
  exact (Subtype.ext (add_left_cancel h)).symm


end NativeOrbit

/-- This is the actual small native raw-family to slice-block interface. -/
theorem native_raw_to_slice_block {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ)
    (H : Fin 4) {M : Set ↥(normalC ξ)} (hM : IsGermImage M 0 (sliceFam ξ hξ H) 0) :
    ∃ B ∈ 𝓝 (0 : RawParam62), ∀ᶠ y in 𝓝 (literalCfg ξ),
      y ∈ rawMap62 ξ hξ H '' B → sliceRep ξ hξ y ∈ M := by
  let b : SliceParam → Cfg := fun p => preMap ξ hξ H (p.1,0,p.2)
  have hb : ContinuousAt b 0 := by
    have he : Continuous (fun p : SliceParam => (p.1,(0 : Fin 8 → ℝ),p.2)) :=
      continuous_fst.prodMk (continuous_const.prodMk continuous_snd)
    exact (analyticAt_preMap hξ H).continuousAt.comp_of_eq he.continuousAt rfl
  have hb0 : b 0 = literalCfg ξ := preMap_zero hξ H
  have hbt : Tendsto b (𝓝 0) (𝓝 (literalCfg ξ)) := hb0 ▸ hb.tendsto
  obtain ⟨Wl,hWl,hrep⟩ := transport_orbit_rep hξ
  obtain ⟨Ug,hUg,hgerm⟩ := hM
  have h0 := hgerm Ug hUg subset_rfl
  rw [eventuallyEqSet_iff] at h0
  have hσ : Tendsto (fun p => sliceRep ξ hξ (b p)) (𝓝 0) (𝓝 0) :=
    (transport_tendsto_rep hξ).comp hbt
  have hV := (hbt.eventually_mem (transport_target_mem hξ)).and
    (((transport_tendsto_add hσ).eventually_mem hWl).and
      ((Filter.eventually_mem_set.2 hUg).and (hσ.eventually h0)))
  refine ⟨Set.univ ×ˢ _,prod_mem_nhds Filter.univ_mem hV,?_⟩
  filter_upwards [hrep] with y hy
  rintro ⟨z,⟨_,hz⟩,rfl⟩
  obtain ⟨hpT,hpW,hpU,hpM⟩ := hz
  have he : sliceRep ξ hξ (rawMap62 ξ hξ H z) = sliceRep ξ hξ (b z.2) :=
    hy _ hpW (groupChart z.1 * groupChart ((slicePH ξ hξ).symm (b z.2)).1)
      (mul_mem_autOf (groupChart_mem_autC _) (groupChart_mem_autC _))
      (by rw [actC_mul,ContinuousLinearMap.comp_apply,transport_decomp hξ hpT]; rfl)
  rw [he]
  exact hpM.1 ⟨z.2,hpU,rfl⟩

#print axioms native_raw_to_slice_block
end Option2.NativeStress.SliceChartTransportA7

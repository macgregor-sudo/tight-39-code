module

public import A5SliceA
public import A5AnchorF

@[expose] public section

/-!
# Slice germs are pointwise `K`-fixed, lie in the zero set, and have the fixed tangent spaces
(piece SLICEB)

For `y = P + sliceFam p`, `y = A • preCfg(..)` with `A ∈ G` near `1`; `kAct H` fixes `preCfg`
exactly (`kAct_preCfg`), so `kAct H y = (kConj H A · A⁻¹) • y` with the group element near `1`; both
`y` and `kAct H y` lie in the slice (`kAct_literalCfg`, `kAct_mem_normalC`) near `P`, so they are
equal by the group/slice local orbit relation `exists_local_orbit_injective`. The common germ is fixed
by every generator. Derivatives of fixed analytic germs in the zero set lie in `(T ∩ N)^H`; dimensions
`10 = 10` and `4 = 4` (`finrank_fixQ`, `finrank_fixQK`) give equality.
-/

noncomputable section

open CKM.NativeFirstOrder CKM.NativeGroupSlice CompactAlbert UnitaryErrorBases
open scoped Matrix Topology

namespace CKM.NativeFourFamily

open Filter

/-- Core `K`-fixedness step. If `x a → P` and every `x a` is fixed by `kAct H`, then eventually
`y a = P + sliceRep (x a)` is fixed. Indeed `x a = g • y a` with `g ∈ G` (`eventually_eq_actC_sliceRep`),
so `x a = kAct H (x a) = kConj H g • kAct H (y a)` and `kAct H (y a) = (kConj H g)⁻¹ g • y a`; both points
lie in the slice near `P`, hence coincide by the local orbit relation `exists_local_orbit_injective`. -/
private theorem sliceB_eventually_kAct {α : Type*} {l : Filter α} {ξ₀ : Fin 4 → ℂ}
    (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (x : α → Cfg)
    (hx : Tendsto x l (𝓝 (literalCfg ξ₀))) (hfix : ∀ a, kAct H (x a) = x a) :
    ∀ᶠ a in l, kAct H (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (x a))) =
      literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (x a)) := by
  have hsymm : ContinuousAt (slicePH ξ₀ hξ₀).symm (literalCfg ξ₀) :=
    (slicePH ξ₀ hξ₀).continuousAt_symm (literalCfg_mem_slicePH_target ξ₀ hξ₀)
  have hc : ContinuousAt (fun y => literalCfg ξ₀ + (sliceRep ξ₀ hξ₀ y : Cfg)) (literalCfg ξ₀) :=
    continuousAt_const.add
      (continuous_subtype_val.continuousAt.comp (continuous_snd.continuousAt.comp hsymm))
  have h0 : literalCfg ξ₀ + (sliceRep ξ₀ hξ₀ (literalCfg ξ₀) : Cfg) = literalCfg ξ₀ := by
    rw [sliceRep_literalCfg hξ₀, Submodule.coe_zero, add_zero]
  have hrep : Tendsto (fun y => literalCfg ξ₀ + (sliceRep ξ₀ hξ₀ y : Cfg)) (𝓝 (literalCfg ξ₀))
      (𝓝 (literalCfg ξ₀)) := by
    have h := hc.tendsto
    simp only [h0] at h
    exact h
  have hK : Continuous (kAct H) := LinearMap.continuous_of_finiteDimensional _
  have hKP : kAct H (literalCfg ξ₀) = literalCfg ξ₀ := kAct_literalCfg hξ₀ H
  have hKt : Tendsto (fun y => kAct H (literalCfg ξ₀ + (sliceRep ξ₀ hξ₀ y : Cfg)))
      (𝓝 (literalCfg ξ₀)) (𝓝 (literalCfg ξ₀)) := by
    have h := (hK.tendsto (literalCfg ξ₀)).comp hrep
    rw [hKP] at h
    exact h
  obtain ⟨W, hW, hinj⟩ := exists_local_orbit_injective ξ₀ hξ₀
  have hev : ∀ᶠ y in 𝓝 (literalCfg ξ₀),
      (∃ D : ↥derC, y = actC (groupChart D) (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ y))) ∧
      literalCfg ξ₀ + (sliceRep ξ₀ hξ₀ y : Cfg) ∈ W ∧
      kAct H (literalCfg ξ₀ + (sliceRep ξ₀ hξ₀ y : Cfg)) ∈ W :=
    (eventually_eq_actC_sliceRep hξ₀).and ((hrep.eventually_mem hW).and (hKt.eventually_mem hW))
  filter_upwards [hx.eventually hev] with a ha
  obtain ⟨⟨D, hD⟩, hyW, hKyW⟩ := ha
  have hg : groupChart D ∈ autC := groupChart_mem_autC D
  have hB : kConj H (groupChart D) ∈ autC := kConj_mem_autC H hg
  have hBi := (mul_inverse_of_mem_autOf hB).2
  have h1 : actC (kConj H (groupChart D)) (kAct H (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (x a)))) =
      actC (groupChart D) (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (x a))) := by
    rw [← kAct_actC, ← hD]
    exact hfix a
  have h2 : actC (Ring.inverse (kConj H (groupChart D)) * groupChart D)
      (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (x a))) =
      kAct H (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (x a))) := by
    calc actC (Ring.inverse (kConj H (groupChart D)) * groupChart D)
          (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (x a)))
        = actC (Ring.inverse (kConj H (groupChart D)))
            (actC (groupChart D) (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (x a)))) := by
          rw [actC_mul]; rfl
      _ = actC (Ring.inverse (kConj H (groupChart D)))
            (actC (kConj H (groupChart D)) (kAct H (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (x a))))) := by
          rw [h1]
      _ = actC (Ring.inverse (kConj H (groupChart D)) * kConj H (groupChart D))
            (kAct H (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (x a)))) := by
          rw [actC_mul]; rfl
      _ = kAct H (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (x a))) := by
          rw [hBi, actC_one]; rfl
  have hyS : literalCfg ξ₀ + (sliceRep ξ₀ hξ₀ (x a) : Cfg) ∈ sliceSet ξ₀ := by
    show literalCfg ξ₀ + (sliceRep ξ₀ hξ₀ (x a) : Cfg) - literalCfg ξ₀ ∈ normalC ξ₀
    rw [add_sub_cancel_left]
    exact (sliceRep ξ₀ hξ₀ (x a)).2
  have hKyS : kAct H (literalCfg ξ₀ + (sliceRep ξ₀ hξ₀ (x a) : Cfg)) ∈ sliceSet ξ₀ := by
    show kAct H (literalCfg ξ₀ + (sliceRep ξ₀ hξ₀ (x a) : Cfg)) - literalCfg ξ₀ ∈ normalC ξ₀
    rw [map_add, hKP, add_sub_cancel_left]
    exact kAct_mem_normalC hξ₀ H (sliceRep ξ₀ hξ₀ (x a)).2
  exact (hinj _ ⟨hyW, hyS⟩ _ ⟨hKyW, hKyS⟩ _
    (mul_mem_autOf (inverse_mem_autOf hB) hg) h2).symm

/-- Zero-set step: `x a = g • (P + sliceRep (x a))` eventually, and `G` preserves the zero set
(`originalF_actC_eq_zero_iff`). -/
private theorem sliceB_eventually_originalF {α : Type*} {l : Filter α} {ξ₀ : Fin 4 → ℂ}
    (hξ₀ : IsUnitPhase ξ₀) (x : α → Cfg) (hx : Tendsto x l (𝓝 (literalCfg ξ₀)))
    (hF : ∀ a, Option2.NativeStress.AnalyticDerivative.originalF (x a) = 0) :
    ∀ᶠ a in l, Option2.NativeStress.AnalyticDerivative.originalF
      (literalCfg ξ₀ + ↑(sliceRep ξ₀ hξ₀ (x a))) = 0 := by
  filter_upwards [hx.eventually (eventually_eq_actC_sliceRep hξ₀)] with a ha
  obtain ⟨D, hD⟩ := ha
  have h := hF a
  rw [hD, originalF_actC_eq_zero_iff (groupChart_mem_autC D)] at h
  exact h

/-- The raw slice-family input tends to `P`. -/
private theorem sliceB_tendsto_preMap {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    Tendsto (fun p : SliceParam => preMap ξ₀ hξ₀ H (p.1, 0, p.2)) (𝓝 0) (𝓝 (literalCfg ξ₀)) := by
  have hc : Continuous (fun p : SliceParam => ((p.1, 0, p.2) : PreParam)) :=
    continuous_fst.prodMk (continuous_const.prodMk continuous_snd)
  have hι : Tendsto (fun p : SliceParam => ((p.1, 0, p.2) : PreParam)) (𝓝 0) (𝓝 0) := by
    have h := hc.tendsto 0
    simp only [Prod.fst_zero, Prod.snd_zero, Prod.mk_zero_zero] at h
    exact h
  have h := (analyticAt_preMap hξ₀ H).continuousAt.tendsto.comp hι
  rw [preMap_zero hξ₀ H] at h
  exact h

/-- Derivative of a germ in the zero set through `P` lies in the tangent space. -/
private theorem sliceB_der_mem_tangent {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ξ₀ : Fin 4 → ℂ} (γ : X → Cfg) (γ' : X →L[ℝ] Cfg) (hγ : HasFDerivAt γ γ' 0) (hγ0 : γ 0 = 0)
    (hF : ∀ᶠ x in 𝓝 (0 : X),
      Option2.NativeStress.AnalyticDerivative.originalF (literalCfg ξ₀ + γ x) = 0) (v : X) :
    γ' v ∈ tangentSpace ξ₀ := by
  have hO : HasFDerivAt Option2.NativeStress.AnalyticDerivative.originalF
      (fderiv ℝ Option2.NativeStress.AnalyticDerivative.originalF (literalCfg ξ₀))
      (literalCfg ξ₀ + γ 0) := by
    rw [hγ0, add_zero]
    exact (hasFDerivAt_originalF _).differentiableAt.hasFDerivAt
  have h1 := hO.comp (0 : X) (hγ.const_add (literalCfg ξ₀))
  have h2 : HasFDerivAt
      (Option2.NativeStress.AnalyticDerivative.originalF ∘ fun x => literalCfg ξ₀ + γ x)
      (0 : X →L[ℝ] (Fin 2184 → ℝ)) 0 :=
    (hasFDerivAt_const (0 : Fin 2184 → ℝ) (0 : X)).congr_of_eventuallyEq hF
  have h3 := h1.unique h2
  show γ' v ∈ LinearMap.ker
    (fderiv ℝ Option2.NativeStress.AnalyticDerivative.originalF (literalCfg ξ₀)).toLinearMap
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  have h4 := congrArg (fun L : X →L[ℝ] (Fin 2184 → ℝ) => L v) h3
  simpa using h4

/-- Derivative of a pointwise `kAct H`-fixed germ through `P` is `kAct H`-fixed. -/
private theorem sliceB_der_mem_fixed {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (γ : X → Cfg) (γ' : X →L[ℝ] Cfg)
    (hγ : HasFDerivAt γ γ' 0)
    (hK : ∀ᶠ x in 𝓝 (0 : X), kAct H (literalCfg ξ₀ + γ x) = literalCfg ξ₀ + γ x) (v : X) :
    γ' v ∈ fixedSpace (kAct H) := by
  let K : Cfg →L[ℝ] Cfg := LinearMap.toContinuousLinearMap (kAct H)
  have h1 : HasFDerivAt (fun x => K (γ x)) (K.comp γ') 0 := K.hasFDerivAt.comp 0 hγ
  have hev : (fun x => K (γ x)) =ᶠ[𝓝 0] γ := by
    filter_upwards [hK] with x hx
    have h : kAct H (literalCfg ξ₀) + kAct H (γ x) = literalCfg ξ₀ + γ x := by
      rw [← map_add]; exact hx
    rw [kAct_literalCfg hξ₀ H] at h
    exact add_left_cancel h
  have h2 : HasFDerivAt (fun x => K (γ x)) γ' 0 := hγ.congr_of_eventuallyEq hev
  have h3 := h1.unique h2
  rw [mem_fixedSpace]
  exact congrArg (fun L : X →L[ℝ] Cfg => L v) h3

private theorem sliceB_finrank_sliceParam : Module.finrank ℝ SliceParam = 10 := by
  simp [Module.finrank_prod]

theorem eventually_kAct_sliceFam {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    ∀ᶠ p in 𝓝 (0 : SliceParam),
      kAct H (literalCfg ξ₀ + ↑(sliceFam ξ₀ hξ₀ H p)) = literalCfg ξ₀ + ↑(sliceFam ξ₀ hξ₀ H p) :=
  sliceB_eventually_kAct hξ₀ H _ (sliceB_tendsto_preMap hξ₀ H) fun _ => kAct_preCfg ξ₀ H _ _ _

theorem eventually_kAct_sliceCommon {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    ∀ᶠ θ in 𝓝 (0 : Fin 4 → ℝ),
      kAct H (literalCfg ξ₀ + ↑(sliceCommon ξ₀ hξ₀ θ)) = literalCfg ξ₀ + ↑(sliceCommon ξ₀ hξ₀ θ) := by
  obtain ⟨ψ, hψ, hψ0, hincl⟩ := exists_slice_inclusion hξ₀ H
  have hψt : Tendsto ψ (𝓝 0) (𝓝 0) := by
    have h := hψ.continuousAt.tendsto
    rw [hψ0] at h
    exact h
  filter_upwards [hincl, hψt.eventually (eventually_kAct_sliceFam hξ₀ H)] with θ h1 h2
  rw [← h1]
  exact h2

theorem eventually_originalF_sliceFam {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    ∀ᶠ p in 𝓝 (0 : SliceParam),
      Option2.NativeStress.AnalyticDerivative.originalF (literalCfg ξ₀ + ↑(sliceFam ξ₀ hξ₀ H p)) = 0 :=
  sliceB_eventually_originalF hξ₀ _ (sliceB_tendsto_preMap hξ₀ H) fun p =>
    (originalF_actC_eq_zero_iff (groupChart_mem_autC 0) _).1
      (originalF_rawMap hξ₀ H (0, p.1, 0, p.2))

theorem eventually_originalF_sliceCommon {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    ∀ᶠ θ in 𝓝 (0 : Fin 4 → ℝ),
      Option2.NativeStress.AnalyticDerivative.originalF (literalCfg ξ₀ + ↑(sliceCommon ξ₀ hξ₀ θ)) = 0 := by
  obtain ⟨ψ, hψ, hψ0, hincl⟩ := exists_slice_inclusion hξ₀ 0
  have hψt : Tendsto ψ (𝓝 0) (𝓝 0) := by
    have h := hψ.continuousAt.tendsto
    rw [hψ0] at h
    exact h
  filter_upwards [hincl, hψt.eventually (eventually_originalF_sliceFam hξ₀ 0)] with θ h1 h2
  rw [← h1]
  exact h2

/-- Tangent identification: the slice family of `H` has tangent space exactly `Q^H`. -/
theorem range_sliceFamDer {ξ₀ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ₀) (H : Fin 4) :
    (LinearMap.range (sliceFamDer ξ₀ hξ.1 H : SliceParam →ₗ[ℝ] ↥(normalC ξ₀))).map
      (normalC ξ₀).subtype = fixQ ξ₀ H := by
  have hγ : HasFDerivAt (fun p => ((sliceFam ξ₀ hξ.1 H p : ↥(normalC ξ₀)) : Cfg))
      ((normalC ξ₀).subtypeL.comp (sliceFamDer ξ₀ hξ.1 H)) 0 :=
    (normalC ξ₀).subtypeL.hasFDerivAt.comp 0 (hasStrictFDerivAt_sliceFam hξ.1 H).hasFDerivAt
  have hγ0 : ((sliceFam ξ₀ hξ.1 H 0 : ↥(normalC ξ₀)) : Cfg) = 0 := by
    rw [sliceFam_zero hξ.1 H, Submodule.coe_zero]
  have hle : (LinearMap.range (sliceFamDer ξ₀ hξ.1 H : SliceParam →ₗ[ℝ] ↥(normalC ξ₀))).map
      (normalC ξ₀).subtype ≤ fixQ ξ₀ H := by
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, (sliceFamDer ξ₀ hξ.1 H v).2⟩, ?_⟩
    · exact sliceB_der_mem_tangent _ _ hγ hγ0 (eventually_originalF_sliceFam hξ.1 H) v
    · exact sliceB_der_mem_fixed hξ.1 H _ _ hγ (eventually_kAct_sliceFam hξ.1 H) v
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [finrank_fixQ hξ H, ← LinearMap.range_comp, LinearMap.finrank_range_of_inj,
    sliceB_finrank_sliceParam]
  exact fun a b h => sliceFamDer_injective hξ.1 H (Subtype.val_injective h)

/-- Tangent identification: the common slice germ has tangent space exactly `Q^K`. -/
theorem range_sliceCommonDer {ξ₀ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ₀) :
    (LinearMap.range (sliceCommonDer ξ₀ hξ.1 : (Fin 4 → ℝ) →ₗ[ℝ] ↥(normalC ξ₀))).map
      (normalC ξ₀).subtype = fixQK ξ₀ := by
  have hγ : HasFDerivAt (fun θ => ((sliceCommon ξ₀ hξ.1 θ : ↥(normalC ξ₀)) : Cfg))
      ((normalC ξ₀).subtypeL.comp (sliceCommonDer ξ₀ hξ.1)) 0 :=
    (normalC ξ₀).subtypeL.hasFDerivAt.comp 0 (hasStrictFDerivAt_sliceCommon hξ.1).hasFDerivAt
  have hγ0 : ((sliceCommon ξ₀ hξ.1 0 : ↥(normalC ξ₀)) : Cfg) = 0 := by
    rw [sliceCommon_zero hξ.1, Submodule.coe_zero]
  have hle : (LinearMap.range (sliceCommonDer ξ₀ hξ.1 : (Fin 4 → ℝ) →ₗ[ℝ] ↥(normalC ξ₀))).map
      (normalC ξ₀).subtype ≤ fixQK ξ₀ := by
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_,
      (sliceCommonDer ξ₀ hξ.1 v).2⟩, ?_⟩, ?_⟩
    · exact sliceB_der_mem_tangent _ _ hγ hγ0 (eventually_originalF_sliceCommon hξ.1) v
    · exact sliceB_der_mem_fixed hξ.1 0 _ _ hγ (eventually_kAct_sliceCommon hξ.1 0) v
    · exact sliceB_der_mem_fixed hξ.1 1 _ _ hγ (eventually_kAct_sliceCommon hξ.1 1) v
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [finrank_fixQK hξ, ← LinearMap.range_comp, LinearMap.finrank_range_of_inj,
    Module.finrank_fin_fun]
  exact fun a b h => sliceCommonDer_injective hξ.1 (Subtype.val_injective h)

end CKM.NativeFourFamily

#print axioms CKM.NativeFourFamily.eventually_kAct_sliceFam
#print axioms CKM.NativeFourFamily.eventually_kAct_sliceCommon
#print axioms CKM.NativeFourFamily.eventually_originalF_sliceFam
#print axioms CKM.NativeFourFamily.eventually_originalF_sliceCommon
#print axioms CKM.NativeFourFamily.range_sliceFamDer
#print axioms CKM.NativeFourFamily.range_sliceCommonDer

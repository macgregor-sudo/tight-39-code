module

public import GSOrbit

@[expose] public section

/-!
# The ambient analytic product chart `Θ_ξ(D, n) = χ(D) • (P + n)`

* `sliceChart ξ (D, n) = actC (groupChart D) (P + n)` on `derC × normalC ξ`, analytic everywhere.
* Its strict derivative at `(0, 0)` is the actual isomorphism `sliceDiff ξ hξ : (D, n) ↦ D(P) + n`
  (`orbitC ξ ⊕ normalC ξ = Cfg` and `orbitMapC` injective).
* `slicePH ξ hξ`: the open partial homeomorphism of the inverse function theorem
  (`HasStrictFDerivAt.toOpenPartialHomeomorph`), with source an open neighbourhood of `(0,0)`,
  target an open neighbourhood of `P`; its inverse is analytic at `P` and on a neighbourhood of `P`.
  Together with the analytic inverse chart of `exists_groupChart_local`, both local inverses exist
  and are analytic.
-/

noncomputable section

namespace CKM.NativeGroupSlice

open Glennie NativePolynomial CKM.NativeFirstOrder
open scoped Topology

/-- The ambient product chart `Θ_ξ(D, n) = χ(D) • (P + n)`. -/
def sliceChart (ξ : Fin 4 → ℂ) (p : derC × normalC ξ) : Cfg :=
  actC (groupChart p.1) (literalCfg ξ + p.2)

theorem sliceChart_zero_left (ξ : Fin 4 → ℂ) (n : normalC ξ) :
    sliceChart ξ (0, n) = literalCfg ξ + n := by
  show actC (groupChart 0) (literalCfg ξ + n) = literalCfg ξ + n
  rw [groupChart_zero, actC_one]
  rfl

theorem sliceChart_zero (ξ : Fin 4 → ℂ) : sliceChart ξ 0 = literalCfg ξ := by
  have h := sliceChart_zero_left ξ 0
  rw [Prod.mk_zero_zero] at h
  rw [h, Submodule.coe_zero, add_zero]

theorem analyticAt_sliceChart (ξ : Fin 4 → ℂ) (p : derC × normalC ξ) :
    AnalyticAt ℝ (sliceChart ξ) p := by
  have hg : AnalyticAt ℝ (fun q : derC × normalC ξ => groupChart q.1) p :=
    (analyticAt_groupChart p.1).comp analyticAt_fst
  have hn : AnalyticAt ℝ (fun q : derC × normalC ξ => literalCfg ξ + (q.2 : Cfg)) p :=
    analyticAt_const.add (((normalC ξ).subtypeL.analyticAt _).comp analyticAt_snd)
  have hb : AnalyticAt ℝ (fun x : CEnd × Cfg => actC x.1 x.2)
      (groupChart p.1, literalCfg ξ + (p.2 : Cfg)) :=
    actC.analyticAt_bilinear _
  exact AnalyticAt.comp (g := fun x : CEnd × Cfg => actC x.1 x.2)
    (f := fun q : derC × normalC ξ => (groupChart q.1, literalCfg ξ + (q.2 : Cfg)))
    hb (hg.prod hn)

/-- The differential `(D, n) ↦ D(P) + n`. -/
def sliceDiffLin (ξ : Fin 4 → ℂ) : (derC × normalC ξ) →L[ℝ] Cfg :=
  ((orbitMapC ξ).comp derC.subtypeL).coprod (normalC ξ).subtypeL

theorem sliceDiffLin_apply (ξ : Fin 4 → ℂ) (p : derC × normalC ξ) :
    sliceDiffLin ξ p = orbitMapC ξ p.1 + p.2 := by
  rfl

theorem sliceDiffLin_bijective (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Function.Bijective (sliceDiffLin ξ) := by
  have hc := isCompl_orbitC_normalC ξ hξ
  constructor
  · rw [injective_iff_map_eq_zero]
    intro p hp
    rw [sliceDiffLin_apply] at hp
    have h1 : orbitMapC ξ p.1 ∈ orbitC ξ := Submodule.mem_map_of_mem p.1.2
    have h2 : orbitMapC ξ p.1 ∈ normalC ξ := by
      rw [eq_neg_of_add_eq_zero_left hp]
      exact (normalC ξ).neg_mem p.2.2
    have h0 : orbitMapC ξ p.1 = 0 :=
      (Submodule.disjoint_def.1 hc.disjoint) _ h1 h2
    have hD : (p.1 : CEnd) = 0 := orbitMapC_injective ξ hξ (by rw [h0, map_zero])
    have hN : (p.2 : Cfg) = 0 := by rw [h0, zero_add] at hp; exact hp
    exact Prod.ext (Subtype.ext hD) (Subtype.ext hN)
  · intro x
    have hx : x ∈ orbitC ξ ⊔ normalC ξ := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨D, hD, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨(⟨D, hD⟩, ⟨z, hz⟩), rfl⟩

/-- Generic chain rule for `p ↦ B (g p.1) (P + ι p.2)` at `0`, stated over abstract normed spaces so
that no product-of-submodule instance unification happens (the `ophOf` trick of COMMON.md). -/
private theorem slice_hasStrictFDerivAt_generic {E₁ E₂ A V : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : A →L[ℝ] V →L[ℝ] V) (g : E₁ → A) (g' : E₁ →L[ℝ] A) (hg : HasStrictFDerivAt g g' 0)
    (P : V) (ι : E₂ →L[ℝ] V) (h1 : B (g 0) = ContinuousLinearMap.id ℝ V)
    (e : E₁ × E₂ →L[ℝ] V) (he : ∀ p, e p = B (g' p.1) P + ι p.2) :
    HasStrictFDerivAt (fun p : E₁ × E₂ => B (g p.1) (P + ι p.2)) e 0 := by
  have hg2 : HasStrictFDerivAt (fun p : E₁ × E₂ => g p.1)
      (g'.comp (ContinuousLinearMap.fst ℝ E₁ E₂)) 0 :=
    hg.comp (0 : E₁ × E₂) hasStrictFDerivAt_fst
  have hn : HasStrictFDerivAt (fun p : E₁ × E₂ => P + ι p.2)
      (ι.comp (ContinuousLinearMap.snd ℝ E₁ E₂)) 0 :=
    (ι.hasStrictFDerivAt.comp (0 : E₁ × E₂) hasStrictFDerivAt_snd).const_add P
  refine (B.hasStrictFDerivAt_of_bilinear hg2 hn).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun p => ?_
  rw [he]
  simp only [add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', Prod.fst_zero, Prod.snd_zero, h1, map_zero, add_zero]
  rw [add_comm]
  rfl

/-- The differential as a linear isomorphism. -/
def sliceDiffLE (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : (derC × normalC ξ) ≃ₗ[ℝ] Cfg :=
  LinearEquiv.ofBijective (sliceDiffLin ξ).toLinearMap (sliceDiffLin_bijective ξ hξ)

/-- The differential as an isomorphism. -/
def sliceDiff (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : (derC × normalC ξ) ≃L[ℝ] Cfg where
  toLinearEquiv := sliceDiffLE ξ hξ
  continuous_toFun := (sliceDiffLin ξ).continuous
  continuous_invFun := by
    have h := LinearMap.continuous_of_finiteDimensional (E := Cfg) (F' := derC × normalC ξ)
      (sliceDiffLE ξ hξ).symm.toLinearMap
    exact h

theorem sliceDiff_apply (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (p : derC × normalC ξ) :
    sliceDiff ξ hξ p = orbitMapC ξ p.1 + p.2 := by
  show sliceDiffLE ξ hξ p = _
  rw [sliceDiffLE, LinearEquiv.ofBijective_apply]
  exact sliceDiffLin_apply ξ p

theorem hasStrictFDerivAt_sliceChart (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    HasStrictFDerivAt (sliceChart ξ) (sliceDiff ξ hξ : (derC × normalC ξ) →L[ℝ] Cfg) 0 := by
  exact slice_hasStrictFDerivAt_generic actC groupChart derC.subtypeL hasStrictFDerivAt_groupChart
    (literalCfg ξ) (normalC ξ).subtypeL (by rw [groupChart_zero, actC_one]) _
    (fun p => by exact sliceDiff_apply ξ hξ p)

/-- The inverse-function-theorem partial homeomorphism of a map with invertible strict derivative. -/
def ophOf {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (e : E ≃L[ℝ] F) (a : E)
    (hf : HasStrictFDerivAt f (e : E →L[ℝ] F) a) : OpenPartialHomeomorph E F :=
  hf.toOpenPartialHomeomorph f

/-- The local product chart (inverse function theorem). -/
def slicePH (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : OpenPartialHomeomorph (derC × normalC ξ) Cfg :=
  ophOf (sliceChart ξ) (sliceDiff ξ hξ) 0 (hasStrictFDerivAt_sliceChart ξ hξ)

theorem slicePH_coe (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : ⇑(slicePH ξ hξ) = sliceChart ξ := rfl

theorem zero_mem_slicePH_source (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (0 : derC × normalC ξ) ∈ (slicePH ξ hξ).source := by
  exact (hasStrictFDerivAt_sliceChart ξ hξ).mem_toOpenPartialHomeomorph_source

theorem literalCfg_mem_slicePH_target (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    literalCfg ξ ∈ (slicePH ξ hξ).target := by
  have h : sliceChart ξ 0 ∈ (slicePH ξ hξ).target :=
    (hasStrictFDerivAt_sliceChart ξ hξ).image_mem_toOpenPartialHomeomorph_target
  rw [sliceChart_zero] at h
  exact h

theorem slicePH_symm_literalCfg (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (slicePH ξ hξ).symm (literalCfg ξ) = 0 := by
  have h := (slicePH ξ hξ).left_inv (zero_mem_slicePH_source ξ hξ)
  rw [slicePH_coe, sliceChart_zero] at h
  exact h

theorem analyticAt_slicePH_symm (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    AnalyticAt ℝ (slicePH ξ hξ).symm (literalCfg ξ) := by
  have h : AnalyticAt ℝ (slicePH ξ hξ).symm (sliceChart ξ 0) :=
    analyticAt_toOpenPartialHomeomorph_symm (hasStrictFDerivAt_sliceChart ξ hξ)
      (analyticAt_sliceChart ξ 0)
  rw [sliceChart_zero] at h
  exact h

theorem exists_analyticOnNhd_slicePH_symm (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    ∃ W ∈ 𝓝 (literalCfg ξ), W ⊆ (slicePH ξ hξ).target ∧ AnalyticOnNhd ℝ (slicePH ξ hξ).symm W := by
  exact ⟨(slicePH ξ hξ).target ∩ {y | AnalyticAt ℝ (slicePH ξ hξ).symm y},
    Filter.inter_mem ((slicePH ξ hξ).open_target.mem_nhds (literalCfg_mem_slicePH_target ξ hξ))
      (analyticAt_slicePH_symm ξ hξ).eventually_analyticAt,
    Set.inter_subset_left, fun _ hy => hy.2⟩

end CKM.NativeGroupSlice

#print axioms CKM.NativeGroupSlice.sliceChart_zero_left
#print axioms CKM.NativeGroupSlice.sliceChart_zero
#print axioms CKM.NativeGroupSlice.analyticAt_sliceChart
#print axioms CKM.NativeGroupSlice.sliceDiffLin_apply
#print axioms CKM.NativeGroupSlice.sliceDiffLin_bijective
#print axioms CKM.NativeGroupSlice.sliceDiff
#print axioms CKM.NativeGroupSlice.sliceDiff_apply
#print axioms CKM.NativeGroupSlice.hasStrictFDerivAt_sliceChart
#print axioms CKM.NativeGroupSlice.slicePH
#print axioms CKM.NativeGroupSlice.zero_mem_slicePH_source
#print axioms CKM.NativeGroupSlice.literalCfg_mem_slicePH_target
#print axioms CKM.NativeGroupSlice.slicePH_symm_literalCfg
#print axioms CKM.NativeGroupSlice.analyticAt_slicePH_symm
#print axioms CKM.NativeGroupSlice.exists_analyticOnNhd_slicePH_symm

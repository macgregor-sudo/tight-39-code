module
public import NativeNormalizedA2AnalyticEndpoint
public import Mathlib.Geometry.Manifold.Immersion
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section

/-!
# Strong analytic immersions of the actual normalized native configurations

The existing full39 and original packed1053 maps and named
quotient/phase atlas are unchanged. An analytic inverse-function chart gives the
actual local inclusion normal form. The complement is the fixed real1043 space,
not a caller hypothesis or a point-dependent choice. No exhaustion is asserted here.
First-party proof using imported owners and pinned mathlib interfaces; no upstream
proof body copied. Thanks to the contributors. “If I have seen further it is by
standing on the sholders of Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/
noncomputable section
open scoped Manifold ContDiff Matrix.Norms.Elementwise Topology
open Set Filter Manifold
open UnitaryErrorBases UnitaryErrorBases.ThreeCycleNormalized
open UnitaryErrorBases.SpecialUnitaryConstraints NativePolynomial.PartialAction

namespace CompactAlbert

private theorem analytic_normal_form
    {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
    (g : E → W) (hg : ContDiffAt ℝ ω g 0)
    (hinj : Function.Injective (fderiv ℝ g 0)) :
    ∃ (e : (E × (Fin (Module.finrank ℝ W - Module.finrank ℝ E) → ℝ)) ≃L[ℝ] W)
      (ψ : OpenPartialHomeomorph W W) (U : Set E),
      IsOpen U ∧ 0 ∈ U ∧ g 0 ∈ ψ.source ∧
      ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, W) ω W ∧
      ∀ v ∈ U, ψ (g v) = e (v, 0) := by
  let A := fderiv ℝ g 0
  have hA : A.HasLeftInverse :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hinj
  let L := hA.leftInverse
  let e₀ : (E × L.ker) ≃L[ℝ] W :=
    (ContinuousLinearEquiv.equivOfRightInverse L A hA.leftInverse_leftInverse).symm
  have hd : Module.finrank ℝ L.ker = Module.finrank ℝ W - Module.finrank ℝ E := by
    have h := e₀.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at h
    omega
  let c : L.ker ≃L[ℝ] (Fin (Module.finrank ℝ W - Module.finrank ℝ E) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simpa using hd)
  let e := ((ContinuousLinearEquiv.refl ℝ E).prodCongr c.symm).trans e₀
  have hev (v : E) : e (v, 0) = A v := by
    simp [e, e₀]
  let G := fun z : E × (Fin (Module.finrank ℝ W - Module.finrank ℝ E) → ℝ) =>
    g z.1 + e (0, z.2)
  have hG : ContDiffAt ℝ ω G 0 := by
    exact (hg.comp 0 contDiffAt_fst).add
      (e.contDiff.contDiffAt.comp 0 (contDiffAt_const.prodMk contDiffAt_snd))
  have hG' : HasFDerivAt G (e : _ →L[ℝ] W) 0 := by
    let C := Fin (Module.finrank ℝ W - Module.finrank ℝ E) → ℝ
    have hp : HasFDerivAt (fun z : E × C => (0, z.2))
        ((0 : E × C →L[ℝ] E).prod (ContinuousLinearMap.snd ℝ E C)) 0 :=
      (hasFDerivAt_const (0 : E) (0 : E × C)).prodMk hasFDerivAt_snd
    have hs : HasFDerivAt (fun z : E × C => e (0, z.2))
        ((e : E × C →L[ℝ] W).comp
          ((0 : E × C →L[ℝ] E).prod (ContinuousLinearMap.snd ℝ E C))) 0 :=
      e.hasFDerivAt.comp (0 : E × C) hp
    have hf : HasFDerivAt (fun z : E × C => g z.1)
        (A.comp (ContinuousLinearMap.fst ℝ E C)) 0 :=
      (hg.differentiableAt (by simp)).hasFDerivAt.comp (0 : E × C) hasFDerivAt_fst
    have h := hf.add hs
    convert h using 1
    apply ContinuousLinearMap.ext
    intro z
    change e z = A z.1 + e (0, z.2)
    rw [← hev, ← map_add]
    simp
  let H := G ∘ e.symm
  have hH : ContDiffAt ℝ ω H 0 := by
    have hh : ContDiffAt ℝ ω G (e.symm 0) := by simpa only [map_zero] using hG
    exact hh.comp 0 e.symm.contDiff.contDiffAt
  have hH' : HasFDerivAt H (ContinuousLinearEquiv.refl ℝ W : W →L[ℝ] W) 0 := by
    have hh : HasFDerivAt G (e : _ →L[ℝ] W) (e.symm 0) := by
      simpa only [map_zero] using hG'
    simpa using hh.comp 0 e.symm.hasFDerivAt
  let φ := hH.toOpenPartialHomeomorph H hH' (by simp)
  have hφ : (φ : W → W) = H := rfl
  have h0 : 0 ∈ φ.source := hH.mem_toOpenPartialHomeomorph_source hH' (by simp)
  have hinv : ContDiffAt ℝ ω φ.symm (H 0) :=
    hH.to_localInverse hH' (by simp)
  have hevent : ∀ᶠ y in 𝓝 (0 : W),
      ContDiffAt ℝ ω H y ∧ ContDiffAt ℝ ω φ.symm (H y) :=
    (hH.eventually (by simp)).and
      (hH.continuousAt.tendsto.eventually (hinv.eventually (by simp)))
  obtain ⟨R, hR, hRo, hR0⟩ := eventually_nhds_iff.mp hevent
  let θ := φ.restr R
  have hθ0 : 0 ∈ θ.source := by
    rw [show θ.source = φ.source ∩ R from φ.restr_source' R hRo]
    exact ⟨h0, hR0⟩
  have hθ : (θ : W → W) = H := rfl
  have hθinv : (θ.symm : W → W) = φ.symm := rfl
  have hθsmooth : ContDiffOn ℝ ω θ θ.source := by
    intro y hy
    have hyR : y ∈ R := by
      rw [show θ.source = φ.source ∩ R from φ.restr_source' R hRo] at hy
      exact hy.2
    exact (hR y hyR).1.contDiffWithinAt
  have hθinvsmooth : ContDiffOn ℝ ω θ.symm θ.target := by
    intro y hy
    have hyR : θ.symm y ∈ R := by
      have h := θ.map_target hy
      rw [show θ.source = φ.source ∩ R from φ.restr_source' R hRo] at h
      exact h.2
    have hr : H (θ.symm y) = y := θ.right_inv hy
    have ht : ContDiffAt ℝ ω φ.symm y := hr ▸ (hR (θ.symm y) hyR).2
    exact ht.contDiffWithinAt
  let U := (fun v : E => e (v, 0)) ⁻¹' θ.source
  refine ⟨e, θ.symm, U, θ.open_source.preimage (by fun_prop), ?_, ?_, ?_, ?_⟩
  · change e (0 : E × (Fin (Module.finrank ℝ W - Module.finrank ℝ E) → ℝ)) ∈ θ.source
    simpa only [map_zero] using hθ0
  · have hv : H 0 = g 0 := by simp [H, G]
    change g 0 ∈ θ.target
    simpa only [hθ, hv] using θ.map_source hθ0
  · exact θ.symm.mem_maximalAtlas_of_contMDiffOn
      hθinvsmooth.contMDiffOn hθsmooth.contMDiffOn
  · intro v hv
    have h := θ.left_inv hv
    have he0 : e (0, 0) = 0 := e.map_zero
    simpa [hθ, H, G, he0] using h

attribute [local instance] descendedNormalizedParameterChartedSpace

private theorem actual_parameter_isImmersionOfComplement
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (f : DescendedNormalizedParameter → W)
    (hf : ContMDiff 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, W) ω f)
    (hd : ∀ p, IsDiffImmersionAt 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, W) f p) :
    IsImmersionOfComplement
      (Fin (Module.finrank ℝ W - Module.finrank ℝ NativeGraphParameters) → ℝ)
      𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, W) ω f := by
  let := descendedNormalizedParameter_isManifold
  intro p
  let c := @chartAt NativeGraphParameters
    (inferInstance : NormedAddCommGroup NativeGraphParameters).toUniformSpace.toTopologicalSpace
    DescendedNormalizedParameter _
    descendedNormalizedParameterChartedSpace p
  let g := fun x => f (c.symm x)
  have hg : ContDiffAt ℝ ω g 0 := by
    have h := (contMDiffAt_iff.mp (hf p)).2
    simpa only [g, c, mfld_simps, descendedNormalizedParameter_chartAt_self,
      chartAt_self_eq, Function.comp_def, OpenPartialHomeomorph.refl_apply,
      contDiffWithinAt_univ] using! h
  have hgi : Function.Injective (fderiv ℝ g 0) := by
    have h := (hd p).mfderiv_injective
    rw [mfderiv, ite_eq_left ((hf p).mdifferentiableAt (by simp))] at h
    have hh : Function.Injective
        ((tangentSpaceCastModel 𝓘(ℝ, W) (f p)).symm.toContinuousLinearMap.comp
          ((fderiv ℝ g 0).comp
            (tangentSpaceCastModel 𝓘(ℝ, NativeGraphParameters) p).toContinuousLinearMap)) := by
      simpa only [g, c, writtenInExtChartAt, mfld_simps,
        descendedNormalizedParameter_chartAt_self, chartAt_self_eq, Function.comp_def,
        OpenPartialHomeomorph.refl_apply, fderivWithin_univ] using! h
    intro a b hab
    apply (tangentSpaceCastModel 𝓘(ℝ, NativeGraphParameters) p).symm.injective
    apply hh
    change (tangentSpaceCastModel 𝓘(ℝ, W) (f p)).symm
      ((fderiv ℝ g 0) ((tangentSpaceCastModel 𝓘(ℝ, NativeGraphParameters) p)
        ((tangentSpaceCastModel 𝓘(ℝ, NativeGraphParameters) p).symm a))) =
      (tangentSpaceCastModel 𝓘(ℝ, W) (f p)).symm
      ((fderiv ℝ g 0) ((tangentSpaceCastModel 𝓘(ℝ, NativeGraphParameters) p)
        ((tangentSpaceCastModel 𝓘(ℝ, NativeGraphParameters) p).symm b)))
    simp only [ContinuousLinearEquiv.apply_symm_apply, hab]
  obtain ⟨e, ψ, U, hUo, hU0, hψ0, hψatlas, hnormal⟩ := analytic_normal_form g hg hgi
  let s := c.source ∩ c ⁻¹' U
  have hso : IsOpen s := c.isOpen_inter_preimage hUo
  let φ := c.restr s
  have hp : p ∈ c.source := @mem_chart_source NativeGraphParameters DescendedNormalizedParameter _ _
    descendedNormalizedParameterChartedSpace p
  have hcp : c p = 0 := descendedNormalizedParameter_chartAt_self p
  have hφp : p ∈ φ.source := by
    rw [show φ.source = c.source ∩ s from c.restr_source' s hso]
    refine ⟨hp, hp, ?_⟩
    change c p ∈ U
    simpa only [hcp] using hU0
  have hg0 : g 0 = f p := by
    have h := c.left_inv hp
    rw [hcp] at h
    exact congrArg f h
  refine IsImmersionAtOfComplement.mk_of_continuousAt (I := 𝓘(ℝ, NativeGraphParameters)) (J := 𝓘(ℝ, W))
    hf.continuous.continuousAt
    e φ ψ hφp (hg0 ▸ hψ0) ?_ hψatlas ?_
  · exact restr_mem_maximalAtlas (contDiffGroupoid ω 𝓘(ℝ, NativeGraphParameters))
      (IsManifold.chart_mem_maximalAtlas p) hso
  · intro v hv
    have hv' : v ∈ φ.target := by simpa only [mfld_simps] using hv
    have hs := φ.map_target hv'
    rw [show φ.source = c.source ∩ s from c.restr_source' s hso] at hs
    have heq : c (φ.symm v) = v := φ.right_inv hv'
    have hvU : v ∈ U := heq ▸ hs.2.2
    simpa only [mfld_simps, Function.comp_def, OpenPartialHomeomorph.restr_symm_apply,
      g, φ] using hnormal v hvU

/-- The actual full configuration has a single real1043 complement at all parameter points. -/
theorem isImmersionOfComplement_nativeNormalizedDescendedConfiguration :
    IsImmersionOfComplement (Fin 1043 → ℝ)
      𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Configuration ℝ) ω
      nativeNormalizedDescendedConfiguration := by
  have hn : Module.finrank ℝ (Configuration ℝ) - Module.finrank ℝ NativeGraphParameters = 1043 := by
    rw [finrank_nativeGraphParameters]
    change Module.finrank ℝ (Fin 39 → Fin 27 → ℝ) - 10 = 1043
    rw [Module.finrank_pi_fintype]
    norm_num
  rw [← hn]
  exact
    actual_parameter_isImmersionOfComplement nativeNormalizedDescendedConfiguration
      nativeNormalizedDescendedConfiguration_analytic_endpoint.2.2.1.2.1
      nativeNormalizedDescendedConfiguration_analytic_endpoint.2.2.1.2.2

/-- The unchanged point-first packed configuration has the same fixed complement. -/
theorem isImmersionOfComplement_nativeNormalizedDescendedPackedConfiguration :
    IsImmersionOfComplement (Fin 1043 → ℝ)
      𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Fin 1053 → ℝ) ω
      nativeNormalizedDescendedPackedConfiguration := by
  have hn : Module.finrank ℝ (Fin 1053 → ℝ) - Module.finrank ℝ NativeGraphParameters = 1043 := by
    rw [finrank_nativeGraphParameters]
    simp
  rw [← hn]
  exact
    actual_parameter_isImmersionOfComplement nativeNormalizedDescendedPackedConfiguration
      nativeNormalizedDescendedConfiguration_analytic_endpoint.2.2.2.1.2.1
      nativeNormalizedDescendedConfiguration_analytic_endpoint.2.2.2.1.2.2

/-- Strong analytic immersion of the exact full native39-point coordinate configuration. -/
theorem isImmersion_nativeNormalizedDescendedConfiguration :
    IsImmersion 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Configuration ℝ) ω
      nativeNormalizedDescendedConfiguration :=
  isImmersionOfComplement_nativeNormalizedDescendedConfiguration.isImmersion

/-- Strong analytic immersion of the exact original point-first packed1053 coordinates. -/
theorem isImmersion_nativeNormalizedDescendedPackedConfiguration :
    IsImmersion 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Fin 1053 → ℝ) ω
      nativeNormalizedDescendedPackedConfiguration :=
  isImmersionOfComplement_nativeNormalizedDescendedPackedConfiguration.isImmersion

/-- The strong analytic normal-form predicate at each actual quotient/phase parameter. -/
theorem isImmersionAt_nativeNormalizedDescendedConfiguration (p : DescendedNormalizedParameter) :
    IsImmersionAt 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Configuration ℝ) ω
      nativeNormalizedDescendedConfiguration p :=
  isImmersion_nativeNormalizedDescendedConfiguration.isImmersionAt p

/-- Pointwise strong analytic immersion in the original1053 polynomial variables. -/
theorem isImmersionAt_nativeNormalizedDescendedPackedConfiguration
    (p : DescendedNormalizedParameter) :
    IsImmersionAt 𝓘(ℝ, NativeGraphParameters) 𝓘(ℝ, Fin 1053 → ℝ) ω
      nativeNormalizedDescendedPackedConfiguration p :=
  isImmersion_nativeNormalizedDescendedPackedConfiguration.isImmersionAt p

end CompactAlbert

module

public import NativeSliceNormalSplitting
public import GSResidual
public import OriginalResidualSmoothnessV2
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

@[expose] public section

/-!
Local nonlinear elimination on the actual native normal slice. The derivative
kernel and range come from the actual 2184 original rows. This constructs a
local C² chart and retains the full original residual as the reduced map.
It neither identifies the A5 sheets in these coordinates nor proves exhaustion.
-/
set_option Elab.async false
noncomputable section

namespace CKM.NativeSliceImplicitReduction

open NativeFirstOrder NativeGroupSlice NativeFourFamily NativeSliceNormalSplitting
open Option2.NativeStress.AnalyticDerivative
open scoped Topology

abbrev Residual := Fin 2184 → ℝ
abbrev Coordinates (ξ : Fin 4 → ℂ) := normalKernel ξ × normalRange ξ

/-- The actual derivative with exactly its own range as codomain. -/
def rangeDerivative (ξ : Fin 4 → ℂ) : normalC ξ →L[ℝ] normalRange ξ :=
  (normalDerivative ξ).codRestrict (normalRange ξ) (fun n => ⟨n, rfl⟩)

@[simp] theorem coe_rangeDerivative (ξ : Fin 4 → ℂ) (n : normalC ξ) :
    (rangeDerivative ξ n : Residual) = normalDerivative ξ n := rfl

@[simp] theorem rangeDerivative_rightInverse (ξ : Fin 4 → ℂ) (y : normalRange ξ) :
    rangeDerivative ξ (normalRightInverse ξ y) = y :=
  Subtype.ext (normalDerivative_rightInverse ξ y)

@[simp] theorem rangeDerivative_kernel (ξ : Fin 4 → ℂ) (k : normalKernel ξ) :
    rangeDerivative ξ (k : normalC ξ) = 0 := Subtype.ext k.property

/-- Kernel projection along the previously constructed derivative complement. -/
def kernelProjection (ξ : Fin 4 → ℂ) : normalC ξ →L[ℝ] normalKernel ξ :=
  ((ContinuousLinearMap.id ℝ (normalC ξ)) -
    (normalRightInverse ξ).comp (rangeDerivative ξ)).codRestrict (normalKernel ξ)
      (fun n => by
        change normalDerivative ξ (n - normalRightInverse ξ (rangeDerivative ξ n)) = 0
        rw [map_sub, normalDerivative_rightInverse, coe_rangeDerivative, sub_self])

@[simp] theorem kernelProjection_coe (ξ : Fin 4 → ℂ) (n : normalC ξ) :
    (kernelProjection ξ n : normalC ξ) = n - normalRightInverse ξ (rangeDerivative ξ n) := rfl

@[simp] theorem kernelProjection_kernel (ξ : Fin 4 → ℂ) (k : normalKernel ξ) :
    kernelProjection ξ (k : normalC ξ) = k := by
  apply Subtype.ext
  simp only [kernelProjection_coe, rangeDerivative_kernel, map_zero, sub_zero]

@[simp] theorem kernelProjection_rightInverse (ξ : Fin 4 → ℂ) (y : normalRange ξ) :
    kernelProjection ξ (normalRightInverse ξ y) = 0 := by
  apply Subtype.ext
  simp only [kernelProjection_coe, rangeDerivative_rightInverse, sub_self, Submodule.coe_zero]

/-- The exact linear coordinates `(kernel part, actual derivative)`. -/
def chartDerivativeLinearEquiv (ξ : Fin 4 → ℂ) : normalC ξ ≃ₗ[ℝ] Coordinates ξ where
  toFun n := (kernelProjection ξ n, rangeDerivative ξ n)
  invFun p := (p.1 : normalC ξ) + normalRightInverse ξ p.2
  left_inv n := sub_add_cancel _ _
  right_inv p := by
    apply Prod.ext
    · simp only [map_add, kernelProjection_kernel, kernelProjection_rightInverse, add_zero]
    · simp only [map_add, rangeDerivative_kernel, rangeDerivative_rightInverse, zero_add]
  map_add' n m := by simp only [map_add, Prod.mk_add_mk]
  map_smul' c n := by simp only [map_smul, Prod.smul_mk, RingHom.id_apply]

def chartDerivative (ξ : Fin 4 → ℂ) : normalC ξ ≃L[ℝ] Coordinates ξ :=
  LinearEquiv.toContinuousLinearEquiv (𝕜 := ℝ)
    (E := ↥(normalC ξ)) (F := Coordinates ξ) (chartDerivativeLinearEquiv ξ)

@[simp] theorem chartDerivative_apply (ξ : Fin 4 → ℂ) (n : normalC ξ) :
    chartDerivative ξ n = (kernelProjection ξ n, rangeDerivative ξ n) := rfl

@[simp] theorem chartDerivative_symm_apply (ξ : Fin 4 → ℂ) (p : Coordinates ξ) :
    (chartDerivative ξ).symm p = (p.1 : normalC ξ) + normalRightInverse ξ p.2 := rfl

/-- A chosen complement to the actual range in the original residual space. -/
def residualComplement (ξ : Fin 4 → ℂ) : Submodule ℝ Residual :=
  Classical.choose (Submodule.exists_isCompl (normalRange ξ))

theorem residualComplement_isCompl (ξ : Fin 4 → ℂ) :
    IsCompl (normalRange ξ) (residualComplement ξ) :=
  Classical.choose_spec (Submodule.exists_isCompl (normalRange ξ))

/-- A continuous linear projection which is the identity on the actual range. -/
def rangeProjection (ξ : Fin 4 → ℂ) : Residual →L[ℝ] normalRange ξ :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Residual) (F' := ↥(normalRange ξ))
    ((normalRange ξ).projectionOnto (residualComplement ξ) (residualComplement_isCompl ξ))

@[simp] theorem rangeProjection_range (ξ : Fin 4 → ℂ) (y : normalRange ξ) :
    rangeProjection ξ (y : Residual) = y :=
  Submodule.projectionOnto_apply_left (residualComplement_isCompl ξ) y

@[simp] theorem rangeProjection_normalDerivative (ξ : Fin 4 → ℂ) (n : normalC ξ) :
    rangeProjection ξ (normalDerivative ξ n) = rangeDerivative ξ n :=
  rangeProjection_range ξ (rangeDerivative ξ n)

/-- All original residuals of the actual translated normal vector. -/
def normalResidual (ξ : Fin 4 → ℂ) (n : normalC ξ) : Residual :=
  originalF (literalCfg ξ + (n : Cfg))

theorem normalResidual_contDiff (ξ : Fin 4 → ℂ) (r : WithTop ℕ∞) :
    ContDiff ℝ r (normalResidual ξ) :=
  (originalF_contDiff r).comp (contDiff_const.add (normalC ξ).subtypeL.contDiff)

theorem normalResidual_hasFDerivAt (ξ : Fin 4 → ℂ) :
    HasFDerivAt (normalResidual ξ) (normalDerivative ξ) 0 := by
  have h := (originalF_differentiable (literalCfg ξ)).hasFDerivAt
  have hι := ((normalC ξ).subtypeL.hasFDerivAt (x := (0 : normalC ξ))).const_add
    (literalCfg ξ)
  have h' : HasFDerivAt originalF (fderiv ℝ originalF (literalCfg ξ))
      (literalCfg ξ + (normalC ξ).subtypeL 0) := by simpa using h
  exact h'.comp 0 hι

/-- The nonlinear map used by the inverse function theorem. -/
def chartMap (ξ : Fin 4 → ℂ) (n : normalC ξ) : Coordinates ξ :=
  (kernelProjection ξ n, rangeProjection ξ (normalResidual ξ n))

theorem chartMap_contDiff (ξ : Fin 4 → ℂ) : ContDiff ℝ 2 (chartMap ξ) := by
  have hk : ContDiff ℝ 2 (kernelProjection ξ) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := ↥(normalC ξ))
      (F := ↥(normalKernel ξ)) (kernelProjection ξ)
  have hr : ContDiff ℝ 2 (fun n : normalC ξ => rangeProjection ξ (normalResidual ξ n)) :=
    (rangeProjection ξ).contDiff.comp (normalResidual_contDiff ξ 2)
  exact hk.prodMk hr

theorem chartMap_hasFDerivAt (ξ : Fin 4 → ℂ) :
    HasFDerivAt (chartMap ξ) (chartDerivative ξ : normalC ξ →L[ℝ] Coordinates ξ) 0 := by
  have hk : HasFDerivAt (kernelProjection ξ) (kernelProjection ξ) 0 :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := ↥(normalC ξ))
      (F := ↥(normalKernel ξ)) (kernelProjection ξ)
  have hp : HasFDerivAt (rangeProjection ξ) (rangeProjection ξ) (normalResidual ξ 0) :=
    (rangeProjection ξ).hasFDerivAt
  have hprod := HasFDerivAt.prodMk (𝕜 := ℝ) (E := ↥(normalC ξ))
    (F := ↥(normalKernel ξ)) (G := ↥(normalRange ξ)) hk
    (hp.comp 0 (normalResidual_hasFDerivAt ξ))
  apply hprod.congr_fderiv
  apply ContinuousLinearMap.ext
  intro n
  change (kernelProjection ξ n, rangeProjection ξ (normalDerivative ξ n)) =
    (kernelProjection ξ n, rangeDerivative ξ n)
  rw [rangeProjection_normalDerivative]

/-- Actual local inverse from the pinned C² inverse-function theorem. -/
def normalPH (ξ : Fin 4 → ℂ) : OpenPartialHomeomorph (normalC ξ) (Coordinates ξ) :=
  (chartMap_contDiff ξ).contDiffAt.toOpenPartialHomeomorph (chartMap ξ)
    (chartMap_hasFDerivAt ξ) (by norm_num)

theorem normalPH_coe (ξ : Fin 4 → ℂ) : ⇑(normalPH ξ) = chartMap ξ := rfl

theorem zero_mem_normalPH_source (ξ : Fin 4 → ℂ) :
    (0 : normalC ξ) ∈ (normalPH ξ).source :=
  (chartMap_contDiff ξ).contDiffAt.mem_toOpenPartialHomeomorph_source
    (chartMap_hasFDerivAt ξ) (by norm_num)

theorem chartMap_zero {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) : chartMap ξ 0 = 0 := by
  simp only [chartMap, normalResidual, Submodule.coe_zero, add_zero,
    originalF_literalCfg ξ hξ.1, map_zero, Prod.mk_zero_zero]

theorem zero_mem_normalPH_target {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    (0 : Coordinates ξ) ∈ (normalPH ξ).target := by
  have h := (normalPH ξ).map_source (zero_mem_normalPH_source ξ)
  simpa only [normalPH_coe, chartMap_zero hξ] using h

theorem normalPH_symm_zero {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    (normalPH ξ).symm 0 = 0 := by
  have h := (normalPH ξ).left_inv (zero_mem_normalPH_source ξ)
  simpa only [normalPH_coe, chartMap_zero hξ] using h

theorem normalPH_symm_contDiffAt {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    ContDiffAt ℝ 2 (normalPH ξ).symm 0 := by
  apply OpenPartialHomeomorph.contDiffAt_symm (𝕜 := ℝ)
    (E := ↥(normalC ξ)) (F := Coordinates ξ) (normalPH ξ)
    (zero_mem_normalPH_target hξ) (f₀' := chartDerivative ξ)
  · simpa only [normalPH_coe, normalPH_symm_zero hξ] using chartMap_hasFDerivAt ξ
  · simpa only [normalPH_coe, normalPH_symm_zero hξ] using (chartMap_contDiff ξ).contDiffAt

theorem normalPH_symm_hasFDerivAt {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    HasFDerivAt (normalPH ξ).symm
      ((chartDerivative ξ).symm : Coordinates ξ →L[ℝ] normalC ξ) 0 := by
  apply OpenPartialHomeomorph.hasFDerivAt_symm (𝕜 := ℝ)
    (E := ↥(normalC ξ)) (F := Coordinates ξ) (normalPH ξ)
    (zero_mem_normalPH_target hξ) (f' := chartDerivative ξ)
  simpa only [normalPH_coe, normalPH_symm_zero hξ] using chartMap_hasFDerivAt ξ

theorem exists_normalPH_symm_C2_neighborhood {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    ∃ W ∈ 𝓝 (0 : Coordinates ξ), W ⊆ (normalPH ξ).target ∧
      ∀ p ∈ W, ContDiffAt ℝ 2 (normalPH ξ).symm p := by
  refine ⟨(normalPH ξ).target ∩ {p | ContDiffAt ℝ 2 (normalPH ξ).symm p},
    Filter.inter_mem ((normalPH ξ).open_target.mem_nhds (zero_mem_normalPH_target hξ))
      ((normalPH_symm_contDiffAt hξ).eventually (by norm_num)),
    Set.inter_subset_left, ?_⟩
  exact fun _ hp => hp.2

/-- The reduced residual retains all 2184 actual original rows. -/
def reducedResidual (ξ : Fin 4 → ℂ) (k : normalKernel ξ) : Residual :=
  normalResidual ξ ((normalPH ξ).symm (k, 0))

theorem reducedResidual_contDiffAt {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    ContDiffAt ℝ 2 (reducedResidual ξ) 0 := by
  have hi : ContDiffAt ℝ 2 (fun k : normalKernel ξ => (k, (0 : normalRange ξ))) 0 :=
    contDiff_id.contDiffAt.prodMk contDiff_const.contDiffAt
  have hs : ContDiffAt ℝ 2 (fun k : normalKernel ξ => (normalPH ξ).symm (k, 0)) 0 :=
    (normalPH_symm_contDiffAt hξ).comp 0 (f := fun k : normalKernel ξ => (k, 0)) hi
  exact (normalResidual_contDiff ξ 2).contDiffAt.comp 0 hs

theorem reducedResidual_zero {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    reducedResidual ξ 0 = 0 := by
  simp only [reducedResidual, Prod.mk_zero_zero, normalPH_symm_zero hξ,
    normalResidual, Submodule.coe_zero, add_zero, originalF_literalCfg ξ hξ.1]

/-- On the local coordinate target, full original zeros are exactly reduced zeros at range zero. -/
theorem originalF_zero_iff_coordinates (ξ : Fin 4 → ℂ) (p : Coordinates ξ)
    (hp : p ∈ (normalPH ξ).target) :
    originalF (literalCfg ξ + ((normalPH ξ).symm p : Cfg)) = 0 ↔
      p.2 = 0 ∧ reducedResidual ξ p.1 = 0 := by
  have hinv : chartMap ξ ((normalPH ξ).symm p) = p := (normalPH ξ).right_inv hp
  constructor
  · intro h
    have h2 : p.2 = 0 := by
      have hh := congrArg Prod.snd hinv
      change rangeProjection ξ (originalF (literalCfg ξ + ((normalPH ξ).symm p : Cfg))) = p.2 at hh
      rw [h, map_zero] at hh
      exact hh.symm
    refine ⟨h2, ?_⟩
    have hp0 : (p.1, (0 : normalRange ξ)) = p := Prod.ext rfl h2.symm
    simpa only [reducedResidual, normalResidual, hp0] using h
  · rintro ⟨h2, hG⟩
    have hp0 : (p.1, (0 : normalRange ξ)) = p := Prod.ext rfl h2.symm
    simpa only [reducedResidual, normalResidual, hp0] using hG

/-- The eliminated equations vanish on every reduced point in the actual local target. -/
theorem reducedResidual_rangeProjection (ξ : Fin 4 → ℂ) (k : normalKernel ξ)
    (hk : (k, (0 : normalRange ξ)) ∈ (normalPH ξ).target) :
    rangeProjection ξ (reducedResidual ξ k) = 0 := by
  exact congrArg Prod.snd ((normalPH ξ).right_inv hk)

theorem reducedResidual_hasFDerivAt_zero {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    HasFDerivAt (reducedResidual ξ) (0 : normalKernel ξ →L[ℝ] Residual) 0 := by
  have hi : HasFDerivAt (fun k : normalKernel ξ => (k, (0 : normalRange ξ)))
      (ContinuousLinearMap.inl ℝ (normalKernel ξ) (normalRange ξ)) 0 :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := ↥(normalKernel ξ))
      (F := Coordinates ξ) (ContinuousLinearMap.inl ℝ (normalKernel ξ) (normalRange ξ))
  have hs : HasFDerivAt (fun k : normalKernel ξ => (normalPH ξ).symm (k, 0))
      (((chartDerivative ξ).symm : Coordinates ξ →L[ℝ] normalC ξ).comp
        (ContinuousLinearMap.inl ℝ (normalKernel ξ) (normalRange ξ))) 0 :=
    HasFDerivAt.comp (𝕜 := ℝ) (E := ↥(normalKernel ξ))
      (F := Coordinates ξ) (G := ↥(normalC ξ)) 0
      (normalPH_symm_hasFDerivAt hξ) hi
  have hF : HasFDerivAt (normalResidual ξ) (normalDerivative ξ)
      ((normalPH ξ).symm ((0 : normalKernel ξ), 0)) := by
    simpa only [Prod.mk_zero_zero, normalPH_symm_zero hξ] using normalResidual_hasFDerivAt ξ
  have hcomp := HasFDerivAt.comp (𝕜 := ℝ) (E := ↥(normalKernel ξ))
    (F := ↥(normalC ξ)) (G := Residual)
    (f := fun k : normalKernel ξ => (normalPH ξ).symm (k, 0)) 0 hF hs
  apply hcomp.congr_fderiv
  apply ContinuousLinearMap.ext
  intro k
  change normalDerivative ξ ((chartDerivative ξ).symm (k, 0)) = 0
  rw [chartDerivative_symm_apply, map_zero, add_zero]
  exact k.property

theorem reducedResidual_fderiv_zero {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    fderiv ℝ (reducedResidual ξ) 0 = 0 := (reducedResidual_hasFDerivAt_zero hξ).fderiv

/-- The complete local native elimination interface, with no rank or inverse premise. -/
theorem native_local_implicit_reduction {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    Module.finrank ℝ (normalKernel ξ) = 28 ∧
    Module.finrank ℝ (normalRange ξ) = 973 ∧
    (0 : normalC ξ) ∈ (normalPH ξ).source ∧
    (0 : Coordinates ξ) ∈ (normalPH ξ).target ∧
    ContDiff ℝ 2 (chartMap ξ) ∧
    ContDiffAt ℝ 2 (normalPH ξ).symm 0 ∧
    ContDiffAt ℝ 2 (reducedResidual ξ) 0 ∧
    reducedResidual ξ 0 = 0 ∧
    fderiv ℝ (reducedResidual ξ) 0 = 0 ∧
    (∀ p ∈ (normalPH ξ).target,
      originalF (literalCfg ξ + ((normalPH ξ).symm p : Cfg)) = 0 ↔
        p.2 = 0 ∧ reducedResidual ξ p.1 = 0) :=
  ⟨finrank_normalKernel hξ, finrank_normalRange hξ, zero_mem_normalPH_source ξ,
    zero_mem_normalPH_target hξ, chartMap_contDiff ξ, normalPH_symm_contDiffAt hξ,
    reducedResidual_contDiffAt hξ, reducedResidual_zero hξ, reducedResidual_fderiv_zero hξ,
    originalF_zero_iff_coordinates ξ⟩

end CKM.NativeSliceImplicitReduction

#check @CKM.NativeSliceImplicitReduction.chartMap_hasFDerivAt
#check @CKM.NativeSliceImplicitReduction.normalPH_symm_contDiffAt
#check @CKM.NativeSliceImplicitReduction.originalF_zero_iff_coordinates
#check @CKM.NativeSliceImplicitReduction.reducedResidual_fderiv_zero
#check @CKM.NativeSliceImplicitReduction.native_local_implicit_reduction
#print axioms CKM.NativeSliceImplicitReduction.chartMap_hasFDerivAt
#print axioms CKM.NativeSliceImplicitReduction.normalPH_symm_contDiffAt
#print axioms CKM.NativeSliceImplicitReduction.originalF_zero_iff_coordinates
#print axioms CKM.NativeSliceImplicitReduction.reducedResidual_fderiv_zero
#print axioms CKM.NativeSliceImplicitReduction.native_local_implicit_reduction

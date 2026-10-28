module

public import A5KLin
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
The actual original-F derivative on the native normal slice. Its kernel is the
accepted tangent/normal intersection, not a surrogate matrix kernel. At an A5
good phase, accepted dimensions give kernel 28 and range 973. A chosen linear
complement and the first isomorphism theorem provide a continuous-linear
splitting and bounded right inverse on the range. Choices and bounds depend on
the phase; no nonlinear elimination, phase-uniform bound or exhaustion follows.
-/
set_option Elab.async false
noncomputable section

namespace CKM.NativeSliceNormalSplitting

open NativeFirstOrder NativeGroupSlice NativeFourFamily
open Option2.NativeStress.AnalyticDerivative (originalF)

/-- The derivative of all 2184 actual original rows on the native normal slice. -/
def normalDerivative (ξ : Fin 4 → ℂ) :
    normalC ξ →L[ℝ] (Fin 2184 → ℝ) :=
  (fderiv ℝ originalF (literalCfg ξ)).comp (normalC ξ).subtypeL

@[simp] theorem normalDerivative_apply (ξ : Fin 4 → ℂ) (n : normalC ξ) :
    normalDerivative ξ n = fderiv ℝ originalF (literalCfg ξ) (n : Cfg) := rfl

abbrev normalKernel (ξ : Fin 4 → ℂ) : Submodule ℝ (normalC ξ) :=
  LinearMap.ker (normalDerivative ξ).toLinearMap

abbrev normalRange (ξ : Fin 4 → ℂ) : Submodule ℝ (Fin 2184 → ℝ) :=
  LinearMap.range (normalDerivative ξ).toLinearMap

/-- The exact native kernel identification, preserving its ambient vector. -/
def kernelEquivTanN (ξ : Fin 4 → ℂ) : normalKernel ξ ≃ₗ[ℝ] tanN ξ where
  toFun x := ⟨x.1.1, ⟨x.2, x.1.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem kernelEquivTanN_coe (ξ : Fin 4 → ℂ) (x : normalKernel ξ) :
    ((kernelEquivTanN ξ x : tanN ξ) : Cfg) = (x.1 : Cfg) := rfl

theorem finrank_normalKernel {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    Module.finrank ℝ (normalKernel ξ) = 28 := by
  calc
    Module.finrank ℝ (normalKernel ξ) = Module.finrank ℝ (tanN ξ) :=
      (kernelEquivTanN ξ).finrank_eq
    _ = 28 := finrank_tanN hξ

theorem finrank_normalRange {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    Module.finrank ℝ (normalRange ξ) = 973 := by
  have h := (normalDerivative ξ).toLinearMap.finrank_range_add_finrank_ker
  change Module.finrank ℝ (normalRange ξ) + Module.finrank ℝ (normalKernel ξ) =
    Module.finrank ℝ (normalC ξ) at h
  rw [finrank_normalKernel hξ, finrank_normalC ξ hξ.1] at h
  omega

/-- A phase-dependent complement inside the actual normal space. -/
def normalComplement (ξ : Fin 4 → ℂ) : Submodule ℝ (normalC ξ) :=
  Classical.choose (Submodule.exists_isCompl (normalKernel ξ))

theorem normalComplement_isCompl (ξ : Fin 4 → ℂ) :
    IsCompl (normalKernel ξ) (normalComplement ξ) :=
  Classical.choose_spec (Submodule.exists_isCompl (normalKernel ξ))

/-- Quotient by the actual kernel, followed by the first isomorphism theorem. -/
def complementRangeLinearEquiv (ξ : Fin 4 → ℂ) :
    normalComplement ξ ≃ₗ[ℝ] normalRange ξ :=
  ((normalKernel ξ).quotientEquivOfIsCompl (normalComplement ξ)
    (normalComplement_isCompl ξ)).symm.trans
      (normalDerivative ξ).toLinearMap.quotKerEquivRange

/-- The genuine derivative restriction, with finite-dimensional continuity. -/
def complementRangeEquiv (ξ : Fin 4 → ℂ) :
    normalComplement ξ ≃L[ℝ] normalRange ξ :=
  LinearEquiv.toContinuousLinearEquiv (𝕜 := ℝ)
    (E := ↥(normalComplement ξ)) (F := ↥(normalRange ξ))
    (complementRangeLinearEquiv ξ)

@[simp] theorem complementRangeEquiv_apply (ξ : Fin 4 → ℂ)
    (e : normalComplement ξ) :
    ((complementRangeEquiv ξ e : normalRange ξ) : Fin 2184 → ℝ) =
      normalDerivative ξ (e : normalC ξ) := rfl

/-- Exact commutative equality in the original residual space. -/
theorem complementRangeEquiv_commutes (ξ : Fin 4 → ℂ) :
    (normalRange ξ).subtypeL.comp (complementRangeEquiv ξ).toContinuousLinearMap =
      (normalDerivative ξ).comp (normalComplement ξ).subtypeL := by
  ext e r
  rfl

theorem finrank_normalComplement {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    Module.finrank ℝ (normalComplement ξ) = 973 := by
  calc
    Module.finrank ℝ (normalComplement ξ) = Module.finrank ℝ (normalRange ξ) :=
      (complementRangeLinearEquiv ξ).finrank_eq
    _ = 973 := finrank_normalRange hξ

/-- A continuous-linear right inverse defined on exactly the derivative range. -/
def normalRightInverse (ξ : Fin 4 → ℂ) : normalRange ξ →L[ℝ] normalC ξ :=
  (normalComplement ξ).subtypeL.comp (complementRangeEquiv ξ).symm.toContinuousLinearMap

theorem normalDerivative_rightInverse (ξ : Fin 4 → ℂ) (y : normalRange ξ) :
    normalDerivative ξ (normalRightInverse ξ y) = (y : Fin 2184 → ℝ) := by
  have h := complementRangeEquiv_apply ξ ((complementRangeEquiv ξ).symm y)
  rw [(complementRangeEquiv ξ).apply_symm_apply] at h
  exact h.symm

theorem normalDerivative_comp_rightInverse (ξ : Fin 4 → ℂ) :
    (normalDerivative ξ).comp (normalRightInverse ξ) = (normalRange ξ).subtypeL := by
  ext y r
  exact congrFun (normalDerivative_rightInverse ξ y) r

theorem normalRightInverse_mem_complement (ξ : Fin 4 → ℂ) (y : normalRange ξ) :
    normalRightInverse ξ y ∈ normalComplement ξ :=
  ((complementRangeEquiv ξ).symm y).property

theorem normalRightInverse_bound (ξ : Fin 4 → ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : normalRange ξ,
      ‖normalRightInverse ξ y‖ ≤ C * ‖y‖ := by
  refine ⟨‖normalRightInverse ξ‖ + 1, by positivity, ?_⟩
  intro y
  calc
    ‖normalRightInverse ξ y‖ ≤ ‖normalRightInverse ξ‖ * ‖y‖ :=
      (normalRightInverse ξ).le_opNorm y
    _ ≤ (‖normalRightInverse ξ‖ + 1) * ‖y‖ := by gcongr; linarith

/-- End-to-end normal derivative splitting at each actual A5 good phase. -/
theorem native_normal_derivative_splitting {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    Module.finrank ℝ (normalKernel ξ) = 28 ∧
    Module.finrank ℝ (normalRange ξ) = 973 ∧
    IsCompl (normalKernel ξ) (normalComplement ξ) ∧
    Module.finrank ℝ (normalComplement ξ) = 973 ∧
    (normalRange ξ).subtypeL.comp (complementRangeEquiv ξ).toContinuousLinearMap =
      (normalDerivative ξ).comp (normalComplement ξ).subtypeL ∧
    (normalDerivative ξ).comp (normalRightInverse ξ) = (normalRange ξ).subtypeL ∧
    (∃ C : ℝ, 0 < C ∧ ∀ y : normalRange ξ,
      ‖normalRightInverse ξ y‖ ≤ C * ‖y‖) :=
  ⟨finrank_normalKernel hξ, finrank_normalRange hξ, normalComplement_isCompl ξ,
    finrank_normalComplement hξ, complementRangeEquiv_commutes ξ,
    normalDerivative_comp_rightInverse ξ, normalRightInverse_bound ξ⟩

end CKM.NativeSliceNormalSplitting
#check @CKM.NativeSliceNormalSplitting.normalDerivative
#check @CKM.NativeSliceNormalSplitting.kernelEquivTanN
#check @CKM.NativeSliceNormalSplitting.complementRangeEquiv
#check @CKM.NativeSliceNormalSplitting.normalRightInverse
#check @CKM.NativeSliceNormalSplitting.native_normal_derivative_splitting
#print axioms CKM.NativeSliceNormalSplitting.kernelEquivTanN
#print axioms CKM.NativeSliceNormalSplitting.complementRangeEquiv
#print axioms CKM.NativeSliceNormalSplitting.normalDerivative_comp_rightInverse
#print axioms CKM.NativeSliceNormalSplitting.native_normal_derivative_splitting

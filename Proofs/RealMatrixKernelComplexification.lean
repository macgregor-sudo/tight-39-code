module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

noncomputable section
namespace Option2.NativeStress.PhaseBookComplexificationA6
open scoped BigOperators
open Matrix
variable {m n κ : Type*} [Fintype n] [Fintype κ] [DecidableEq κ]

def complexMatrix (M : Matrix m n ℝ) : Matrix m n ℂ := M.map Complex.ofRealHom

theorem mulVec_re (M : Matrix m n ℝ) (v : n → ℂ) :
    M *ᵥ (fun j => (v j).re) = fun i => ((complexMatrix M *ᵥ v) i).re := by
  ext i
  simp [Matrix.mulVec, dotProduct, complexMatrix, Complex.mul_re]

theorem mulVec_im (M : Matrix m n ℝ) (v : n → ℂ) :
    M *ᵥ (fun j => (v j).im) = fun i => ((complexMatrix M *ᵥ v) i).im := by
  ext i
  simp [Matrix.mulVec, dotProduct, complexMatrix, Complex.mul_im]

def kernelRe (M : Matrix m n ℝ) (v : LinearMap.ker (complexMatrix M).mulVecLin) :
    LinearMap.ker M.mulVecLin :=
  ⟨fun j => (v.val j).re, by
    rw [LinearMap.mem_ker,Matrix.mulVecLin_apply,mulVec_re]
    have hv := v.property
    rw [LinearMap.mem_ker,Matrix.mulVecLin_apply] at hv
    rw [hv]
    rfl⟩

def kernelIm (M : Matrix m n ℝ) (v : LinearMap.ker (complexMatrix M).mulVecLin) :
    LinearMap.ker M.mulVecLin :=
  ⟨fun j => (v.val j).im, by
    rw [LinearMap.mem_ker,Matrix.mulVecLin_apply,mulVec_im]
    have hv := v.property
    rw [LinearMap.mem_ker,Matrix.mulVecLin_apply] at hv
    rw [hv]
    rfl⟩

/-- Complexify the REAL coefficient matrix of f; this asserts no complex
linearity of f or its original real domain. -/
def complexMap (f : (κ → ℝ) →ₗ[ℝ] (n → ℝ)) : (κ → ℂ) →ₗ[ℂ] (n → ℂ) :=
  (complexMatrix (LinearMap.toMatrix' f)).mulVecLin

theorem complexMap_re (f : (κ → ℝ) →ₗ[ℝ] (n → ℝ)) (v : κ → ℂ) :
    (fun i => (complexMap f v i).re) = f (fun k => (v k).re) := by
  change (fun i => ((complexMatrix (LinearMap.toMatrix' f) *ᵥ v) i).re) = _
  rw [← mulVec_re,LinearMap.toMatrix'_mulVec]

theorem complexMap_im (f : (κ → ℝ) →ₗ[ℝ] (n → ℝ)) (v : κ → ℂ) :
    (fun i => (complexMap f v i).im) = f (fun k => (v k).im) := by
  change (fun i => ((complexMatrix (LinearMap.toMatrix' f) *ᵥ v) i).im) = _
  rw [← mulVec_im,LinearMap.toMatrix'_mulVec]

def kernelAmbient (M : Matrix m n ℝ) (e : (κ → ℝ) ≃ₗ[ℝ] LinearMap.ker M.mulVecLin) :
    (κ → ℝ) →ₗ[ℝ] (n → ℝ) := (LinearMap.ker M.mulVecLin).subtype.comp e.toLinearMap

def complexKernelMap (M : Matrix m n ℝ) (e : (κ → ℝ) ≃ₗ[ℝ] LinearMap.ker M.mulVecLin) :
    (κ → ℂ) →ₗ[ℂ] LinearMap.ker (complexMatrix M).mulVecLin :=
  (complexMap (kernelAmbient M e)).codRestrict _ (by
    intro v
    rw [LinearMap.mem_ker]
    apply funext
    intro i
    apply Complex.ext
    · have hr := congrFun (mulVec_re M (complexMap (kernelAmbient M e) v)) i
      rw [complexMap_re] at hr
      have hker := (e (fun k => (v k).re)).property
      rw [LinearMap.mem_ker] at hker
      change M *ᵥ (e (fun k => (v k).re)).val = 0 at hker
      change (M *ᵥ (e (fun k => (v k).re)).val) i = _ at hr
      rw [hker] at hr
      exact hr.symm
    · have hi := congrFun (mulVec_im M (complexMap (kernelAmbient M e) v)) i
      rw [complexMap_im] at hi
      have hker := (e (fun k => (v k).im)).property
      rw [LinearMap.mem_ker] at hker
      change M *ᵥ (e (fun k => (v k).im)).val = 0 at hker
      change (M *ᵥ (e (fun k => (v k).im)).val) i = _ at hi
      rw [hker] at hi
      exact hi.symm)

theorem complexKernelMap_re (M : Matrix m n ℝ)
    (e : (κ → ℝ) ≃ₗ[ℝ] LinearMap.ker M.mulVecLin) (v : κ → ℂ) :
    (fun i => ((complexKernelMap M e v).val i).re) = (e (fun k => (v k).re)).val :=
  complexMap_re (kernelAmbient M e) v

theorem complexKernelMap_im (M : Matrix m n ℝ)
    (e : (κ → ℝ) ≃ₗ[ℝ] LinearMap.ker M.mulVecLin) (v : κ → ℂ) :
    (fun i => ((complexKernelMap M e v).val i).im) = (e (fun k => (v k).im)).val :=
  complexMap_im (kernelAmbient M e) v

def inverseCoordinates (M : Matrix m n ℝ)
    (e : (κ → ℝ) ≃ₗ[ℝ] LinearMap.ker M.mulVecLin)
    (v : LinearMap.ker (complexMatrix M).mulVecLin) : κ → ℂ :=
  fun k => ((e.symm (kernelRe M v) k : ℝ) : ℂ) + Complex.I * (e.symm (kernelIm M v) k : ℝ)

theorem complexKernelMap_inverse (M : Matrix m n ℝ)
    (e : (κ → ℝ) ≃ₗ[ℝ] LinearMap.ker M.mulVecLin)
    (v : LinearMap.ker (complexMatrix M).mulVecLin) :
    complexKernelMap M e (inverseCoordinates M e v) = v := by
  apply Subtype.ext
  apply funext
  intro i
  apply Complex.ext
  · have h := congrFun (complexKernelMap_re M e (inverseCoordinates M e v)) i
    simpa [inverseCoordinates,kernelRe] using h
  · have h := congrFun (complexKernelMap_im M e (inverseCoordinates M e v)) i
    simpa [inverseCoordinates,kernelIm] using h

theorem complexKernelMap_injective (M : Matrix m n ℝ)
    (e : (κ → ℝ) ≃ₗ[ℝ] LinearMap.ker M.mulVecLin) : Function.Injective (complexKernelMap M e) := by
  intro v w h
  have hr : (fun k => (v k).re) = fun k => (w k).re := by
    apply e.injective
    apply Subtype.ext
    rw [← complexKernelMap_re,← complexKernelMap_re,h]
  have hi : (fun k => (v k).im) = fun k => (w k).im := by
    apply e.injective
    apply Subtype.ext
    rw [← complexKernelMap_im,← complexKernelMap_im,h]
  funext k
  exact Complex.ext (congrFun hr k) (congrFun hi k)

/-- Every real kernel coordinate equivalence extends faithfully to the complex
kernel of the entrywise matrix extension, with explicit real/imaginary inverse. -/
def complexKernelEquiv (M : Matrix m n ℝ)
    (e : (κ → ℝ) ≃ₗ[ℝ] LinearMap.ker M.mulVecLin) :
    (κ → ℂ) ≃ₗ[ℂ] LinearMap.ker (complexMatrix M).mulVecLin :=
  LinearEquiv.ofBijective (complexKernelMap M e)
    ⟨complexKernelMap_injective M e,fun v => ⟨inverseCoordinates M e v,complexKernelMap_inverse M e v⟩⟩

theorem complexKernelEquiv_symm (M : Matrix m n ℝ)
    (e : (κ → ℝ) ≃ₗ[ℝ] LinearMap.ker M.mulVecLin)
    (v : LinearMap.ker (complexMatrix M).mulVecLin) :
    (complexKernelEquiv M e).symm v = inverseCoordinates M e v := by
  apply (complexKernelEquiv M e).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (complexKernelMap_inverse M e v).symm

end Option2.NativeStress.PhaseBookComplexificationA6

module

public import RealMatrixKernelComplexification
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Pi

@[expose] public section

/-! A complex derivative whose actual real slice is real-valued is the
complexification of that slice's real derivative. Injectivity then follows
from the real and imaginary parts separately. -/

noncomputable section
namespace Option2.NativeStress.RealSliceDerivativeA6
open PhaseBookComplexificationA6
open scoped Topology

def realEmbedding (σ : Type*) [Fintype σ] : (σ → ℝ) →L[ℝ] (σ → ℂ) :=
  ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

@[simp] theorem realEmbedding_apply {σ : Type*} [Fintype σ] (x : σ → ℝ) :
    realEmbedding σ x = fun i => (x i : ℂ) := rfl

variable {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ]

theorem complexMap_ofReal (L : (σ → ℝ) →ₗ[ℝ] (τ → ℝ)) (x : σ → ℝ) :
    complexMap L (realEmbedding σ x) = realEmbedding τ (L x) := by
  funext j
  apply Complex.ext
  · have h := congrFun (complexMap_re L (realEmbedding σ x)) j
    simpa only [realEmbedding_apply, Complex.ofReal_re] using h
  · have h := congrFun (complexMap_im L (realEmbedding σ x)) j
    have hz : (fun k => (realEmbedding σ x k).im) = (0 : σ → ℝ) := rfl
    rw [hz, map_zero] at h
    simpa only [realEmbedding_apply, Complex.ofReal_im, Pi.zero_apply] using h

/-- Agreement on an actual real slice near zero identifies the whole complex
derivative. The real target of f is essential. -/
theorem real_slice_fderiv_eq_complexMap
    (F : (σ → ℂ) → (τ → ℂ)) (f : (σ → ℝ) → (τ → ℝ))
    (L : (σ → ℝ) →L[ℝ] (τ → ℝ))
    (hF : DifferentiableAt ℂ F 0) (hf : HasFDerivAt f L 0)
    (hslice : ∀ᶠ x in 𝓝 (0 : σ → ℝ),
      F (fun i => (x i : ℂ)) = fun j => (f x j : ℂ)) :
    (fderiv ℂ F 0).toLinearMap = complexMap L.toLinearMap := by
  let A := fderiv ℂ F 0
  have hcomplex : HasFDerivAt F (A.restrictScalars ℝ) (realEmbedding σ 0) := by
    simpa only [map_zero] using hF.hasFDerivAt.restrictScalars ℝ
  have hfirst : HasFDerivAt (fun x => F (realEmbedding σ x))
      ((A.restrictScalars ℝ).comp (realEmbedding σ)) 0 :=
    hcomplex.comp 0 (realEmbedding σ).hasFDerivAt
  have hsecond : HasFDerivAt (fun x => F (realEmbedding σ x))
      ((realEmbedding τ).comp L) 0 :=
    ((realEmbedding τ).hasFDerivAt.comp 0 hf).congr_of_eventuallyEq hslice
  have hder := hfirst.unique hsecond
  have hreal (x : σ → ℝ) : A (realEmbedding σ x) = realEmbedding τ (L x) :=
    congrArg (fun D : (σ → ℝ) →L[ℝ] (τ → ℂ) => D x) hder
  apply LinearMap.ext
  intro v
  change A v = complexMap L.toLinearMap v
  have hv : realEmbedding σ (fun i => (v i).re) +
      Complex.I • realEmbedding σ (fun i => (v i).im) = v := by
    funext i
    change ((v i).re : ℂ) + Complex.I * ((v i).im : ℂ) = v i
    rw [mul_comm Complex.I, Complex.re_add_im]
  calc
    A v = A (realEmbedding σ (fun i => (v i).re) +
        Complex.I • realEmbedding σ (fun i => (v i).im)) := congrArg A hv.symm
    _ = realEmbedding τ (L (fun i => (v i).re)) +
        Complex.I • realEmbedding τ (L (fun i => (v i).im)) := by
      rw [map_add, map_smul, hreal, hreal]
    _ = complexMap L.toLinearMap (realEmbedding σ (fun i => (v i).re) +
        Complex.I • realEmbedding σ (fun i => (v i).im)) := by
      rw [map_add, map_smul, complexMap_ofReal, complexMap_ofReal]
      rfl
    _ = complexMap L.toLinearMap v := congrArg (complexMap L.toLinearMap) hv

theorem complexMap_injective_of_injective
    (L : (σ → ℝ) →ₗ[ℝ] (τ → ℝ)) (hL : Function.Injective L) :
    Function.Injective (complexMap L) := by
  intro v w h
  have hr : (fun i => (v i).re) = fun i => (w i).re := by
    apply hL
    rw [← complexMap_re, ← complexMap_re, h]
  have hi : (fun i => (v i).im) = fun i => (w i).im := by
    apply hL
    rw [← complexMap_im, ← complexMap_im, h]
  funext i
  exact Complex.ext (congrFun hr i) (congrFun hi i)

theorem real_slice_fderiv_injective
    (F : (σ → ℂ) → (τ → ℂ)) (f : (σ → ℝ) → (τ → ℝ))
    (L : (σ → ℝ) →L[ℝ] (τ → ℝ))
    (hF : DifferentiableAt ℂ F 0) (hf : HasFDerivAt f L 0)
    (hslice : ∀ᶠ x in 𝓝 (0 : σ → ℝ),
      F (fun i => (x i : ℂ)) = fun j => (f x j : ℂ))
    (hL : Function.Injective L) : Function.Injective (fderiv ℂ F 0) := by
  change Function.Injective (fderiv ℂ F 0).toLinearMap
  rw [real_slice_fderiv_eq_complexMap F f L hF hf hslice]
  exact complexMap_injective_of_injective L.toLinearMap hL

#print axioms Option2.NativeStress.RealSliceDerivativeA6.real_slice_fderiv_eq_complexMap
#print axioms Option2.NativeStress.RealSliceDerivativeA6.real_slice_fderiv_injective
end Option2.NativeStress.RealSliceDerivativeA6

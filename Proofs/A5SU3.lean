module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

/-!
# An analytic exponential chart of `SU(3)` (generic, Mathlib only)

`suMat k = ∑ⱼ kⱼ • gellMannⱼ` identifies `ℝ⁸` with the real Lie algebra `su(3)` of traceless
skew-Hermitian `3 × 3` complex matrices (the basis is `i` times the Gell-Mann matrices, with the
eighth rescaled to `diag(i, i, -2i)`). `suExp k = exp (suMat k)` lies in `SU(3)` for every `k`, is
real-analytic, and has strict derivative `suMat` at `0`.

The determinant identity `det (exp X) = exp (tr X)` is not in the pinned mathlib (it is a mathlib
TODO). Here only the skew-Hermitian case is needed; it follows from the spectral theorem for the
Hermitian matrix `-i X`.

Matrices carry no global norm. Analyticity is therefore stated for the entry function
`fun k i j => suExp k i j : (Fin 8 → ℝ) → Fin 3 → Fin 3 → ℂ`, which uses the product norm; proofs may
activate `Matrix.linftyOpNormedRing`/`Matrix.linftyOpNormedAlgebra` locally.
-/

noncomputable section

open Matrix Complex

namespace CKM.NativeFourFamily

/-- `i` times the Gell-Mann matrices (the eighth rescaled by `√3`): a real basis of `su(3)`. -/
def gellMann : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![0, I, 0; I, 0, 0; 0, 0, 0],
    !![0, 1, 0; -1, 0, 0; 0, 0, 0],
    !![I, 0, 0; 0, -I, 0; 0, 0, 0],
    !![0, 0, I; 0, 0, 0; I, 0, 0],
    !![0, 0, 1; 0, 0, 0; -1, 0, 0],
    !![0, 0, 0; 0, 0, I; 0, I, 0],
    !![0, 0, 0; 0, 0, 1; 0, -1, 0],
    !![I, 0, 0; 0, I, 0; 0, 0, -2 * I]]

/-- Real coordinates on `su(3)`. -/
def suMat (k : Fin 8 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ := ∑ j, ((k j : ℝ) : ℂ) • gellMann j

/-- The exponential chart of `SU(3)` at the identity. -/
def suExp (k : Fin 8 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ := NormedSpace.exp (suMat k)

/-- Explicit entries of `suMat`. -/
theorem su_suMat_eq (k : Fin 8 → ℝ) : suMat k =
    !![(k 2 + k 7 : ℂ) * I, (k 0 : ℂ) * I + k 1, (k 3 : ℂ) * I + k 4;
       (k 0 : ℂ) * I - k 1, (-k 2 + k 7 : ℂ) * I, (k 5 : ℂ) * I + k 6;
       (k 3 : ℂ) * I - k 4, (k 5 : ℂ) * I - k 6, -2 * (k 7 : ℂ) * I] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suMat, gellMann, Fin.sum_univ_eight] <;> ring

theorem su_suMat_add (k k' : Fin 8 → ℝ) : suMat (k + k') = suMat k + suMat k' := by
  simp [suMat, add_smul, Finset.sum_add_distrib]

theorem su_suMat_smul (c : ℝ) (k : Fin 8 → ℝ) : suMat (c • k) = (c : ℂ) • suMat k := by
  simp only [suMat, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.smul_sum, smul_smul]

/-- `suMat` as a continuous real-linear map into the entry space. -/
def suMatCLM : (Fin 8 → ℝ) →L[ℝ] (Fin 3 → Fin 3 → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun k i j => suMat k i j
      map_add' := by
        intro k k'
        rw [su_suMat_add]
        rfl
      map_smul' := by
        intro c k
        ext i j
        simp [su_suMat_smul, Complex.real_smul] }

/-- Cartan coordinates: for `∑ β = 0`, `suMat (cartanCoord β) = diag (i β)`. -/
def cartanCoord (β : Fin 3 → ℝ) : Fin 8 → ℝ :=
  Pi.single 2 (β 0 + β 2 / 2) + Pi.single 7 (-(β 2) / 2)

theorem suMatCLM_apply (k : Fin 8 → ℝ) (i j : Fin 3) : suMatCLM k i j = suMat k i j := rfl

theorem suMat_conjTranspose (k : Fin 8 → ℝ) : (suMat k)ᴴ = -suMat k := by
  rw [su_suMat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply] <;> ring

theorem suMat_trace (k : Fin 8 → ℝ) : (suMat k).trace = 0 := by
  rw [su_suMat_eq, Matrix.trace_fin_three]
  simp
  ring

theorem suMat_injective : Function.Injective suMat := by
  intro k k' h
  rw [su_suMat_eq, su_suMat_eq] at h
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e02 := congrFun (congrFun h 0) 2
  have e12 := congrFun (congrFun h 1) 2
  have e22 := congrFun (congrFun h 2) 2
  simp [Complex.ext_iff] at e00 e01 e02 e12 e22
  funext j
  fin_cases j <;> simp <;> linarith

theorem suMat_surjective (X : Matrix (Fin 3) (Fin 3) ℂ) (hX : Xᴴ = -X) (htr : X.trace = 0) :
    ∃ k, suMat k = X := by
  have hs : ∀ i j, star (X j i) = -X i j := fun i j => by
    have h := congrFun (congrFun hX i) j
    simpa [Matrix.conjTranspose_apply] using h
  have hr : ∀ i j, (X j i).re = -(X i j).re := fun i j => by
    have h := congrArg Complex.re (hs i j); simpa using h
  have hi : ∀ i j, (X j i).im = (X i j).im := fun i j => by
    have h := congrArg Complex.im (hs i j); simpa using h
  rw [Matrix.trace_fin_three] at htr
  have htr' := congrArg Complex.im htr
  simp only [Complex.add_im, Complex.zero_im] at htr'
  have r00 := hr 0 0
  have r11 := hr 1 1
  have r22 := hr 2 2
  have r10 := hr 0 1
  have r20 := hr 0 2
  have r21 := hr 1 2
  have i10 := hi 0 1
  have i20 := hi 0 2
  have i21 := hi 1 2
  refine ⟨![(X 0 1).im, (X 0 1).re, (X 0 0).im + (X 2 2).im / 2, (X 0 2).im, (X 0 2).re,
    (X 1 2).im, (X 1 2).re, -(X 2 2).im / 2], ?_⟩
  rw [su_suMat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.ext_iff] <;> (try constructor) <;> linarith

theorem suExp_zero : suExp 0 = 1 := by
  have : suMat 0 = 0 := by simp [suMat]
  rw [suExp, this, NormedSpace.exp_zero]

/-- `exp X` is unitary for skew-Hermitian `X`. -/
theorem su_exp_unitary (X : Matrix (Fin 3) (Fin 3) ℂ) (hX : Xᴴ = -X) :
    NormedSpace.exp X ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hX,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl X)), add_neg_cancel,
    NormedSpace.exp_zero]

/-- `det (exp X) = 1` for traceless skew-Hermitian `X`: diagonalize the Hermitian matrix `-i X`
(spectral theorem, `Matrix.IsHermitian.spectral_theorem`), so `det (exp X) = ∏ exp (i λⱼ) =
exp (tr X)`. -/
theorem su_det_exp_skew (X : Matrix (Fin 3) (Fin 3) ℂ) (hX : Xᴴ = -X) (htr : X.trace = 0) :
    (NormedSpace.exp X).det = 1 := by
  have hH : ((-I) • X).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hX]
    simp
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  set U : Matrix (Fin 3) (Fin 3) ℂ := (hH.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℂ) with hU
  set D : Matrix (Fin 3) (Fin 3) ℂ := diagonal (RCLike.ofReal ∘ hH.eigenvalues) with hD
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hUinv : U⁻¹ = star U := Matrix.inv_eq_right_inv hUU
  have hUunit : IsUnit U := by
    have : IsUnit U.det := Matrix.isUnit_det_of_right_inverse hUU
    exact (Matrix.isUnit_iff_isUnit_det U).mpr this
  have hXeq : X = U * (I • D) * U⁻¹ := by
    have h1 : X = I • ((-I) • X) := by
      rw [smul_smul]; simp
    rw [h1, hspec, hUinv]
    simp
  have htrD : (I • D).trace = 0 := by
    rw [← htr, hXeq, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det U).mp hUunit), Matrix.one_mul]
  rw [hXeq, Matrix.exp_conj _ _ hUunit, Matrix.det_conj hUunit, hD, ← Matrix.diagonal_smul,
    Matrix.exp_diagonal, Matrix.det_diagonal, Pi.exp_def]
  rw [hD, ← Matrix.diagonal_smul, Matrix.trace_diagonal] at htrD
  simp only [← Complex.exp_eq_exp_ℂ]
  rw [← Complex.exp_sum, htrD, Complex.exp_zero]


/-- `det (exp X) = 1` for traceless skew-Hermitian `X`, through the spectral theorem. -/
theorem suExp_mem_specialUnitaryGroup (k : Fin 8 → ℝ) :
    suExp k ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ :=
  Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨su_exp_unitary _ (suMat_conjTranspose k),
      su_det_exp_skew _ (suMat_conjTranspose k) (suMat_trace k)⟩

theorem suExp_mul_conjTranspose (k : Fin 8 → ℝ) : suExp k * (suExp k)ᴴ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp (su_exp_unitary _ (suMat_conjTranspose k))
  rwa [Matrix.star_eq_conjTranspose] at h

theorem suExp_det (k : Fin 8 → ℝ) : (suExp k).det = 1 :=
  su_det_exp_skew _ (suMat_conjTranspose k) (suMat_trace k)

section SUAnalytic

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private def su_matCLM : (Fin 8 → ℝ) →L[ℝ] Matrix (Fin 3) (Fin 3) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := suMat
      map_add' := su_suMat_add
      map_smul' := fun c k => by
        rw [su_suMat_smul, Complex.coe_smul]
        rfl }

private def su_entryCLM : Matrix (Fin 3) (Fin 3) ℂ →L[ℝ] (Fin 3 → Fin 3 → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M i j => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

private theorem su_suExp_entry :
    (fun k (i j : Fin 3) => suExp k i j) = fun k => su_entryCLM (NormedSpace.exp (su_matCLM k)) :=
  rfl

theorem analyticAt_suExp (k₀ : Fin 8 → ℝ) :
    AnalyticAt ℝ (fun k (i j : Fin 3) => suExp k i j) k₀ := by
  rw [su_suExp_entry]
  exact (su_entryCLM.analyticAt _).comp
    ((NormedSpace.exp_analytic (𝕂 := ℝ) _).comp (su_matCLM.analyticAt _))

theorem hasStrictFDerivAt_suExp :
    HasStrictFDerivAt (fun k (i j : Fin 3) => suExp k i j) suMatCLM 0 := by
  have h0 : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin 3) (Fin 3) ℂ → _)
      (1 : Matrix (Fin 3) (Fin 3) ℂ →L[ℝ] Matrix (Fin 3) (Fin 3) ℂ) (su_matCLM 0) := by
    rw [map_zero]
    exact hasStrictFDerivAt_exp_zero
  have h := su_entryCLM.hasStrictFDerivAt.comp (0 : Fin 8 → ℝ)
    (h0.comp (0 : Fin 8 → ℝ) su_matCLM.hasStrictFDerivAt)
  rw [su_suExp_entry]
  convert h using 1
  ext k i j
  rfl

end SUAnalytic

theorem suMat_cartanCoord (β : Fin 3 → ℝ) (hβ : β 0 + β 1 + β 2 = 0) :
    suMat (cartanCoord β) = Matrix.diagonal fun j => ((β j : ℝ) : ℂ) * I := by
  have h1 : (β 1 : ℂ) = -(β 0 : ℂ) - β 2 := by
    have : β 1 = -β 0 - β 2 := by linarith
    exact_mod_cast this
  rw [su_suMat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cartanCoord, h1] <;> ring

theorem suExp_cartanCoord (β : Fin 3 → ℝ) (hβ : β 0 + β 1 + β 2 = 0) :
    suExp (cartanCoord β) = Matrix.diagonal fun j => Complex.exp (((β j : ℝ) : ℂ) * I) := by
  rw [suExp, suMat_cartanCoord β hβ, Matrix.exp_diagonal, Pi.exp_def, Complex.exp_eq_exp_ℂ]

end CKM.NativeFourFamily

#print axioms CKM.NativeFourFamily.suMatCLM
#print axioms CKM.NativeFourFamily.suMatCLM_apply
#print axioms CKM.NativeFourFamily.suMat_conjTranspose
#print axioms CKM.NativeFourFamily.suMat_trace
#print axioms CKM.NativeFourFamily.suMat_injective
#print axioms CKM.NativeFourFamily.suMat_surjective
#print axioms CKM.NativeFourFamily.suExp_zero
#print axioms CKM.NativeFourFamily.suExp_mem_specialUnitaryGroup
#print axioms CKM.NativeFourFamily.suExp_mul_conjTranspose
#print axioms CKM.NativeFourFamily.suExp_det
#print axioms CKM.NativeFourFamily.analyticAt_suExp
#print axioms CKM.NativeFourFamily.hasStrictFDerivAt_suExp
#print axioms CKM.NativeFourFamily.suMat_cartanCoord
#print axioms CKM.NativeFourFamily.suExp_cartanCoord

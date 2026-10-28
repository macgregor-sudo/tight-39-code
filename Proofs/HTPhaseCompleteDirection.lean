module

public import DirKNative

@[expose] public section

/-!
# Phase Book direction `Vxi`

`Vxi ξ hξ` is the term-by-term phase analogue of the specified
`realV_eq_real_column_sum`, with every D6 column replaced by the ACTUAL A5 pre-family derivative
`preVar ξ hξ H (X, X, 0)` at the same root parameter. Proved here, for every `IsUnitPhase ξ`
(resonant phases included):
* `Vxi_tangent`: tangency to the genuine `originalF` derivative at `Pxi ξ`;
* `Vxi_base`: `Vxi exactPhases = realVContinuousLinearMap` (accepted D6/realV map);
* `Vxi_fixedK`: `Vxi ξ hξ z = Re(Σ_j y_j(z) K_j · literalCfg ξ)` with the FIXED JSON operators `K_j`
  (`kMat`, kernel-checked against the accepted Lean sheet operator), and `Vxi_fixedK_complex`: the complex
  sum is already real (conjugation structure `K_{j̄} = −conj K_j`, `y_{j̄} = −conj y_j`);
* `Vxi_native`: the same with the fixed native Albert operators `kRe`, `kIm`.
First-party.
-/

set_option Elab.async false
noncomputable section

namespace Option2.NativeStress.HTPhaseComplete

open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open Option2.NativeStress.BookHT Option2.NativeStress.BookHT.TangentCoordinates
open Option2.NativeStress.BookHT.NativeNormalKernelBridge
open QuadraticCertificate.ExactCKMConfiguration
open NativePolynomial
open scoped ComplexConjugate

/-- The literal phase point in the 1053 original coordinates. -/
abbrev Pxi (ξ : Fin 4 → ℂ) : Fin 1053 → ℝ := PartialAction.pack (literalCfg ξ)

/-- Real coefficient functional `z ↦ Re (realCoordinates z j)` (accepted Book substitution). -/
def coordRe (j : Fin 24) : BookHT.Blocks →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => ((realCoordinatesLinearMap z).val j).re
      map_add' := by intro z w; simp [map_add]
      map_smul' := by intro a z; simp [map_smul] }

/-- Imaginary coefficient functional `z ↦ Im (realCoordinates z j)`. -/
def coordIm (j : Fin 24) : BookHT.Blocks →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => ((realCoordinatesLinearMap z).val j).im
      map_add' := by intro z w; simp [map_add]
      map_smul' := by intro a z; simp [map_smul] }

/-- Phase column for the real part of Book coordinate `j`: the actual A5 family variation. -/
def colRe (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (j : Fin 24) : Fin 1053 → ℝ :=
  PartialAction.pack (preVar ξ hξ (d6Sheet (eigenIndex j))
    (rootRealParam ⟨(eigenIndex j).val % 6, by omega⟩,
      rootRealParam ⟨(eigenIndex j).val % 6, by omega⟩, 0))

/-- Phase column for the imaginary part of Book coordinate `j`. -/
def colIm (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (j : Fin 24) : Fin 1053 → ℝ :=
  PartialAction.pack (preVar ξ hξ (d6Sheet (eigenIndex j))
    (rootImagParam ⟨(eigenIndex j).val % 6, by omega⟩,
      rootImagParam ⟨(eigenIndex j).val % 6, by omega⟩, 0))

/-- The phase Book direction. Real continuous-linear by construction. -/
def Vxi (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : BookHT.Blocks →L[ℝ] (Fin 1053 → ℝ) :=
  ∑ j : Fin 24, ((coordRe j).smulRight (colRe ξ hξ j) - (coordIm j).smulRight (colIm ξ hξ j))

theorem Vxi_apply (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : BookHT.Blocks) :
    Vxi ξ hξ z = ∑ j : Fin 24, ((Dictionary.realCoordinates z j).re • colRe ξ hξ j -
      (Dictionary.realCoordinates z j).im • colIm ξ hξ j) := by
  simp only [Vxi, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smulRight_apply]
  rfl

/-! ## Tangency at every unit phase -/

theorem Vxi_tangent (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : BookHT.Blocks) :
    fderiv ℝ Option2.NativeStress.originalF (Pxi ξ) (Vxi ξ hξ z) = 0 := by
  rw [Vxi_apply, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [map_sub, map_smul, map_smul, colRe, colIm, preVar_mem_original_kernel,
    preVar_mem_original_kernel, smul_zero, smul_zero, sub_self]

/-! ## Base normalization -/

private theorem fin1053_split (v : Fin 1053) :
    (⟨27 * (v.val / 27) + v.val % 27, by omega⟩ : Fin 1053) = v := by
  apply Fin.ext; change 27 * (v.val / 27) + v.val % 27 = v.val; omega

theorem colRe_exactPhases (j : Fin 24) :
    colRe exactPhases exactPhases_unit j = fun v => (d6Column (eigenIndex j) v).re := by
  funext v
  have h := d6Column_re_preVar_point (eigenIndex j) ⟨v.val / 27, by omega⟩ ⟨v.val % 27, by omega⟩
  rw [fin1053_split] at h
  exact h.symm

theorem colIm_exactPhases (j : Fin 24) :
    colIm exactPhases exactPhases_unit j = fun v => (d6Column (eigenIndex j) v).im := by
  funext v
  have h := d6Column_im_preVar_point (eigenIndex j) ⟨v.val / 27, by omega⟩ ⟨v.val % 27, by omega⟩
  rw [fin1053_split] at h
  exact h.symm

theorem Vxi_base_apply (z : BookHT.Blocks) : Vxi exactPhases exactPhases_unit z = realV z := by
  rw [Vxi_apply, realV_eq_real_column_sum]
  simp only [colRe_exactPhases, colIm_exactPhases]

theorem Vxi_base : Vxi exactPhases exactPhases_unit = realVContinuousLinearMap :=
  ContinuousLinearMap.ext fun z => by rw [Vxi_base_apply, realVContinuousLinearMap_apply]

/-! ## The fixed-operator form -/

/-- Columns are the fixed native operators applied to the literal phase point. -/
theorem colRe_native (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (j : Fin 24) (v : Fin 1053) :
    colRe ξ hξ j v = upperCoordinates (kRe (eigenIndex j)
      (literalPoint ξ ⟨v.val / 27, by omega⟩)) ⟨v.val % 27, by omega⟩ := by
  rw [kRe_preVar hξ]; rfl

theorem colIm_native (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (j : Fin 24) (v : Fin 1053) :
    colIm ξ hξ j v = upperCoordinates (kIm (eigenIndex j)
      (literalPoint ξ ⟨v.val / 27, by omega⟩)) ⟨v.val % 27, by omega⟩ := by
  rw [kIm_preVar hξ]; rfl

/-- `Vxi = Re(K^ℝ(z) · literalPoint ξ)` with the fixed native operators, state by state. -/
theorem Vxi_native (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : BookHT.Blocks) (v : Fin 1053) :
    Vxi ξ hξ z v = ∑ j : Fin 24,
      ((Dictionary.realCoordinates z j).re *
          upperCoordinates (kRe (eigenIndex j) (literalPoint ξ ⟨v.val / 27, by omega⟩))
            ⟨v.val % 27, by omega⟩ -
        (Dictionary.realCoordinates z j).im *
          upperCoordinates (kIm (eigenIndex j) (literalPoint ξ ⟨v.val / 27, by omega⟩))
            ⟨v.val % 27, by omega⟩) := by
  rw [Vxi_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    colRe_native, colIm_native]

/-- The complex weight `(K_j · literalCfg ξ)` at packed coordinate `v`, with the JSON matrices. -/
def kWeight (ξ : Fin 4 → ℂ) (j : Fin 24) (v : Fin 1053) : ℂ :=
  ∑ c : Fin 27, Q12.toComplex (kMat j ⟨v.val % 27, by omega⟩ c) *
    (literalCfg ξ ⟨v.val / 27, by omega⟩ c : ℂ)

theorem kWeight_re (ξ : Fin 4 → ℂ) (j : Fin 24) (v : Fin 1053) :
    (kWeight ξ j v).re = upperCoordinates (kRe (eigenIndex j)
      (literalPoint ξ ⟨v.val / 27, by omega⟩)) ⟨v.val % 27, by omega⟩ := by
  rw [kRe_coords, kWeight, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.re_mul_ofReal, kMat_eq_q12Op]
  rfl

theorem kWeight_im (ξ : Fin 4 → ℂ) (j : Fin 24) (v : Fin 1053) :
    (kWeight ξ j v).im = upperCoordinates (kIm (eigenIndex j)
      (literalPoint ξ ⟨v.val / 27, by omega⟩)) ⟨v.val % 27, by omega⟩ := by
  rw [kIm_coords, kWeight, Complex.im_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.im_mul_ofReal, kMat_eq_q12Op]
  rfl

/-- The brief's candidate, exactly: `Vxi ξ z = Re(K(y(z)) · literalCfg ξ)` with the FIXED JSON `K_j`. -/
theorem Vxi_fixedK (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : BookHT.Blocks) (v : Fin 1053) :
    Vxi ξ hξ z v = (∑ j : Fin 24, Dictionary.realCoordinates z j * kWeight ξ j v).re := by
  rw [Vxi_native, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.mul_re, kWeight_re, kWeight_im]

theorem kWeight_bar (ξ : Fin 4 → ℂ) (j : Fin 24) (v : Fin 1053) :
    kWeight ξ (Dictionary.coordinateBar j) v = -conj (kWeight ξ j v) := by
  simp only [kWeight, kMat_bar, map_neg, Q12.toComplex_conj, map_sum, map_mul,
    Complex.conj_ofReal, neg_mul, Finset.sum_neg_distrib]

/-- Real/conjugation handling: the complex sum `Σ_j y_j (K_j · literalCfg ξ)` is already real. -/
theorem Vxi_fixedK_complex (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : BookHT.Blocks)
    (v : Fin 1053) :
    ((Vxi ξ hξ z v : ℝ) : ℂ) = ∑ j : Fin 24, Dictionary.realCoordinates z j * kWeight ξ j v := by
  have hc := BookRealFormTransport.linearCombination_conj Dictionary.coordinateBar
    Dictionary.coordinateBar_involutive (kWeight ξ) (kWeight_bar ξ)
    (Dictionary.realCoordinates z) (Dictionary.realCoordinates_bar z) v
  rw [BookRealFormTransport.linearCombination_apply] at hc
  rw [Vxi_fixedK]
  exact (Complex.conj_eq_iff_re.mp hc)

end Option2.NativeStress.HTPhaseComplete

open Option2.NativeStress.HTPhaseComplete
#print axioms Vxi
#print axioms Vxi_tangent
#print axioms Vxi_base
#print axioms Vxi_base_apply
#print axioms Vxi_native
#print axioms Vxi_fixedK
#print axioms Vxi_fixedK_complex

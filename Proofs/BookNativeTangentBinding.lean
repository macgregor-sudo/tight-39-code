module

public import BookRootFamilyDirections

@[expose] public section

/-!
The actual supplied Book realV directions are tangent to all original F residuals
at the actual literal Book base. Every column is first identified with native
simultaneous conjugation, then with an actual accepted A5 family derivative.
No tangent, rank, metric, covector cancellation or quadratic reproduction premise.
-/ 
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.BookHT.TangentCoordinates
open Option2.BookNativeBase CKM.NativeFirstOrder CKM.NativeFourFamily NativePolynomial
open QuadraticCertificate.ExactCKMConfiguration

theorem d6Column_re_originalF_derivative_zero (b : Fin 24) :
    fderiv ℝ Option2.NativeStress.originalF bookBase (fun v => (d6Column b v).re) = 0 := by
  let j : Fin 6 := ⟨b.val%6, by omega⟩
  have he : (fun v : Fin 1053 => (d6Column b v).re) =
      PartialAction.pack (preVar exactPhases exactPhases_unit (d6Sheet b)
        (rootRealParam j, rootRealParam j, 0)) := by
    funext v
    let p : Fin 39 := Fin.divNat (n := 27) v
    let k : Fin 27 := Fin.modNat (m := 39) v
    have hv : (⟨27*p.val+k.val, by omega⟩ : Fin 1053) = v := by
      apply Fin.ext
      change 27*(v.val/27)+v.val%27 = v.val
      omega
    have h := d6Column_re_preVar_point b p k
    rw [hv] at h
    exact h
  rw [he, ← pack_literalCfg_exactPhases]
  exact preVar_mem_original_kernel exactPhases_unit (d6Sheet b) _

theorem d6Column_im_originalF_derivative_zero (b : Fin 24) :
    fderiv ℝ Option2.NativeStress.originalF bookBase (fun v => (d6Column b v).im) = 0 := by
  let j : Fin 6 := ⟨b.val%6, by omega⟩
  have he : (fun v : Fin 1053 => (d6Column b v).im) =
      PartialAction.pack (preVar exactPhases exactPhases_unit (d6Sheet b)
        (rootImagParam j, rootImagParam j, 0)) := by
    funext v
    let p : Fin 39 := Fin.divNat (n := 27) v
    let k : Fin 27 := Fin.modNat (m := 39) v
    have hv : (⟨27*p.val+k.val, by omega⟩ : Fin 1053) = v := by
      apply Fin.ext
      change 27*(v.val/27)+v.val%27 = v.val
      omega
    have h := d6Column_im_preVar_point b p k
    rw [hv] at h
    exact h
  rw [he, ← pack_literalCfg_exactPhases]
  exact preVar_mem_original_kernel exactPhases_unit (d6Sheet b) _

theorem realV_eq_real_column_sum (w : Blocks) :
    realV w = ∑ j : Fin 24,
      ((Dictionary.realCoordinates w j).re • (fun v => (d6Column (eigenIndex j) v).re) -
      (Dictionary.realCoordinates w j).im • (fun v => (d6Column (eigenIndex j) v).im)) := by
  funext v
  have h := congrArg Complex.re (realV_complex w v)
  rw [V_apply] at h
  simp only [← Complex.reCLM_apply, map_sum] at h
  simpa only [Complex.reCLM_apply, Complex.ofReal_re, Complex.mul_re, Finset.sum_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eigenColumn] using h

/-- All1053 supplied real coordinates satisfy the genuine derivative of all2184 original rows. -/
theorem realV_originalF_derivative_zero (w : Blocks) :
    fderiv ℝ Option2.NativeStress.originalF bookBase (realV w) = 0 := by
  rw [realV_eq_real_column_sum, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [map_sub, map_smul, map_smul,
    d6Column_re_originalF_derivative_zero, d6Column_im_originalF_derivative_zero]
  simp only [smul_zero, sub_self]

/-- The same exact statement at the already accepted original seed. -/
theorem realV_originalSeed_derivative_zero (w : Blocks) :
    fderiv ℝ Option2.NativeStress.originalF Option2.NativeStress.originalSeed (realV w) = 0 := by
  rw [← bookBase_eq_originalSeed]
  exact realV_originalF_derivative_zero w

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.realV_originalF_derivative_zero
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.realV_originalF_derivative_zero
#check Option2.NativeStress.BookHT.TangentCoordinates.realV_originalSeed_derivative_zero
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.realV_originalSeed_derivative_zero


module

public import NativeIncludedQuartetReadouts

@[expose] public section

/-!
Actual native mixed-product realization of left Hermitian multiplication.
The native Jordan product, signed hidden gauge and inverse coordinate maps are
those of the accepted NativeIncludedQuartetReadouts owner. No product or
complement-preservation hypothesis is added.
First-party composition of that owner and pinned Mathlib matrix/trace APIs
(065356127b1dc0016f66b7283ce0ce2c4055aa55, Apache-2.0).
Thanks to the native-model and Mathlib contributors. “If I have seen further it
is by standing on the sholders of Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
namespace CompactAlbert

/-- The inverse of the native mixed-action coefficient on Hermitian matrices. -/
def hermitianLeftPreimage (H : TitsComplexMatrix) : TitsComplexMatrix :=
  (H.trace.re : ℂ) • (1 : TitsComplexMatrix) - (2 : ℂ) • H

theorem hermitianLeftPreimage_isHermitian (H : TitsComplexMatrix)
    (hH : H.IsHermitian) : (hermitianLeftPreimage H).IsHermitian := by
  apply Matrix.IsHermitian.sub
  · exact Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])
  · exact hH.smul (by simp [IsSelfAdjoint])

/-- Dimension three is essential: tr((Re tr H)I - 2H) has real part Re tr H. -/
theorem hermitianLeftPreimage_trace_re (H : TitsComplexMatrix) :
    (hermitianLeftPreimage H).trace.re = H.trace.re := by
  simp [hermitianLeftPreimage, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, Complex.mul_re]
  <;> ring

/-- Exact recovery of the owner formula, including its factor one half. -/
theorem hermitianLeftPreimage_coefficient (H : TitsComplexMatrix) :
    (1 / 2 : ℂ) •
      (((hermitianLeftPreimage H).trace.re : ℂ) • (1 : TitsComplexMatrix) -
        hermitianLeftPreimage H) = H := by
  rw [hermitianLeftPreimage_trace_re]
  unfold hermitianLeftPreimage
  rw [sub_sub_cancel, smul_smul]
  norm_num

/-- An actual native hidden-only input, via the accepted inverse equivalences. -/
def nativeHiddenMatrix (B : TitsComplexMatrix) : Glennie.Albert :=
  compactTitsCoordinateEquiv.symm
    (titsHermitianPairEquiv.symm (⟨0, Matrix.isHermitian_zero⟩, B))

theorem nativeHiddenMatrix_pair (B : TitsComplexMatrix) :
    nativeTitsMatrixPair (nativeHiddenMatrix B) = (0, B) := by
  have h : toHermitianPair (toTitsCoordinates (nativeHiddenMatrix B)) =
      (⟨0, Matrix.isHermitian_zero⟩, B) := by
    change titsHermitianPairEquiv
      (compactTitsCoordinateEquiv (nativeHiddenMatrix B)) = _
    unfold nativeHiddenMatrix
    rw [LinearEquiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply Prod.ext
  · exact congrArg (fun q : HermitianTitsPair => q.1.val) h
  · exact congrArg (fun q : HermitianTitsPair => q.2) h

/-- Reuse the owner's actual visible-only embedding at the explicit preimage. -/
def nativeHermitianLeftInput (H : TitsComplexMatrix) (hH : H.IsHermitian) :
    Glennie.Albert :=
  includeHermitianMatrix ⟨hermitianLeftPreimage H, hermitianLeftPreimage_isHermitian H hH⟩

theorem nativeHermitianLeftInput_pair (H : TitsComplexMatrix) (hH : H.IsHermitian) :
    nativeTitsMatrixPair (nativeHermitianLeftInput H hH) = (hermitianLeftPreimage H, 0) :=
  includeHermitianMatrix_pair _

/-- Every Hermitian left multiplication is a genuine actual native mixed Jordan
product. This says nothing about an arbitrary fixer's hidden-complement action. -/
theorem native_jordan_realizes_hermitian_left (H B : TitsComplexMatrix)
    (hH : H.IsHermitian) :
    nativeTitsMatrixPair (Glennie.jordan (nativeHermitianLeftInput H hH)
      (nativeHiddenMatrix B)) = (0, H * B) := by
  change toMatrixPair (toTitsCoordinates (Glennie.jordan _ _)) = _
  rw [native_tits_product_pair]
  change compactSecondTitsProduct
    (nativeTitsMatrixPair (nativeHermitianLeftInput H hH))
    (nativeTitsMatrixPair (nativeHiddenMatrix B)) = _
  rw [nativeHermitianLeftInput_pair, nativeHiddenMatrix_pair]
  apply Prod.ext
  · simp [compactSecondTitsProduct, compactSecondTitsProductComplex]
  · simp only [compactSecondTitsProduct, compactSecondTitsProductHidden,
      Matrix.trace_zero, Complex.zero_re, Complex.ofReal_zero, zero_smul,
      sub_zero, zero_mul, zero_add, Matrix.adjugate_zero,
      Matrix.conjTranspose_zero, sub_self, add_zero]
    rw [← Matrix.smul_mul, hermitianLeftPreimage_coefficient]

end CompactAlbert

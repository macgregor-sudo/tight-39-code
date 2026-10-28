module

public import SelectedMinorKernel
public import NativePhaseRank
public import NativePhasePivotLocus
public import NativePhaseQuadraticBinding

@[expose] public section

/-! Actual pointwise complex D2/D3/D4 witnesses on the proved native pivot locus.
The80 free coordinates complement the exact retained973 column selection.
No claim of Laurent coefficients, Book normalization, or the48 Book stresses. -/

noncomputable section
namespace Option2.NativeStress.PhaseKernelA6
open PhasePivotA6 PhasePivotLocusA6 PhaseRankA6 PhaseHilbertA6
open SelectedMinorKernel PolynomialJets SliceLemmas
open A6Compact A6Compact.LinEngine CKM.NativeFirstOrder
open scoped BigOperators

theorem exists_native_linear_slice (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (hminor : (selectedMinor (nativeJ ξ)).det ≠ 0) :
    ∃ (B : Matrix (Fin 1053) (Fin 80) ℂ) (piv : Fin 80 → Fin 1053),
      Set.range piv = (Set.range colSelF)ᶜ ∧
      IsPivot B piv ∧
      (∀ r t, ∑ j, nativeJ ξ r j * B j t = 0) ∧
      cutLinearSpace (nativeRows ξ) id [] ≤ linearAnnihilator B ∧
      1053 - 80 ≤ Module.finrank ℂ (cutLinearSpace (nativeRows ξ) id []) ∧
      Module.finrank ℂ (LinearMap.ker (nativeJ ξ).mulVecLin) = 80 := by
  obtain ⟨piv, B, _, hcover, hB, hJB, hker⟩ :=
    exists_normalized_kernel (nativeJ ξ) rowSelF colSelF hminor (nativeJ_rank_le ξ hξ)
  refine ⟨B, piv, hcover, hB, hJB, ?_, ?_, hker⟩
  · apply ChainMid.cutLinearSpace_nil_le_linearAnnihilator (nativeRows ξ) id B
    exact hJB
  · exact ChainMid.le_finrank_cutLinearSpace_nil_of_det (nativeRows ξ) id
      rowSelF colSelF hminor

/-- Actual open-dense locus specialization. No rank or kernel premise remains. -/
theorem native_linear_slice_on_locus (u : NativePhaseTorus) (hu : u ∈ nativePivotLocus) :
    ∃ (B : Matrix (Fin 1053) (Fin 80) ℂ) (piv : Fin 80 → Fin 1053),
      Set.range piv = (Set.range colSelF)ᶜ ∧
      IsPivot B piv ∧
      (∀ r t, ∑ j, nativeJ u.1 r j * B j t = 0) ∧
      cutLinearSpace (nativeRows u.1) id [] ≤ linearAnnihilator B ∧
      1053 - 80 ≤ Module.finrank ℂ (cutLinearSpace (nativeRows u.1) id []) ∧
      Module.finrank ℂ (LinearMap.ker (nativeJ u.1).mulVecLin) = 80 :=
  exists_native_linear_slice u.1 u.2 hu

/-- Applying the same construction to the transpose supplies1211 independent
pointwise full-row annihilators. These are NOT asserted to be the Book48 family. -/
theorem exists_native_row_annihilators (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (hminor : (selectedMinor (nativeJ ξ)).det ≠ 0) :
    ∃ (w : Fin 1211 → Fin 2184 → ℂ) (piv : Fin 1211 → Fin 2184),
      Set.range piv = (Set.range rowSelF)ᶜ ∧
      (∀ t t', w t' (piv t) = if t = t' then 1 else 0) ∧
      (∀ t j, ∑ r, w t r * nativeJ ξ r j = 0) ∧
      Module.finrank ℂ (LinearMap.ker (nativeJ ξ).transpose.mulVecLin) = 1211 := by
  have hdet : ((nativeJ ξ).transpose.submatrix colSelF rowSelF).det ≠ 0 := by
    simpa only [selectedMinor, ← Matrix.transpose_submatrix, Matrix.det_transpose] using hminor
  have hrank : (nativeJ ξ).transpose.rank ≤ 973 := by
    rw [Matrix.rank_transpose]
    exact nativeJ_rank_le ξ hξ
  obtain ⟨piv, B, _, hcover, hB, hJB, hker⟩ :=
    exists_normalized_kernel (nativeJ ξ).transpose colSelF rowSelF hdet hrank
  refine ⟨fun t r => B r t, piv, hcover, hB, ?_, hker⟩
  intro t j
  simpa only [Matrix.transpose_apply, mul_comm] using hJB j t

end Option2.NativeStress.PhaseKernelA6

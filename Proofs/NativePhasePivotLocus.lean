module

public import NativePhasePivotFactor
public import GPTorus

@[expose] public section

noncomputable section
namespace Option2.NativeStress.PhasePivotLocusA6
open PhasePivotA6 HTPhaseKron
open CKM.NativeFirstOrder QuadraticCertificate.ExactCKMConfiguration

/-- The actual unit phases, with their existing subspace topology. -/
abbrev NativePhaseTorus := CKM.NativeGoodPhase.UnitTorus 4

/-- The original native selected973 minor, not merely an unrelated complex-unit determinant. -/
def nativePivotLocus : Set NativePhaseTorus :=
  {u | (selectedMinor (nativeJ u.1)).det ≠ 0}

def referenceNativePhase : NativePhaseTorus := ⟨exactPhases, exactPhases_unit'⟩

theorem nativePivotLocus_eq_polynomial :
    nativePivotLocus = CKM.NativeGoodPhase.evalNeZeroSet pivotPolynomial := by
  ext u
  change ((selectedMinor (nativeJ u.1)).det ≠ 0 ↔ MvPolynomial.eval u.1 pivotPolynomial ≠ 0)
  exact (polynomial_eval_ne_zero_iff_native_minor u.1 u.2).symm

theorem reference_polynomial_eval_ne_zero : MvPolynomial.eval exactPhases pivotPolynomial ≠ 0 :=
  (polynomial_eval_ne_zero_iff_native_minor exactPhases exactPhases_unit').mpr
    native_reference_minor_ne_zero

theorem referenceNativePhase_mem : referenceNativePhase ∈ nativePivotLocus :=
  native_reference_minor_ne_zero

theorem nativePivotLocus_nonempty : nativePivotLocus.Nonempty :=
  ⟨referenceNativePhase, referenceNativePhase_mem⟩

/-- Accepted polynomial density is applied on the ACTUAL four-phase torus.
This is only a Jacobian pivot locus, not the quadratic/Hilbert propagation. -/
theorem isOpen_dense_nativePivotLocus : IsOpen nativePivotLocus ∧ Dense nativePivotLocus := by
  rw [nativePivotLocus_eq_polynomial]
  exact ⟨CKM.NativeGoodPhase.isOpen_evalNeZeroSet pivotPolynomial,
    CKM.NativeGoodPhase.dense_evalNeZeroSet pivotPolynomial_ne_zero⟩

end Option2.NativeStress.PhasePivotLocusA6

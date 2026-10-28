module

public import SpecialUnitaryConstraintSplitting
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

/-!
# Explicit real coordinates for the actual SU3 constraint kernel

The carrier is literally the kernel of the frozen real
constraint differential. Two real imaginary-diagonal entries and three complex
upper entries determine a unique traceless skew-Hermitian matrix on the original
cyclic Index. Dimension is derived through this explicit linear equivalence,
not a rank certificate or assumed coordinate theorem. No manifold claim.
First-party composition of the accepted kernel equation and standard finite
linear-algebra APIs. Imported owners retain their notices and provenance.
Thanks to the Lean, mathlib and project contributors. “If I have seen further
it is by standing on the sholders of Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
open scoped Matrix.Norms.Elementwise
namespace UnitaryErrorBases.SpecialUnitaryConstraints

/-- Two real diagonal coordinates and the complex entries 01, 02 and 12. -/
abbrev ConstraintKernelCoordinates := (ℝ × ℝ) × (ℂ × ℂ × ℂ)

/-- The literal structural inverse, with trace-zero imaginary diagonal and
negative-conjugate lower entries in the original index convention. -/
def constraintKernelMatrix (x : ConstraintKernelCoordinates) : Mat := fun i j =>
  if i = 0 then
    if j = 0 then ⟨0, x.1.1⟩ else if j = 1 then x.2.1 else x.2.2.1
  else if i = 1 then
    if j = 0 then -star x.2.1 else if j = 1 then ⟨0, x.1.2⟩ else x.2.2.2
  else
    if j = 0 then -star x.2.2.1 else if j = 1 then -star x.2.2.2
    else ⟨0, -(x.1.1 + x.1.2)⟩

private lemma index_cases (i : Index) : i = 0 ∨ i = 1 ∨ i = 2 :=
  (by decide : ∀ i : Index, i = 0 ∨ i = 1 ∨ i = 2) i

@[simp] private lemma index_two_ne_zero : (2 : Index) ≠ 0 := by decide
@[simp] private lemma index_two_ne_one : (2 : Index) ≠ 1 := by decide

private lemma trace_eq_three_diagonal (A : Mat) :
    Matrix.trace A = A 0 0 + A 1 1 + A 2 2 := by
  have hu : (Finset.univ : Finset Index) = {0, 1, 2} := by decide
  simp [Matrix.trace, hu, Finset.sum_insert, index_two_ne_zero.symm,
    index_two_ne_one.symm, add_assoc]

/-- Every reconstructed matrix satisfies the exact frozen kernel equation. -/
theorem constraintKernelMatrix_mem (x : ConstraintKernelCoordinates) :
    constraintKernelMatrix x ∈ LinearMap.ker constraintDifferential.toLinearMap := by
  apply (constraintDifferential_kernel _).mpr
  constructor
  · ext i j
    rcases index_cases i with rfl | rfl | rfl <;>
      rcases index_cases j with rfl | rfl | rfl <;>
      simp [constraintKernelMatrix, Matrix.conjTranspose_apply, Complex.ext_iff]
  · rw [trace_eq_three_diagonal]
    simp [constraintKernelMatrix, Complex.ext_iff]

/-- The actual coordinate extraction on the literal kernel subtype. -/
def constraintKernelCoordinates (A : LinearMap.ker constraintDifferential.toLinearMap) :
    ConstraintKernelCoordinates :=
  (((A.val 0 0).im, (A.val 1 1).im), (A.val 0 1, A.val 0 2, A.val 1 2))

/-- Reconstructing the extracted coordinates recovers every actual kernel matrix. -/
theorem constraintKernelMatrix_coordinates
    (A : LinearMap.ker constraintDifferential.toLinearMap) :
    constraintKernelMatrix (constraintKernelCoordinates A) = A.val := by
  have hk := (constraintDifferential_kernel A.val).mp A.property
  have hd (i : Index) : (A.val i i).re = 0 := by
    have h := congrArg (fun M : Mat => (M i i).re) hk.1
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def,
      Complex.conj_re, Complex.neg_re] at h
    linarith
  have hl (i j : Index) : A.val j i = -star (A.val i j) := by
    have h := congrArg (fun M : Mat => M j i) hk.1
    change star (A.val i j) = -A.val j i at h
    simpa using (congrArg (fun z : ℂ => -z) h).symm
  have ht : (A.val 2 2).im = -((A.val 0 0).im + (A.val 1 1).im) := by
    have h := congrArg Complex.im hk.2
    rw [trace_eq_three_diagonal] at h
    simp only [Complex.add_im, Complex.zero_im] at h
    linarith
  have hl01 := hl 0 1
  have hl02 := hl 0 2
  have hl12 := hl 1 2
  ext i j
  rcases index_cases i with rfl | rfl | rfl <;>
    rcases index_cases j with rfl | rfl | rfl <;>
    simp [constraintKernelMatrix, constraintKernelCoordinates, hl01, hl02, hl12, Complex.ext_iff, hd, ht]

/-- Explicit real coordinates on the exact kernel, with no dimension premise. -/
def constraintKernelCoordinateEquiv :
    LinearMap.ker constraintDifferential.toLinearMap ≃ₗ[ℝ] ConstraintKernelCoordinates where
  toFun := constraintKernelCoordinates
  invFun x := ⟨constraintKernelMatrix x, constraintKernelMatrix_mem x⟩
  left_inv A := Subtype.ext (constraintKernelMatrix_coordinates A)
  right_inv x := by
    rcases x with ⟨⟨a, b⟩, u, v, w⟩
    simp [constraintKernelCoordinates, constraintKernelMatrix]
  map_add' A B := by
    ext <;> simp [constraintKernelCoordinates]
  map_smul' r A := by
    ext <;> simp [constraintKernelCoordinates]

/-- Exact entry binding for the forward coordinate equivalence. -/
theorem constraintKernelCoordinateEquiv_apply
    (A : LinearMap.ker constraintDifferential.toLinearMap) :
    constraintKernelCoordinateEquiv A =
      (((A.val 0 0).im, (A.val 1 1).im), (A.val 0 1, A.val 0 2, A.val 1 2)) := rfl

/-- The inverse equivalence uses the displayed structural matrix formula. -/
theorem constraintKernelCoordinateEquiv_symm_val (x : ConstraintKernelCoordinates) :
    (constraintKernelCoordinateEquiv.symm x).val = constraintKernelMatrix x := rfl

/-- The same equivalence with the existing finite-dimensional norm topologies. -/
def constraintKernelCoordinateContinuousLinearEquiv :
    LinearMap.ker constraintDifferential.toLinearMap ≃L[ℝ] ConstraintKernelCoordinates :=
  constraintKernelCoordinateEquiv.toContinuousLinearEquiv

/-- The actual kernel has real dimension eight. -/
theorem finrank_constraintDifferential_kernel :
    Module.finrank ℝ (LinearMap.ker constraintDifferential.toLinearMap) = 8 := by
  rw [constraintKernelCoordinateEquiv.finrank_eq]
  simp [ConstraintKernelCoordinates, Module.finrank_prod, Complex.finrank_real_complex]

end UnitaryErrorBases.SpecialUnitaryConstraints

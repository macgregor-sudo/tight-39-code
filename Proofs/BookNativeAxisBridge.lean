module

public import BookNativeRootSeparation

@[expose] public section

/-! The unchanged Book blocks are the six off-diagonal real parameters of
exactly their native A5 families, after the genuine orbit projection. -/
set_option Elab.async false
set_option maxRecDepth 2000
noncomputable section
namespace Option2.NativeStress.BookHT.NativeNormalKernelBridge
open TangentCoordinates CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open NativePolynomial QuadraticCertificate.ExactCKMConfiguration
open scoped ComplexConjugate

/-- Exact six real coordinates from the supplied Book eigenvector ordering. -/
def axisParameters (H : Fin 4) (u : Triple) : Fin 8 → ℝ :=
  let a : Fin 4 → Fin 8 → ℝ :=
    ![![(u 0).im, -(u 0).re, 0, (u 2).im, (u 2).re, (u 1).im, -(u 1).re, 0],
      ![(u 0).im, (u 0).re, 0, (u 1).im, -(u 1).re, (u 2).im, (u 2).re, 0],
      ![(u 1).im, -(u 1).re, 0, (u 2).im, (u 2).re, (u 0).im, -(u 0).re, 0],
      ![(u 2).im, (u 2).re, 0, (u 0).im, -(u 0).re, (u 1).im, (u 1).re, 0]]
  (a H 0) • Pi.single 0 1 + (a H 1) • Pi.single 1 1 + (a H 3) • Pi.single 3 1 +
    (a H 4) • Pi.single 4 1 + (a H 5) • Pi.single 5 1 + (a H 6) • Pi.single 6 1

theorem axisParameters_cartan (H : Fin 4) (u : Triple) :
    axisParameters H u 2 = 0 ∧ axisParameters H u 7 = 0 := by
  simp [axisParameters, Pi.single_apply]

private theorem map_single (F : (Fin 8 → ℝ) →L[ℝ] normalC exactPhases)
    (m : Fin 8) (a : ℝ) : F (Pi.single m a) = a • F (Pi.single m 1) := by
  rw [← map_smul]
  congr 1
  ext k
  simp [Pi.single_apply, ite_mul, mul_ite]

private theorem map_half (F : (Fin 8 → ℝ) →L[ℝ] normalC exactPhases) (m : Fin 8) :
    F (Pi.single m (1/2 : ℝ)) = (1/2 : ℝ) • F (Pi.single m 1) := map_single F m _
private theorem map_neg_half (F : (Fin 8 → ℝ) →L[ℝ] normalC exactPhases) (m : Fin 8) :
    F (Pi.single m (-(1/2) : ℝ)) = (-(1/2) : ℝ) • F (Pi.single m 1) := map_single F m _

set_option maxHeartbeats 800000 in
/-- Binding of all six real parameters; only the supplied 24 coefficient labels are reduced. -/
theorem projectedBook_axis (H : Fin 4) (u : Triple) :
    normalProjection (bookDirection (Pi.single H u)) =
      projectedSimultaneousFamily H (axisParameters H u) := by
  rw [bookDirection_apply, realV_eq_real_column_sum]
  simp only [map_sum, map_sub, map_smul, projected_d6_real_family, projected_d6_imag_family]
  fin_cases H <;>
    norm_num [Fin.sum_univ_succ, Dictionary.realCoordinates, eigenIndex, d6Sheet,
      rootRealParam, rootImagParam, Pi.single_apply, axisParameters, map_add,
      map_half, map_neg_half, map_smul, map_zero, zero_smul, sub_zero, zero_sub, Complex.neg_re,
      Complex.neg_im, Complex.conj_re, Complex.conj_im]
  all_goals module

/-- Explicit inverse on the native six-dimensional off-diagonal coordinate space. -/
def axisInverse (H : Fin 4) (X : Fin 8 → ℝ) : Triple :=
  WithLp.toLp 2
    (![![⟨-X 1, X 0⟩, ⟨-X 6, X 5⟩, ⟨X 4, X 3⟩],
       ![⟨X 1, X 0⟩, ⟨-X 4, X 3⟩, ⟨X 6, X 5⟩],
       ![⟨-X 6, X 5⟩, ⟨-X 1, X 0⟩, ⟨X 4, X 3⟩],
       ![⟨-X 4, X 3⟩, ⟨X 6, X 5⟩, ⟨X 1, X 0⟩]] H)

theorem axisParameters_axisInverse (H : Fin 4) (X : Fin 8 → ℝ)
    (h2 : X 2 = 0) (h7 : X 7 = 0) : axisParameters H (axisInverse H X) = X := by
  ext m
  fin_cases H <;> fin_cases m <;>
    simp [axisParameters, axisInverse, Pi.single_apply, h2, h7]

theorem axisInverse_axisParameters (H : Fin 4) (u : Triple) :
    axisInverse H (axisParameters H u) = u := by
  ext j
  fin_cases H <;> fin_cases j <;>
    simp [axisParameters, axisInverse, Pi.single_apply]

theorem projectedBook_axis_inter_common (H : Fin 4) (u : Triple)
    (hu : (projectedBook (Pi.single H u) : Cfg) ∈ fixQK exactPhases) : u = 0 := by
  have he := projectedBook_axis H u
  have hc : (projectedSimultaneousFamily H (axisParameters H u) : Cfg) ∈
      fixQK exactPhases := by rw [← he]; exact hu
  have hz := projected_offDiagonal_inter_common H (axisParameters H u)
    (axisParameters_cartan H u).1 (axisParameters_cartan H u).2 hc
  rw [← axisInverse_axisParameters H u, hz]
  ext j
  fin_cases H <;> fin_cases j <;> simp [axisInverse] <;> rfl

end Option2.NativeStress.BookHT.NativeNormalKernelBridge
#check Option2.NativeStress.BookHT.NativeNormalKernelBridge.projectedBook_axis
#check Option2.NativeStress.BookHT.NativeNormalKernelBridge.projectedBook_axis_inter_common
#print axioms Option2.NativeStress.BookHT.NativeNormalKernelBridge.projectedBook_axis
#print axioms Option2.NativeStress.BookHT.NativeNormalKernelBridge.projectedBook_axis_inter_common

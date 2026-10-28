module

public import BookNativeRealFormDirect
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option Elab.async false

@[expose] public section

/-!
The accepted literal Book coordinate substitution and supplied sparse map,
now with their real continuous-linear interface. Blocks retains the canonical
outer finite Pi norm on four complex Euclidean triples; the target retains the
canonical finite Pi norm on Fin 1053. No norm or topology is replaced here.
This proves neither native tangent membership nor a metric, rank, or stress
identity.
-/

noncomputable section

namespace Option2.NativeStress.BookHT.TangentCoordinates

open Dictionary
open scoped ComplexConjugate ContDiff

/-- The actual 24-coordinate substitution, valued in its proved real form. -/
def realCoordinatesLinearMap : Blocks →ₗ[ℝ]
    BookRealFormTransport.realForm coordinateBar where
  toFun z := ⟨realCoordinates z, realCoordinates_bar z⟩
  map_add' z w := by
    apply Subtype.ext
    funext j
    change realCoordinates (z + w) j = realCoordinates z j + realCoordinates w j
    revert j
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
    simp [realCoordinates, PiLp.add_apply, map_add, add_comm]
  map_smul' a z := by
    apply Subtype.ext
    funext j
    change realCoordinates (a • z) j = a • realCoordinates z j
    revert j
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
    simp [realCoordinates, PiLp.smul_apply, Complex.real_smul]

@[simp] theorem realCoordinatesLinearMap_coe (z : Blocks) :
    (realCoordinatesLinearMap z).val = realCoordinates z := rfl

/-- The same supplied real map, with continuity from its finite-dimensional domain. -/
def realVContinuousLinearMap : Blocks →L[ℝ] (Fin 1053 → ℝ) :=
  (realRestriction.comp realCoordinatesLinearMap).toContinuousLinearMap

@[simp] theorem coe_realVContinuousLinearMap :
    ⇑realVContinuousLinearMap = realV := rfl

@[simp] theorem realVContinuousLinearMap_apply (z : Blocks) :
    realVContinuousLinearMap z = realV z := rfl

theorem continuous_realV : Continuous realV := by
  simpa only [coe_realVContinuousLinearMap] using realVContinuousLinearMap.continuous

theorem contDiff_realV : ContDiff ℝ ∞ realV := by
  simpa only [coe_realVContinuousLinearMap] using realVContinuousLinearMap.contDiff (n := ∞)

theorem hasFDerivAt_realV (z : Blocks) :
    HasFDerivAt realV realVContinuousLinearMap z := by
  simpa only [coe_realVContinuousLinearMap] using realVContinuousLinearMap.hasFDerivAt (x := z)

theorem fderiv_realV_apply (z n : Blocks) :
    (fderiv ℝ realV z) n = realV n := by
  rw [(hasFDerivAt_realV z).fderiv]
  exact realVContinuousLinearMap_apply n

/-- Every packed derivative coordinate has the accepted supplied complex formula. -/
theorem fderiv_realV_complex (z n : Blocks) (r : Fin 1053) :
    ((fderiv ℝ realV z) n r : ℂ) = V (realCoordinates n) r := by
  rw [fderiv_realV_apply]
  exact realV_complex n r

end Option2.NativeStress.BookHT.TangentCoordinates

open Option2.NativeStress.BookHT.TangentCoordinates

#check @realCoordinatesLinearMap
#check @realCoordinatesLinearMap_coe
#check @realVContinuousLinearMap
#check @coe_realVContinuousLinearMap
#check @continuous_realV
#check @contDiff_realV
#check @hasFDerivAt_realV
#check @fderiv_realV_apply
#check @fderiv_realV_complex
#print axioms realCoordinatesLinearMap_coe
#print axioms coe_realVContinuousLinearMap
#print axioms continuous_realV
#print axioms contDiff_realV
#print axioms hasFDerivAt_realV
#print axioms fderiv_realV_apply
#print axioms fderiv_realV_complex

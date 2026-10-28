module

public import NativeExactCKMAllFrames
public import NativeOriginalGIdempotencyDifferential

/-!
# Original G idempotency, within-frame and sum values from actual CKM frames

The accepted nativePoint_all_frames theorem supplies the actual frame fields;
no frame or residual-zero premise is added. The existing original point
packing, real coordinate product dictionary and gRow evaluation identify all
1053idempotency,1053within-frame and351sum scalar rows at pointCoordinates.
The original h=1/2,t=1/3, row labels, framePointIndex and unit subtraction
remain unchanged. Cross rows and final all-G dispatch are separate owners.

First-party accepted theorem composition; no replacement product, point or
residual. Native/mathlib Apache-2.0 pins remain in imported owners:
compact-albert-recognition40d3b344180d9ddb78aaa2876873377c1e631515;
mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55. No third-party proof copied.
Thanks to their contributors and the original CKM construction.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke,1676. No release license assigned.
-/

@[expose] public section
noncomputable section
namespace QuadraticCertificate.ExactCKMFrameValueRows
open scoped BigOperators
open NativePolynomial CompactAlbert
open NativePolynomial.ConfigurationResiduals
open NativePolynomial.ConfigurationResiduals.MixedCoefficients
open NativePolynomial.ConfigurationResiduals.Evaluation
open NativePolynomial.CoordinateMaps ConfigurationResidualIndices
open ExactCKMConfiguration

private theorem nativePoint_idempotent (i : Fin 39) :
    Glennie.jordan (nativePoint i) (nativePoint i) = nativePoint i := by
  let f : Fin 13 := ⟨i.val / 3, by have hi := i.isLt; omega⟩
  let a : Fin 3 := ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩
  have hi : framePointIndex f a = i := by
    apply Fin.ext
    dsimp only [framePointIndex, f, a]
    omega
  rw [← hi]
  exact (ExactCKMAllFrames.nativePoint_all_frames f).idempotent a

private theorem upperCoordinates_zero (k : Fin 27) :
    upperCoordinates (0 : Glennie.Albert) k = 0 := by
  change upperCoordinateEquiv (0 : Glennie.Albert) k = 0
  rw [map_zero]
  rfl

/-- Static original coordinate dictionary for the actual native unit. -/
theorem upperCoordinates_unit_eq_coordinateUnit :
    upperCoordinates (1 : Glennie.Albert) = (coordinateUnit : Fin 27 → ℝ) := by
  funext k
  fin_cases k <;> rfl

/-- All1053original gId scalar values, with original point and coordinate labels. -/
theorem gId_value_zero (i : Fin 39) (k : Fin 27) :
    valueRow (1/2 : ℝ) (1/3 : ℝ) pointCoordinates (gNumber (gId i k)) = 0 := by
  simp only [valueRow, Equiv.symm_apply_apply, valueResidual, gId]
  rw [coordinateProduct_real_eq_native_coordinates (1/2 : ℝ) (by norm_num)]
  simp only [pointValues_pointCoordinates, fromUpperCoordinates_upperCoordinates]
  rw [nativePoint_idempotent, sub_self]

/-- All1053original gWithin scalar values, with actual withinPair orientation. -/
theorem gWithin_value_zero (f : Fin 13) (s : Fin 3) (k : Fin 27) :
    valueRow (1/2 : ℝ) (1/3 : ℝ) pointCoordinates
      (gNumber (gWithin f s k)) = 0 := by
  have horth : Glennie.jordan
      (nativePoint (framePointIndex f (withinPair s).val.1))
      (nativePoint (framePointIndex f (withinPair s).val.2)) = 0 :=
    (ExactCKMAllFrames.nativePoint_all_frames f).orthogonal _ _
      (ne_of_lt (withinPair s).property)
  simp only [valueRow, Equiv.symm_apply_apply, valueResidual, gWithin]
  rw [coordinateProduct_real_eq_native_coordinates (1/2 : ℝ) (by norm_num)]
  simp only [pointValues_pointCoordinates, fromUpperCoordinates_upperCoordinates]
  rw [horth]
  exact upperCoordinates_zero k

/-- All351original gSum scalar values, retaining the original unit subtraction. -/
theorem gSum_value_zero (f : Fin 13) (k : Fin 27) :
    valueRow (1/2 : ℝ) (1/3 : ℝ) pointCoordinates (gNumber (gSum f k)) = 0 := by
  have hsum := (ExactCKMAllFrames.nativePoint_all_frames f).sum_unit
  have hc := congrArg (fun x : Glennie.Albert => upperCoordinates x k) hsum
  simp only [upperCoordinates_add, Pi.add_apply, upperCoordinates_unit_eq_coordinateUnit] at hc
  simp only [valueRow, Equiv.symm_apply_apply, valueResidual, gSum,
    pointValues_pointCoordinates, Fin.sum_univ_three]
  exact sub_eq_zero.mpr hc

/-- Literal original gId polynomials evaluate to zero at the same real point. -/
theorem gId_eval_zero (i : Fin 39) (k : Fin 27) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gId i k))) = 0 := by
  rw [gRow_eval]
  exact gId_value_zero i k

/-- Literal original gWithin polynomials evaluate to zero at the same real point. -/
theorem gWithin_eval_zero (f : Fin 13) (s : Fin 3) (k : Fin 27) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gWithin f s k))) = 0 := by
  rw [gRow_eval]
  exact gWithin_value_zero f s k

/-- Literal original gSum polynomials evaluate to zero at the same real point. -/
theorem gSum_eval_zero (f : Fin 13) (k : Fin 27) :
    MvPolynomial.eval pointCoordinates
      (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℝ) (1/3 : ℝ)
        (gNumber (gSum f k))) = 0 := by
  rw [gRow_eval]
  exact gSum_value_zero f k

end QuadraticCertificate.ExactCKMFrameValueRows

#print axioms QuadraticCertificate.ExactCKMFrameValueRows.upperCoordinates_unit_eq_coordinateUnit
#print axioms QuadraticCertificate.ExactCKMFrameValueRows.gId_value_zero
#print axioms QuadraticCertificate.ExactCKMFrameValueRows.gWithin_value_zero
#print axioms QuadraticCertificate.ExactCKMFrameValueRows.gSum_value_zero
#print axioms QuadraticCertificate.ExactCKMFrameValueRows.gId_eval_zero
#print axioms QuadraticCertificate.ExactCKMFrameValueRows.gWithin_eval_zero
#print axioms QuadraticCertificate.ExactCKMFrameValueRows.gSum_eval_zero

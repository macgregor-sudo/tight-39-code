module

public import NativeConfigurationEvaluation
public import LiteralNativeQuartetBinder

@[expose] public section

/-!
One actual native39-point definition at the rational phases from MASTER6.3
and exact_point_binder.py, using the existing native outer product, basis,
complex plane and cube root with positive imaginary part. Point/outcome labels are fixed
before coordinate packing; no orthogonality search, modular lift, Tits gauge
or normalized two-phase monomial family defines this point.

The first12 points reuse the existing coordinate/phase anchor definitions.
The remaining27 are explicit native vv*/3 field formulas with complex
coefficients multiplying j,ell,n on the LEFT, n=j*ell. A later uniform
unit-ray proof must identify the fixed denominator3 with the norm-square
denominator; no global solution/normalization theorem is assumed here.

The only numerical sample below is complete point21, the first A/B point.
Its native e7 sign is retained. No all-row vanishing follows from the sample.
First-party point/index/coordinate composition, with no novelty claim.
Native/Apache-2.0 provenance remains in THIRD_PARTY_NOTICES.md#native-albert-code,
upstream https://github.com/macgregor-sudo/compact-albert-recognition at
40d3b344180d9ddb78aaa2876873377c1e631515. Lean4.35.0-rc2;
mathlib065356127b1dc0016f66b7283ce0ce2c4055aa55.
Thanks to the original family, native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke,1676. No release license is selected here.
-/

noncomputable section

namespace QuadraticCertificate.ExactCKMConfiguration

open NativePolynomial CompactAlbert
open NativePolynomial.ConfigurationResiduals
open NativePolynomial.ConfigurationResiduals.MixedCoefficients
open UnitaryErrorBases.ComplexQuartet UnitaryErrorBases.ThreeCycleFourier

/-- The four EXACT rational unit-circle phases, in original A,B,C,D order. -/
def exactPhases : Fin 4 → ℂ :=
  ![(3 + 4 * Complex.I) / 5, (5 + 12 * Complex.I) / 13,
    (15 + 8 * Complex.I) / 17, (21 + 20 * Complex.I) / 29]

/-- Native labelled family, with s naming a frame and t its outcome. -/
def nativeFamilyPoint (q : Fin 4) (s t : PhaseIndex) : Glennie.Albert :=
  if q = 0 then literalNativePhasePoint s t
  else if q = 1 then
    nativeOuterProductThird
      (Glennie.octMul (complexOctonion (character t)) (nativeOctonionBasis 2))
      (Glennie.octMul (complexOctonion (character (s + t))) (nativeOctonionBasis 4))
  else if q = 2 then
    nativeOuterProductThird
      (Glennie.octMul (complexOctonion (exactPhases 0 * character t))
        (nativeOctonionBasis 4))
      (Glennie.octMul (complexOctonion (exactPhases 1 * character (s + t)))
        (nativeOctonionBasis 6))
  else
    nativeOuterProductThird
      (Glennie.octMul (complexOctonion (exactPhases 2 * character t))
        (nativeOctonionBasis 6))
      (Glennie.octMul (complexOctonion (exactPhases 3 * character (s + t)))
        (nativeOctonionBasis 2))

/-- Original frame-grouped point order: coordinate0..2, then3+9q+3s+t. -/
def nativePoint (i : Fin 39) : Glennie.Albert :=
  if hi : i.val < 3 then literalNativeCoordinatePoint ⟨i.val, hi⟩
  else
    let q : Fin 4 := ⟨(i.val - 3) / 9, by have hi39 := i.isLt; omega⟩
    let s : PhaseIndex := (((i.val - 3) % 9) / 3 : ℕ)
    let t : PhaseIndex := ((i.val - 3) % 3 : ℕ)
    nativeFamilyPoint q s t

/-- The SAME native upper coordinates, packed in the original1053 variables. -/
def pointCoordinates (v : Fin 1053) : ℝ :=
  let ic := (finProdFinEquiv : Fin 39 × Fin 27 ≃ Fin 1053).symm v
  upperCoordinates (nativePoint ic.1) ic.2

theorem pointValues_pointCoordinates (i : Fin 39) :
    pointValues pointCoordinates i = upperCoordinates (nativePoint i) := by
  funext c
  have hIndex : variableIndex i c =
      (finProdFinEquiv : Fin 39 × Fin 27 ≃ Fin 1053) (i, c) := by
    apply Fin.ext
    change 27 * i.val + c.val = c.val + 27 * i.val
    exact Nat.add_comm _ _
  simp only [pointValues, pointCoordinates, hIndex, Equiv.symm_apply_apply]

/-- Complete original point21, including the sign from left multiplication by n. -/
theorem nativePoint21_readout :
    nativePoint (21 : Fin 39) =
      (⟨1/3, 1/3, 1/3,
        (0, ⟨-1/5, -4/15, 0, 0⟩),
        (0, ⟨0, 0, -5/39, 4/13⟩),
        (⟨0, 0, 11/65, 56/195⟩, 0)⟩ : Glennie.Albert) := by
  change nativeFamilyPoint (2 : Fin 4) 0 0 = _
  apply Glennie.Albert.extExplicit
  all_goals first | (apply Prod.ext <;> apply Quaternion.ext) | skip
  all_goals
    norm_num [nativeFamilyPoint, exactPhases, nativeOuterProductThird,
      complexOctonion, character, nativeOctonionBasis, firstUpperCoordinateIndex,
      nativeCoordinateBasis, fromUpperCoordinates, Pi.single_apply,
      Glennie.octNormSq, Quaternion.normSq_def', Glennie.octMul, Glennie.octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
      Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.normSq_apply, smul_eq_mul]

/-- The native upper02/e7 coordinate is POSITIVE4/13 at this labelled point. -/
theorem point21_native_e7_value :
    pointCoordinates (variableIndex (21 : Fin 39) (18 : Fin 27)) = (4/13 : ℝ) := by
  change pointValues pointCoordinates (21 : Fin 39) (18 : Fin 27) = _
  rw [pointValues_pointCoordinates, nativePoint21_readout]
  rfl

/-- Reversing that SAME native coordinate's sign is rejected. -/
theorem point21_native_e7_changed_sign :
    pointCoordinates (variableIndex (21 : Fin 39) (18 : Fin 27)) ≠ (-4/13 : ℝ) := by
  rw [point21_native_e7_value]
  norm_num

end QuadraticCertificate.ExactCKMConfiguration

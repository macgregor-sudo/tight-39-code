module

public import ThreeCycleNormalizedAnalytic
public import SpecialUnitaryCurveTangent
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.Deriv.Pi

@[expose] public section

/-!
Differential transport for the same actual normalized native construction.
The matrix and phase curves satisfy the original subtype equations at every
time. Their coordinate derivatives are arbitrary; tangent constraints and
zero-kernel consequences come from the frozen actual-SU3 curve owner.
All original labels and independent fixed central orientations are retained.
No quotient charts, global Albert topology or manifold immersion is asserted.

First-party composition of named native, analytic and tangent APIs; no upstream
proof or coordinate formula is copied. Thanks to their contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, 1676. https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
open scoped Matrix.Norms.Elementwise

namespace CompactAlbert.NativeCentralArrayTopology

open NativePolynomial

/-- The existing outcome-zero recovery map is differentiable in all native coordinates. -/
theorem differentiable_recoverCentralArray : Differentiable ℝ recoverCentralArray := by
  let encode : (Fin 27 → ℝ) →L[ℝ] TitsCoordinates :=
    (compactTitsCoordinateEquiv.toLinearMap.comp
      upperCoordinateEquiv.symm.toLinearMap).toContinuousLinearMap
  intro p
  change DifferentiableAt ℝ
    (fun q : Fin 9 → Fin 3 → Fin 27 → ℝ => fun r => (3 : ℂ) • (encode (q r 0)).2.2) p
  apply differentiableAt_pi.mpr
  intro r
  have he : DifferentiableAt ℝ
      (fun q : Fin 9 → Fin 3 → Fin 27 → ℝ => encode (q r 0)) p :=
    encode.differentiableAt.comp p
      ((ContinuousLinearMap.proj (R := ℝ) 0).differentiableAt.comp p
        (ContinuousLinearMap.proj (R := ℝ) r).differentiableAt)
  exact he.snd.snd.const_smul (3 : ℂ)

end CompactAlbert.NativeCentralArrayTopology

namespace CompactAlbert

open UnitaryErrorBases UnitaryErrorBases.ThreeCycleNormalized
open NativeCentralArrayTopology

/-- The exact original family velocity, with the accepted label and matrix reindexing. -/
theorem nativeThreeCycleArray_hasDerivAt_of_specialUnitaryCurve
    (Q : ℝ → {M : Mat // IsSpecialUnitary M}) (d : ℝ → PhaseTriple)
    (V : Mat) (v : Index → ℂ) (t : ℝ)
    (hQ : HasDerivAt (fun s => (Q s).val) V t)
    (hd : HasDerivAt (fun s => (d s).val) v t) :
    HasDerivAt (fun s => nativeThreeCycleArray (Q s).val (d s))
      (nativeArrayOfChallengeFamily
        (normalizedVelocity (Q t).val (d t) ((Q t).val.conjTranspose * V) v)) t := by
  have h := normalizedFamily_hasDerivAt_of_specialUnitaryCurve Q d V v t hQ hd
  apply hasDerivAt_pi.mpr
  intro r
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp
    (hasDerivAt_pi.mp h (challengeLabelEquiv.symm r))
      (challengeMatrixIndexEquiv i)) (challengeMatrixIndexEquiv j)

/-- The derivative in all native upper coordinates, for any independent fixed
forward/reverse pattern, is the derivative of the existing analytic constructor
applied to the exact reindexed normalized velocity. -/
theorem nativeCentralArray_hasDerivAt_of_specialUnitaryCurve
    (reverse : Fin 9 → Bool)
    (Q : ℝ → {M : Mat // IsSpecialUnitary M}) (d : ℝ → PhaseTriple)
    (V : Mat) (v : Index → ℂ) (t : ℝ)
    (hQ : HasDerivAt (fun s => (Q s).val) V t)
    (hd : HasDerivAt (fun s => (d s).val) v t) :
    HasDerivAt (fun s => centralArrayCoordinates reverse (nativeThreeCycleArray (Q s).val (d s)))
      ((fderiv ℝ (centralArrayCoordinates reverse) (nativeThreeCycleArray (Q t).val (d t)))
        (nativeArrayOfChallengeFamily
          (normalizedVelocity (Q t).val (d t) ((Q t).val.conjTranspose * V) v))) t :=
  ((analyticOnNhd_centralArrayCoordinates reverse _ (Set.mem_univ _)).differentiableAt.hasFDerivAt).comp_hasDerivAt
    t (nativeThreeCycleArray_hasDerivAt_of_specialUnitaryCurve Q d V v t hQ hd)

/-- Zero actual native coordinate derivative forces both genuine parameter
velocities to vanish, without a supplied tangent or injectivity premise. -/
theorem nativeCentralArray_zero_derivative_of_specialUnitaryCurve
    (reverse : Fin 9 → Bool)
    (Q : ℝ → {M : Mat // IsSpecialUnitary M}) (d : ℝ → PhaseTriple)
    (V : Mat) (v : Index → ℂ) (t : ℝ)
    (hQ : HasDerivAt (fun s => (Q s).val) V t)
    (hd : HasDerivAt (fun s => (d s).val) v t)
    (hzero : HasDerivAt
      (fun s => centralArrayCoordinates reverse (nativeThreeCycleArray (Q s).val (d s))) 0 t) :
    V = 0 ∧ v = 0 := by
  have hr := (differentiable_recoverCentralArray _).hasFDerivAt.comp_hasDerivAt t hzero
  have heq : (recoverCentralArray ∘
      (fun s => centralArrayCoordinates reverse (nativeThreeCycleArray (Q s).val (d s)))) =
      (fun s => nativeThreeCycleArray (Q s).val (d s)) :=
    funext fun s => recoverCentralArray_leftInverse reverse _
  rw [heq] at hr
  have hz := (fderiv ℝ recoverCentralArray
    (centralArrayCoordinates reverse (nativeThreeCycleArray (Q t).val (d t)))).map_zero
  have hr0 : HasDerivAt (fun s => nativeThreeCycleArray (Q s).val (d s)) 0 t :=
    hr.congr_deriv hz
  apply normalizedFamily_zero_derivative_of_specialUnitaryCurve Q d V v t hQ hd
  apply hasDerivAt_pi.mpr
  intro p
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h := hasDerivAt_pi.mp (hasDerivAt_pi.mp
    (hasDerivAt_pi.mp hr0 (challengeLabelEquiv p))
      (challengeMatrixIndexEquiv.symm i)) (challengeMatrixIndexEquiv.symm j)
  simpa only [nativeThreeCycleArray_apply, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply, Pi.zero_apply, Matrix.zero_apply] using h

/-- Exact forward representative binding via the frozen ambient extension equality. -/
theorem nativeNormalizedFamilyExtension_hasDerivAt_of_specialUnitaryCurve
    (Q : ℝ → {M : Mat // IsSpecialUnitary M}) (d : ℝ → PhaseTriple)
    (V : Mat) (v : Index → ℂ) (t : ℝ)
    (hQ : HasDerivAt (fun s => (Q s).val) V t)
    (hd : HasDerivAt (fun s => (d s).val) v t) :
    HasDerivAt (fun s => nativeNormalizedFamilyExtension ((Q s).val, (d s).val))
      ((fderiv ℝ (centralArrayCoordinates (fun _ => false))
        (nativeThreeCycleArray (Q t).val (d t)))
        (nativeArrayOfChallengeFamily
          (normalizedVelocity (Q t).val (d t) ((Q t).val.conjTranspose * V) v))) t := by
  simpa only [nativeNormalizedFamilyExtension_eq] using
    nativeCentralArray_hasDerivAt_of_specialUnitaryCurve (fun _ => false) Q d V v t hQ hd

/-- The same zero-kernel result for the exact frozen forward native extension. -/
theorem nativeNormalizedFamilyExtension_zero_derivative_of_specialUnitaryCurve
    (Q : ℝ → {M : Mat // IsSpecialUnitary M}) (d : ℝ → PhaseTriple)
    (V : Mat) (v : Index → ℂ) (t : ℝ)
    (hQ : HasDerivAt (fun s => (Q s).val) V t)
    (hd : HasDerivAt (fun s => (d s).val) v t)
    (hzero : HasDerivAt
      (fun s => nativeNormalizedFamilyExtension ((Q s).val, (d s).val)) 0 t) :
    V = 0 ∧ v = 0 := by
  apply nativeCentralArray_zero_derivative_of_specialUnitaryCurve
    (fun _ => false) Q d V v t hQ hd
  simpa only [nativeNormalizedFamilyExtension_eq] using hzero

end CompactAlbert

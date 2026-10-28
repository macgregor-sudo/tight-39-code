module
public import SpecialUnitaryImplicitChart
public import SpecialUnitaryTranslatedConstraints
public import NativeNormalizedFamilyDifferential
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-!
# Actual native normalized family in ten graph/phase directions

This differentiates the same implicit identity graph and
translates it by an actual standard SU3 basepoint. Two explicit unit-circle
exponentials feed the existing phaseOfCircles constructor, retaining all unit
and product-one constraints. The output is exactly the frozen native ambient
extension; outcome-zero recovery returns the original labelled family.
No manifold atlas, quotient chart, tangent constraint, rank or injectivity is
assumed. New conclusions are local analytic representative and differential
statements, not a quotient-manifold immersion or full A2.

First-party composition of frozen IFT, translation, phase, native recovery and
normalized-velocity owners. Pinned mathlib public derivative/analytic APIs are
imported at 065356127b1dc0016f66b7283ce0ce2c4055aa55. No upstream proof body is
copied; imported owners retain their provenance. Thanks to the contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, 1676. https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/
noncomputable section
open scoped Matrix.Norms.Elementwise Topology ContDiff
open Filter

namespace UnitaryErrorBases.SpecialUnitaryConstraints

theorem specialUnitaryNormalGraph_hasFDerivAt_zero :
    HasFDerivAt specialUnitaryNormalGraph (0 : ConstraintTangent →L[ℝ] ConstraintRange) 0 := by
  have h := (contDiffAt_coordinateResidual_zero.hasStrictFDerivAt_implicitFunction
    (by simp) coordinateResidual_normal_invertible).hasFDerivAt
  change HasFDerivAt specialUnitaryNormalGraph _ 0 at h
  have he : -(fderiv ℝ coordinateResidual 0 ∘L
      ContinuousLinearMap.inr ℝ ConstraintTangent ConstraintRange).inverse ∘L
      (fderiv ℝ coordinateResidual 0 ∘L
        ContinuousLinearMap.inl ℝ ConstraintTangent ConstraintRange) = 0 := by
    rw [coordinateResidual_hasFDerivAt_zero.fderiv]
    have hz : ContinuousLinearMap.snd ℝ ConstraintTangent ConstraintRange ∘L
        ContinuousLinearMap.inl ℝ ConstraintTangent ConstraintRange = 0 := rfl
    rw [hz, ContinuousLinearMap.comp_zero]
    apply ContinuousLinearMap.ext
    intro k
    apply Subtype.ext
    change -(0 : Mat × ℝ) = 0
    exact neg_zero
  exact he ▸ h

/-- The graph derivative is the literal inclusion of the actual tangent kernel. -/
theorem specialUnitaryIdentityParam_hasFDerivAt_zero :
    HasFDerivAt specialUnitaryIdentityParam ConstraintTangent.subtypeL 0 := by
  have hp := (hasFDerivAt_id (𝕜 := ℝ) (0 : ConstraintTangent)).prodMk
    specialUnitaryNormalGraph_hasFDerivAt_zero
  have h := (tangentNormalCoordinates.symm.toContinuousLinearMap.hasFDerivAt.comp 0 hp).const_add 1
  change HasFDerivAt specialUnitaryIdentityParam _ 0 at h
  have he : tangentNormalCoordinates.symm.toContinuousLinearMap ∘L
      (ContinuousLinearMap.id ℝ ConstraintTangent).prod 0 = ConstraintTangent.subtypeL := by
    apply ContinuousLinearMap.ext
    intro k
    change tangentNormalCoordinates.symm (k, 0) = k.val
    rw [tangentNormalCoordinates_symm_apply]
    simp [constraintNormal]
  exact he ▸ h

end UnitaryErrorBases.SpecialUnitaryConstraints

namespace UnitaryErrorBases.ThreeCycleNormalized

/-- Unit-circle exponentials use the existing phase constructor, including inverse-product entry. -/
def phaseExpParam (d₀ : PhaseTriple) (x : ℝ × ℝ) : PhaseTriple :=
  phaseOfCircles (phaseCircle d₀ 0 * Circle.exp x.1,
    phaseCircle d₀ 1 * Circle.exp x.2)

@[simp] theorem phaseExpParam_zero (d₀ : PhaseTriple) : phaseExpParam d₀ 0 = d₀ := by
  simp only [phaseExpParam, Prod.fst_zero, Prod.snd_zero, Circle.exp_zero, mul_one]
  exact phaseTripleHomeomorph.symm_apply_apply d₀

private def phaseExpValue (a : Circle) (t : ℝ) : ℂ :=
  (a : ℂ) * Complex.exp ((t : ℂ) * Complex.I)

private theorem phaseExpValue_ne_zero (a : Circle) (t : ℝ) : phaseExpValue a t ≠ 0 :=
  mul_ne_zero (Circle.coe_ne_zero a) (Complex.exp_ne_zero _)

private theorem analyticAt_phaseExpValue (a : Circle) (t : ℝ) :
    AnalyticAt ℝ (phaseExpValue a) t := by
  have h : AnalyticAt ℝ (fun s : ℝ => (s : ℂ) * Complex.I) t :=
    (Complex.ofRealCLM.analyticAt t).mul analyticAt_const
  exact analyticAt_const.mul (analyticAt_cexp.restrictScalars.comp h)

private theorem phaseExpValue_hasDerivAt_zero (a : Circle) :
    HasDerivAt (phaseExpValue a) ((a : ℂ) * Complex.I) 0 := by
  have ht : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 0 := by
    simpa using! Complex.ofRealCLM.hasFDerivAt.hasDerivAt
  simpa [phaseExpValue] using! (ht.mul_const Complex.I).cexp.const_mul (a : ℂ)

/-- Real analytic in both actual phase directions; no local-chart assertion is assumed. -/
theorem analyticAt_phaseExpParam_val (d₀ : PhaseTriple) (x : ℝ × ℝ) :
    AnalyticAt ℝ (fun y => (phaseExpParam d₀ y).val) x := by
  have ha := (analyticAt_phaseExpValue (phaseCircle d₀ 0) x.1).comp
    (analyticAt_fst (𝕜 := ℝ) (p := x))
  have hb := (analyticAt_phaseExpValue (phaseCircle d₀ 1) x.2).comp
    (analyticAt_snd (𝕜 := ℝ) (p := x))
  apply AnalyticAt.pi
  intro j
  change AnalyticAt ℝ (fun y : ℝ × ℝ =>
    if j = 0 then phaseExpValue (phaseCircle d₀ 0) y.1
    else if j = 1 then phaseExpValue (phaseCircle d₀ 1) y.2
    else (phaseExpValue (phaseCircle d₀ 0) y.1 *
      phaseExpValue (phaseCircle d₀ 1) y.2)⁻¹) x
  split_ifs
  · exact ha
  · exact hb
  · exact (ha.mul hb).inv (mul_ne_zero (phaseExpValue_ne_zero _ _) (phaseExpValue_ne_zero _ _))

theorem phaseExpParam_fderiv_first_two (d₀ : PhaseTriple) (w : ℝ × ℝ) :
    (fderiv ℝ (fun x => (phaseExpParam d₀ x).val) 0 w) 0 =
      w.1 • (d₀.val 0 * Complex.I) ∧
    (fderiv ℝ (fun x => (phaseExpParam d₀ x).val) 0 w) 1 =
      w.2 • (d₀.val 1 * Complex.I) := by
  have hf := (analyticAt_phaseExpParam_val d₀ 0).differentiableAt.hasFDerivAt
  constructor
  · have hp := (ContinuousLinearMap.proj (R := ℝ) (0 : Index)).hasFDerivAt.comp 0 hf
    have he := (phaseExpValue_hasDerivAt_zero (phaseCircle d₀ 0)).hasFDerivAt.comp 0
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
    change HasFDerivAt (fun x : ℝ × ℝ => phaseExpValue (phaseCircle d₀ 0) x.1) _ 0 at hp
    exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℂ => L w) (hp.unique he)
  · have hp := (ContinuousLinearMap.proj (R := ℝ) (1 : Index)).hasFDerivAt.comp 0 hf
    have he := (phaseExpValue_hasDerivAt_zero (phaseCircle d₀ 1)).hasFDerivAt.comp 0
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
    change HasFDerivAt (fun x : ℝ × ℝ => phaseExpValue (phaseCircle d₀ 1) x.2) _ 0 at hp
    exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℂ => L w) (hp.unique he)

/-- The two real phase velocities are recovered from the first two nonzero unit entries. -/
theorem phaseExpParam_fderiv_injective (d₀ : PhaseTriple) :
    Function.Injective (fderiv ℝ (fun x => (phaseExpParam d₀ x).val) 0) := by
  apply (injective_iff_map_eq_zero (fderiv ℝ (fun x => (phaseExpParam d₀ x).val) 0)).mpr
  intro w hw
  obtain ⟨h0, h1⟩ := phaseExpParam_fderiv_first_two d₀ w
  rw [hw, Pi.zero_apply] at h0 h1
  have hz0 : w.1 = 0 := (smul_eq_zero.mp h0.symm).resolve_right
    (mul_ne_zero (Circle.coe_ne_zero (phaseCircle d₀ 0)) Complex.I_ne_zero)
  have hz1 : w.2 = 0 := (smul_eq_zero.mp h1.symm).resolve_right
    (mul_ne_zero (Circle.coe_ne_zero (phaseCircle d₀ 1)) Complex.I_ne_zero)
  exact Prod.ext hz0 hz1

end UnitaryErrorBases.ThreeCycleNormalized

namespace UnitaryErrorBases.ThreeCycleNormalized
open SpecialUnitaryConstraints

/-- Translate the same proved identity graph by the actual standard SU3 basepoint. -/
def specialUnitaryGraphParam (Q₀ : StandardSpecialUnitary) (k : ConstraintTangent) : Mat :=
  (specialUnitaryLeftTranslation Q₀).symm (specialUnitaryIdentityParam k)

@[simp] theorem specialUnitaryGraphParam_zero (Q₀ : StandardSpecialUnitary) :
    specialUnitaryGraphParam Q₀ 0 = Q₀.val := by
  simp only [specialUnitaryGraphParam, specialUnitaryIdentityParam_zero,
    specialUnitaryLeftTranslation_symm_one]

theorem analyticAt_specialUnitaryGraphParam (Q₀ : StandardSpecialUnitary) :
    AnalyticAt ℝ (specialUnitaryGraphParam Q₀) 0 :=
  ((specialUnitaryLeftTranslation Q₀).symm.toContinuousLinearMap.analyticAt _).comp
    analyticAt_specialUnitaryIdentityParam

theorem specialUnitaryGraphParam_hasFDerivAt_zero (Q₀ : StandardSpecialUnitary) :
    HasFDerivAt (specialUnitaryGraphParam Q₀)
      ((specialUnitaryLeftTranslation Q₀).symm.toContinuousLinearMap ∘L ConstraintTangent.subtypeL) 0 :=
  (specialUnitaryLeftTranslation Q₀).symm.toContinuousLinearMap.hasFDerivAt.comp 0
    specialUnitaryIdentityParam_hasFDerivAt_zero

theorem eventually_specialUnitaryGraphParam_mem (Q₀ : StandardSpecialUnitary) :
    ∀ᶠ k : ConstraintTangent in 𝓝 0,
      specialUnitaryGraphParam Q₀ k ∈ Matrix.specialUnitaryGroup Index ℂ := by
  filter_upwards [eventually_specialUnitaryIdentityParam_mem] with k hk
  exact (specialUnitaryLeftTranslation_symm_mem_iff Q₀ _).mpr hk

end UnitaryErrorBases.ThreeCycleNormalized

namespace CompactAlbert
open UnitaryErrorBases UnitaryErrorBases.ThreeCycleNormalized
open UnitaryErrorBases.SpecialUnitaryConstraints NativeCentralArrayTopology

abbrev NativeGraphParameters := ConstraintTangent × (ℝ × ℝ)

/-- The unchanged native representative extension along the actual matrix graph and phase map. -/
def nativeNormalizedGraphFamily (Q₀ : StandardSpecialUnitary) (d₀ : PhaseTriple)
    (x : NativeGraphParameters) : Fin 9 → Fin 3 → Fin 27 → ℝ :=
  nativeNormalizedFamilyExtension
    (specialUnitaryGraphParam Q₀ x.1, (phaseExpParam d₀ x.2).val)

theorem nativeNormalizedGraphFamily_eq (Q₀ : StandardSpecialUnitary) (d₀ : PhaseTriple)
    (x : NativeGraphParameters) :
    nativeNormalizedGraphFamily Q₀ d₀ x = centralArrayCoordinates (fun _ => false)
      (nativeThreeCycleArray (specialUnitaryGraphParam Q₀ x.1) (phaseExpParam d₀ x.2)) := rfl

@[simp] theorem nativeNormalizedGraphFamily_zero (Q₀ : StandardSpecialUnitary) (d₀ : PhaseTriple) :
    nativeNormalizedGraphFamily Q₀ d₀ 0 =
      centralArrayCoordinates (fun _ => false) (nativeThreeCycleArray Q₀.val d₀) := by
  simp only [nativeNormalizedGraphFamily_eq, Prod.fst_zero, Prod.snd_zero,
    specialUnitaryGraphParam_zero, phaseExpParam_zero]

theorem analyticAt_nativeNormalizedGraphFamily (Q₀ : StandardSpecialUnitary) (d₀ : PhaseTriple) :
    AnalyticAt ℝ (nativeNormalizedGraphFamily Q₀ d₀) 0 := by
  have hQ : AnalyticAt ℝ (fun x : NativeGraphParameters => specialUnitaryGraphParam Q₀ x.1) 0 :=
    (analyticAt_specialUnitaryGraphParam Q₀).comp_of_eq analyticAt_fst rfl
  have hd : AnalyticAt ℝ (fun x : NativeGraphParameters => (phaseExpParam d₀ x.2).val) 0 :=
    (analyticAt_phaseExpParam_val d₀ 0).comp_of_eq analyticAt_snd rfl
  exact (analyticOnNhd_nativeNormalizedFamilyExtension _ (Set.mem_univ _)).comp (hQ.prod hd)

theorem nativeNormalizedGraphFamily_hasFDerivAt (Q₀ : StandardSpecialUnitary) (d₀ : PhaseTriple) :
    HasFDerivAt (nativeNormalizedGraphFamily Q₀ d₀)
      (fderiv ℝ (nativeNormalizedGraphFamily Q₀ d₀) 0) 0 :=
  (analyticAt_nativeNormalizedGraphFamily Q₀ d₀).differentiableAt.hasFDerivAt

/-- All ten actual graph/phase directions are detected by the original native coordinates. -/
theorem nativeNormalizedGraphFamily_fderiv_injective
    (Q₀ : StandardSpecialUnitary) (d₀ : PhaseTriple) :
    Function.Injective (fderiv ℝ (nativeNormalizedGraphFamily Q₀ d₀) 0) := by
  apply (injective_iff_map_eq_zero (fderiv ℝ (nativeNormalizedGraphFamily Q₀ d₀) 0)).mpr
  intro x hx
  have hl : HasDerivAt (fun t : ℝ => t • x) x 0 := by
    simpa using! (hasDerivAt_id (0 : ℝ)).smul_const x
  have hn0 : HasFDerivAt (nativeNormalizedGraphFamily Q₀ d₀)
      (fderiv ℝ (nativeNormalizedGraphFamily Q₀ d₀) 0) ((0 : ℝ) • x) := by
    simpa only [zero_smul] using! nativeNormalizedGraphFamily_hasFDerivAt Q₀ d₀
  have hn := hn0.comp_hasDerivAt 0 hl
  have hnz := hn.congr_deriv hx
  have hr := (differentiable_recoverCentralArray _).hasFDerivAt.comp_hasDerivAt 0 hnz
  have heq : (recoverCentralArray ∘ nativeNormalizedGraphFamily Q₀ d₀ ∘
      (fun t : ℝ => t • x)) =
      (fun t => nativeThreeCycleArray (specialUnitaryGraphParam Q₀ (t • x.1))
        (phaseExpParam d₀ (t • x.2))) := by
    funext t
    exact recoverCentralArray_leftInverse (fun _ => false) _
  rw [heq] at hr
  have hr0 : HasDerivAt (fun t : ℝ => nativeThreeCycleArray
      (specialUnitaryGraphParam Q₀ (t • x.1)) (phaseExpParam d₀ (t • x.2))) 0 0 :=
    hr.congr_deriv (map_zero _)
  have hfamily : HasDerivAt (fun t : ℝ => normalizedFamily
      (specialUnitaryGraphParam Q₀ (t • x.1)) (phaseExpParam d₀ (t • x.2))) 0 0 := by
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
  have hlk : HasDerivAt (fun t : ℝ => t • x.1) x.1 0 := by
    simpa using! (hasDerivAt_id (0 : ℝ)).smul_const x.1
  have hlw : HasDerivAt (fun t : ℝ => t • x.2) x.2 0 := by
    simpa using! (hasDerivAt_id (0 : ℝ)).smul_const x.2
  have hQ0 : HasFDerivAt (specialUnitaryGraphParam Q₀)
      ((specialUnitaryLeftTranslation Q₀).symm.toContinuousLinearMap ∘L ConstraintTangent.subtypeL)
      ((0 : ℝ) • x.1) := by
    simpa only [zero_smul] using! specialUnitaryGraphParam_hasFDerivAt_zero Q₀
  have hQ := hQ0.comp_hasDerivAt 0 hlk
  have hd0 : HasFDerivAt (fun y => (phaseExpParam d₀ y).val)
      (fderiv ℝ (fun y => (phaseExpParam d₀ y).val) 0) ((0 : ℝ) • x.2) := by
    simpa only [zero_smul] using! (analyticAt_phaseExpParam_val d₀ 0).differentiableAt.hasFDerivAt
  have hd := hd0.comp_hasDerivAt 0 hlw
  obtain ⟨hskew, htrace⟩ := (constraintDifferential_kernel x.1.val).mp x.1.property
  have hSU : IsSpecialUnitary (specialUnitaryGraphParam Q₀ ((0 : ℝ) • x.1)) := by
    simpa only [zero_smul, specialUnitaryGraphParam_zero] using
      (isSpecialUnitary_iff_mem_standard Q₀.val).mpr Q₀.property
  have hQ' : HasDerivAt (fun t : ℝ => specialUnitaryGraphParam Q₀ (t • x.1))
      (specialUnitaryGraphParam Q₀ ((0 : ℝ) • x.1) * x.1.val) 0 := by
    simpa only [zero_smul, specialUnitaryGraphParam_zero] using! hQ
  obtain ⟨hk, hw⟩ := normalizedFamily_zero_derivative_recovers_velocity
    (fun t => specialUnitaryGraphParam Q₀ (t • x.1))
    (fun t => phaseExpParam d₀ (t • x.2)) x.1.val
    (fderiv ℝ (fun y => (phaseExpParam d₀ y).val) 0 x.2) 0 hSU hQ' hd hskew htrace hfamily
  apply Prod.ext
  · exact Subtype.ext hk
  · apply phaseExpParam_fderiv_injective d₀
    simpa only [Prod.snd_zero, map_zero] using! hw

theorem finrank_nativeGraphParameters : Module.finrank ℝ NativeGraphParameters = 10 := by
  rw [Module.finrank_prod, finrank_constraintDifferential_kernel, Module.finrank_prod]
  norm_num

/-- Near zero, the same native output is an actual standard quotient representative. -/
theorem eventually_nativeNormalizedGraphFamily_represented
    (Q₀ : StandardSpecialUnitary) (d₀ : PhaseTriple) :
    ∀ᶠ x : NativeGraphParameters in 𝓝 0,
      ∃ Q : StandardSpecialUnitary, Q.val = specialUnitaryGraphParam Q₀ x.1 ∧
        nativeNormalizedGraphFamily Q₀ d₀ x = nativeNormalizedProjectiveFamily
          (QuotientGroup.mk Q,
            (phaseCircle d₀ 0 * Circle.exp x.2.1, phaseCircle d₀ 1 * Circle.exp x.2.2)) := by
  have hc : Tendsto (Prod.fst : NativeGraphParameters → ConstraintTangent) (𝓝 0) (𝓝 0) :=
    continuous_fst.continuousAt.tendsto
  filter_upwards [hc.eventually (eventually_specialUnitaryGraphParam_mem Q₀)] with x hx
  refine ⟨⟨specialUnitaryGraphParam Q₀ x.1, hx⟩, rfl, ?_⟩
  exact nativeNormalizedFamilyExtension_mk ⟨specialUnitaryGraphParam Q₀ x.1, hx⟩
    (phaseCircle d₀ 0 * Circle.exp x.2.1, phaseCircle d₀ 1 * Circle.exp x.2.2)

end CompactAlbert

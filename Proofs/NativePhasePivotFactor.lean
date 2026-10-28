module

public import NativePhasePivotNaturality

@[expose] public section

noncomputable section
namespace Option2.NativeStress.PhasePivotLocusA6
open PhasePivotA6 HTPhaseKron
open CKM.NativeFirstOrder QuadraticCertificate.ExactCKMConfiguration
open scoped BigOperators

abbrev PhasePolynomial := MvPolynomial (Fin 4) ℂ

/-- The only denominator inverted: the product of the four actual phase variables. -/
def coordinateProduct : PhasePolynomial := ∏ i : Fin 4, MvPolynomial.X i

abbrev LaurentPhaseRing := Localization.Away coordinateProduct

def complexConstants : ℂ →+* LaurentPhaseRing :=
  (algebraMap PhasePolynomial LaurentPhaseRing).comp MvPolynomial.C

def formalCoefficients : Q12 →+* LaurentPhaseRing := complexConstants.comp Q12.toComplex

theorem variable_isUnit (i : Fin 4) :
    IsUnit (algebraMap PhasePolynomial LaurentPhaseRing (MvPolynomial.X i)) := by
  apply IsLocalization.Away.isUnit_of_dvd coordinateProduct
  exact Finset.dvd_prod_of_mem (fun j : Fin 4 => (MvPolynomial.X j : PhasePolynomial)) (Finset.mem_univ i)

/-- Variables are ACTUAL ξ coordinates; their ratios to exactPhases form U.
This avoids claiming native phase density from a different parametrization. -/
def formalUnit (i : Fin 4) : LaurentPhaseRingˣ :=
  (variable_isUnit i).unit * Units.map complexConstants.toMonoidHom
    (Units.mk0 ((exactPhases i)⁻¹) (inv_ne_zero (ne_of_unit exactPhases_unit' i)))

theorem formalUnit_val (i : Fin 4) : (formalUnit i : LaurentPhaseRing) =
    algebraMap PhasePolynomial LaurentPhaseRing (MvPolynomial.X i) *
      complexConstants ((exactPhases i)⁻¹) := by
  simp [formalUnit]

/-- The concrete selected973 finite determinant in the Laurent coordinate ring. -/
def formalPivot : LaurentPhaseRing := (selectedMinor (J formalCoefficients formalUnit)).det

/-- Existing localization section, applied to that exact determinant, supplies
its finite polynomial numerator and a power of the coordinate product. -/
def clearingData : PhasePolynomial × ℕ :=
  IsLocalization.Away.sec coordinateProduct formalPivot

def pivotPolynomial : PhasePolynomial := clearingData.1
def clearingPower : ℕ := clearingData.2

theorem numerator_spec :
    formalPivot * algebraMap PhasePolynomial LaurentPhaseRing (coordinateProduct ^ clearingPower) =
      algebraMap PhasePolynomial LaurentPhaseRing pivotPolynomial :=
  IsLocalization.Away.sec_spec coordinateProduct formalPivot

theorem eval_coordinateProduct (ξ : Fin 4 → ℂ) :
    MvPolynomial.eval ξ coordinateProduct = ∏ i : Fin 4, ξ i := by
  simp [coordinateProduct]

theorem phase_product_ne_zero (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (∏ i : Fin 4, ξ i) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => ne_of_unit hξ i

/-- Evaluation extends to the Laurent ring at EVERY actual unit phase. -/
def phaseEval (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : LaurentPhaseRing →+* ℂ :=
  IsLocalization.Away.lift coordinateProduct (g := MvPolynomial.eval ξ)
    (isUnit_iff_ne_zero.mpr (by
      rw [eval_coordinateProduct]
      exact phase_product_ne_zero ξ hξ))

@[simp] theorem phaseEval_algebraMap (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (p : PhasePolynomial) :
    phaseEval ξ hξ (algebraMap PhasePolynomial LaurentPhaseRing p) = MvPolynomial.eval ξ p :=
  IsLocalization.Away.lift_eq coordinateProduct _ p

@[simp] theorem phaseEval_complexConstants (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : ℂ) :
    phaseEval ξ hξ (complexConstants z) = z := by
  simp [complexConstants]

theorem phaseEval_formalCoefficients (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (phaseEval ξ hξ).comp formalCoefficients = Q12.toComplex := by
  ext z
  simp [formalCoefficients]

theorem phaseEval_formalUnit (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) :
    Units.map (phaseEval ξ hξ).toMonoidHom (formalUnit i) = Uph ξ hξ i := by
  apply Units.ext
  change phaseEval ξ hξ (formalUnit i : LaurentPhaseRing) = ξ i / exactPhases i
  rw [formalUnit_val, map_mul, phaseEval_algebraMap, phaseEval_complexConstants]
  simp [div_eq_mul_inv]

theorem phaseEval_formalPivot (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    phaseEval ξ hξ formalPivot = phasePivot (Uph ξ hξ) := by
  have h := map_pivot (phaseEval ξ hξ) formalCoefficients formalUnit
  rw [phaseEval_formalCoefficients] at h
  have hu : (fun i => Units.map (phaseEval ξ hξ).toMonoidHom (formalUnit i)) = Uph ξ hξ :=
    funext (phaseEval_formalUnit ξ hξ)
  rw [hu] at h
  exact h

/-- The numerator identity is on ACTUAL ξ variables, with its exact denominator
power visible. It is not merely an identity on unrelated complex units. -/
theorem polynomial_evaluation (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    MvPolynomial.eval ξ pivotPolynomial =
      (∏ i : Fin 4, ξ i) ^ clearingPower * phasePivot (Uph ξ hξ) := by
  have h := congrArg (phaseEval ξ hξ) numerator_spec
  have h' : phasePivot (Uph ξ hξ) * (∏ i : Fin 4, ξ i) ^ clearingPower =
      MvPolynomial.eval ξ pivotPolynomial := by
    simpa only [map_mul, phaseEval_formalPivot, phaseEval_algebraMap,
      map_pow, eval_coordinateProduct] using h
  simpa only [mul_comm] using h'.symm

/-- Reference nonvanishing is inherited from the exact native selected minor. -/
theorem pivotPolynomial_ne_zero : pivotPolynomial ≠ 0 := by
  intro hp
  have h := polynomial_evaluation exactPhases exactPhases_unit'
  rw [hp, map_zero] at h
  have hn : (∏ i : Fin 4, exactPhases i) ^ clearingPower *
      phasePivot (Uph exactPhases exactPhases_unit') ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (phase_product_ne_zero exactPhases exactPhases_unit'))
      phasePivot_reference_ne_zero
  exact hn h.symm

/-- Exact conversion to the original native matrix, with no generic point premise. -/
theorem phasePivot_native (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    phasePivot (Uph ξ hξ) = (selectedMinor (nativeJ ξ)).det := by
  unfold phasePivot
  rw [J_native]

theorem polynomial_eval_ne_zero_iff_native_minor (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    MvPolynomial.eval ξ pivotPolynomial ≠ 0 ↔ (selectedMinor (nativeJ ξ)).det ≠ 0 := by
  rw [polynomial_evaluation ξ hξ]
  have hn : (∏ i : Fin 4, ξ i) ^ clearingPower ≠ 0 :=
    pow_ne_zero _ (phase_product_ne_zero ξ hξ)
  constructor
  · intro h
    have hp : phasePivot (Uph ξ hξ) ≠ 0 := (mul_ne_zero_iff.mp h).2
    simpa only [phasePivot_native ξ hξ] using hp
  · intro h
    apply mul_ne_zero hn
    rwa [phasePivot_native]

end Option2.NativeStress.PhasePivotLocusA6

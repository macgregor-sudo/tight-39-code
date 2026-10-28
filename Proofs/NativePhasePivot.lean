module

public import NativePhasePivotReference
public import HTPhaseKronBridge4

@[expose] public section

noncomputable section
namespace Option2.NativeStress.PhasePivotA6
open HTPhaseKron NativeH.Equilibrium
open PolynomialJets NativePolynomial NativePolynomial.ConfigurationResiduals QuarticCertificate.RowBridge
open QuarticCertificate.PipelineNaturality
open CKM.NativeFirstOrder QuadraticCertificate.ExactCKMConfiguration

/-- The actual third constant, mapped from Q12 only to a target ring admitting
such a map. No map from Q12 to the finite residue field is used. -/
def thirdQ12 : Q12 := Q12.lit 1 0 0 0 3

/-- The generic finite phase Jacobian of every original translated row. -/
def J {R : Type*} [CommRing R] (ι : Q12 →+* R) (U : Fin 4 → Rˣ) :
    Matrix (Fin 2184) (Fin 1053) R :=
  Matrix.of fun r c => equationLinearMatrix
    (fun r => translate (PhiR ι U) (fRow (ι half) (ι thirdQ12) r)) r c

theorem J_apply {R : Type*} [CommRing R] (ι : Q12 →+* R) (U : Fin 4 → Rˣ)
    (r : Fin 2184) (c : Fin 1053) :
    J ι U r c = jacobianEntry (ι half) (ι thirdQ12) r (PhiR ι U) c :=
  equationLinearMatrix_translate_fRow (PhiR ι U) (ι half) (ι thirdQ12) r c

/-- The unchanged original-row complexified Jacobian at the literal native phase. -/
def nativeJ (ξ : Fin 4 → ℂ) : Matrix (Fin 2184) (Fin 1053) ℂ :=
  Matrix.of fun r c => equationLinearMatrix
    (fun r => translate (fun v => ((PartialAction.pack (literalCfg ξ) v : ℝ) : ℂ))
      (fRow (1/2 : ℂ) (1/3 : ℂ) r)) r c

theorem nativeJ_apply (ξ : Fin 4 → ℂ) (r : Fin 2184) (c : Fin 1053) :
    nativeJ ξ r c = jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r
      (fun v => ((PartialAction.pack (literalCfg ξ) v : ℝ) : ℂ)) c :=
  equationLinearMatrix_translate_fRow _ _ _ r c

theorem toComplex_third : Q12.toComplex thirdQ12 = 1/3 := by
  simp [thirdQ12, Q12.toComplex_lit]

/-- The frozen phi_bridge binds ALL2184 rows and ALL1053 columns at every unit
phase to the actual literal native configuration. -/
theorem J_native (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    J Q12.toComplex (Uph ξ hξ) = nativeJ ξ := by
  have hphi : PhiR Q12.toComplex (Uph ξ hξ) =
      (fun v => ((PartialAction.pack (literalCfg ξ) v : ℝ) : ℂ)) :=
    funext (phi_bridge ξ hξ)
  unfold J nativeJ
  rw [hphi, toComplex_half, toComplex_third]

/-- The reference p-integral point is exactly the same retained Q12 point. -/
theorem referencePoint_complex :
    (fun v : Fin 1053 => Q12.toComplex (baseQ12 v)) = FourSheets.PointBridge.P :=
  pIntegralToComplex_pointPIntegral

/-- Explicit native reference binding, not an assumed equality of seed points. -/
theorem nativeReferencePoint : FourSheets.PointBridge.P =
    (fun v => ((PartialAction.pack (literalCfg exactPhases) v : ℝ) : ℂ)) := by
  funext v
  have hn : Q12.toComplex (baseQ12 v) =
      ((PartialAction.pack (literalCfg exactPhases) v : ℝ) : ℂ) := by
    simpa only [bq, Cn, dite_eq_left v.isLt] using base_link v.val
  exact (congrFun referencePoint_complex v).symm.trans hn

theorem nativeJ_reference : nativeJ exactPhases =
    Matrix.of (fun r c => equationLinearMatrix translatedRowComplex r c) := by
  unfold nativeJ
  rw [← nativeReferencePoint]
  rfl

/-- The EXACT existing rowSelF/colSelF973 minor is nonzero in the actual native
complexified Jacobian at the reference phase. -/
theorem native_reference_minor_ne_zero :
    (selectedMinor (nativeJ exactPhases)).det ≠ 0 := by
  rw [nativeJ_reference]
  exact complexReferenceMinor_ne_zero

/-- A concrete finite Laurent-evaluation pivot, without symbolic determinant expansion. -/
def phasePivot (U : Fin 4 → ℂˣ) : ℂ := (selectedMinor (J Q12.toComplex U)).det

def referencePhase : Fin 4 → ℂˣ := Uph exactPhases exactPhases_unit'

theorem phasePivot_reference_ne_zero : phasePivot referencePhase ≠ 0 := by
  unfold phasePivot referencePhase
  rw [J_native]
  exact native_reference_minor_ne_zero

end Option2.NativeStress.PhasePivotA6

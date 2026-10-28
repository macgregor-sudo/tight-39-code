module

public import A6LinMain
public import PipelineNaturality

@[expose] public section

noncomputable section
namespace Option2.NativeStress.PhasePivotA6
open A6Compact A6Compact.LinEngine
open PolynomialJets QuarticCertificate.PipelineNaturality Q12
open scoped BigOperators

/-- The unchanged explicit973-row/column selection, over any coefficient ring. -/
def selectedMinor {R : Type*} (M : Matrix (Fin 2184) (Fin 1053) R) :
    Matrix (Fin 973) (Fin 973) R := M.submatrix rowSelF colSelF

def integralReferenceMinor : Matrix (Fin 973) (Fin 973) PIntegral1048573 :=
  selectedMinor (Matrix.of fun r c => equationLinearMatrix translatedRowPIntegral r c)

def modularReferenceMinor : Matrix (Fin 973) (Fin 973) A6Compact.F :=
  selectedMinor (Matrix.of fun r c => equationLinearMatrix translatedRowModP r c)

def complexReferenceMinor : Matrix (Fin 973) (Fin 973) ℂ :=
  selectedMinor (Matrix.of fun r c => equationLinearMatrix translatedRowComplex r c)

/-- Abstract triangular determinants use the existing checked LU witnesses;
no symbolic973 determinant is evaluated or expanded. -/
theorem modularReferenceMinor_ne_zero : modularReferenceMinor.det ≠ 0 := by
  change Matrix.det (Matrix.of fun a b =>
    equationLinearMatrix translatedRowModP (id (rowSelF a)) (colSelF b)) ≠ 0
  rw [minor_eq_LoU, Matrix.det_mul, Matrix.det_of_isLowerTriangular _ LoM_lower,
    Matrix.det_of_isUpperTriangular UM_upper]
  have hLo : ∀ a : Fin 973, LoM a a = 1 := by
    intro a
    obtain ⟨hLo, -⟩ := lu_valid a.val a.isLt
    simp only [LoM, Matrix.of_apply]
    rw [natSlot_eq_zero_of_not_mem _ _ (fun e he hek => by have := hLo e he; omega)]
    simp
  simp only [hLo, Finset.prod_const_one, one_mul]
  rw [Finset.prod_ne_zero_iff]
  intro k _
  obtain ⟨-, -, hd, -⟩ := lu_valid k.val k.isLt
  simp only [UM, Matrix.of_apply]
  intro h0
  exact hd (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp h0))

theorem integralReferenceMinor_map_modP :
    reduceMod1048573.mapMatrix integralReferenceMinor = modularReferenceMinor := by
  ext a b
  exact (equationLinearMatrix_modP_eq (rowSelF a) (colSelF b)).symm

theorem integralReferenceMinor_map_complex :
    (pIntegralToComplex 1048573).mapMatrix integralReferenceMinor = complexReferenceMinor := by
  ext a b
  exact (equationLinearMatrix_complex_eq (rowSelF a) (colSelF b)).symm

/-- Nonvanishing lifts from the residue ring to the actual p-integral matrix. -/
theorem integralReferenceMinor_ne_zero : integralReferenceMinor.det ≠ 0 := by
  intro hzero
  apply modularReferenceMinor_ne_zero
  rw [← integralReferenceMinor_map_modP, ← reduceMod1048573.map_det, hzero, map_zero]

/-- The genuine injective p-integral inclusion transfers the SAME selected
minor to complex numbers; no Q12-to-finite-field map is invented. -/
theorem complexReferenceMinor_ne_zero : complexReferenceMinor.det ≠ 0 := by
  intro hzero
  apply integralReferenceMinor_ne_zero
  apply pIntegralToComplex_injective 1048573
  rw [map_zero, (pIntegralToComplex 1048573).map_det,
    integralReferenceMinor_map_complex, hzero]

end Option2.NativeStress.PhasePivotA6

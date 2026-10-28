module

public import NativeT00Equilibrium
public import NativeT01Equilibrium
public import NativeT02Equilibrium
public import NativeT10Equilibrium
public import NativeT11Equilibrium
public import NativeT12Equilibrium
public import NativeT20Equilibrium
public import NativeT21Equilibrium
public import NativeT22Equilibrium
public import NativeT30Equilibrium
public import NativeT31Equilibrium
public import NativeT32Equilibrium
public import NativeTWeights
public import NativeTAnalyticBridge
public import BookNativeBaseBinding

@[expose] public section

/-! Exact fixed-base equilibrium of the twelve supplied Book T representatives.
Every original ambient column is checked; no H anchor-support assumption,
quadratic reproduction, tangent restriction or phase extrapolation is used. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.NativeT
open scoped BigOperators
open NativeH.Equilibrium NativePolynomial.ConfigurationResiduals
open PolynomialJets AnchorSupport Option2.BookNativeBase
open QuadraticCertificate.ExactCKMConfiguration

theorem all_points (i : Fin 4) (a : Fin 3) (p : Fin 39) (k : Fin 27) :
    fastContraction (rawEntries i a) (tSpec i a) (Q12.lit 1 0 0 0 2) baseQ12
      (variableIndex p k) = 0 := by
  fin_cases i <;> fin_cases a
  · exact t00_all_points p k
  · exact t01_all_points p k
  · exact t02_all_points p k
  · exact t10_all_points p k
  · exact t11_all_points p k
  · exact t12_all_points p k
  · exact t20_all_points p k
  · exact t21_all_points p k
  · exact t22_all_points p k
  · exact t30_all_points p k
  · exact t31_all_points p k
  · exact t32_all_points p k

/-- All twelve components and every one of the1053 original columns. -/
theorem pointCoordinates_t_equilibrium (i : Fin 4) (a : Fin 3) (c : Fin 1053) :
    ∑ r : Fin 2184, weightT i a r *
      equationLinearMatrix (translatedRow (fun v => (pointCoordinates v : ℂ))) r c = 0 := by
  rw [← fastContraction_to_original_column]
  let p : Fin 39 := Fin.divNat (n := 27) c
  let k : Fin 27 := Fin.modNat (m := 39) c
  have hc : variableIndex p k = c := by
    apply Fin.ext
    change 27 * (c.val / 27) + c.val % 27 = c.val
    omega
  have h := all_points i a p k
  rw [hc] at h
  rw [h, map_zero]

/-- Literal Book D1 base, unchanged original F normalization and row numbering. -/
theorem book_t_equilibrium (i : Fin 4) (a : Fin 3) (c : Fin 1053) :
    ∑ r : Fin 2184, weightT i a r *
      equationLinearMatrix (translatedRow (fun v => (bookBase v : ℂ))) r c = 0 := by
  rw [bookBase_eq_pointCoordinates]
  exact pointCoordinates_t_equilibrium i a c

theorem originalSeed_t_equilibrium (i : Fin 4) (a : Fin 3) (c : Fin 1053) :
    ∑ r : Fin 2184, weightT i a r *
      equationLinearMatrix (translatedRow (fun v => (originalSeed v : ℂ))) r c = 0 := by
  rw [← bookBase_eq_originalSeed]
  exact book_t_equilibrium i a c

/-- The actual continuous real-linear T covector annihilates the actual packed
original-F derivative on all ambient directions at the literal Book base. -/
theorem stressCovector_at_bookBase (i : Fin 4) (a : Fin 3) :
    (AnalyticDerivative.stressCovector (weightT i a)).comp
      (fderiv ℝ Option2.NativeStress.originalF bookBase) = 0 :=
  stressCovector_originalF_derivative_zero_of_columns bookBase (weightT i a)
    (book_t_equilibrium i a)

theorem stressCovector_at_originalSeed (i : Fin 4) (a : Fin 3) :
    (AnalyticDerivative.stressCovector (weightT i a)).comp
      (fderiv ℝ Option2.NativeStress.originalF originalSeed) = 0 := by
  rw [← bookBase_eq_originalSeed]
  exact stressCovector_at_bookBase i a

theorem all_real_directions_annihilated (i : Fin 4) (a : Fin 3) (W : NativeAmbient) :
    ∑ r : Fin 2184, weightT i a r *
      (fderiv ℝ Option2.NativeStress.originalF bookBase W r : ℂ) = 0 := by
  have h := congrArg (fun L : NativeAmbient →L[ℝ] ℂ => L W)
    (stressCovector_at_bookBase i a)
  simpa only [ContinuousLinearMap.comp_apply, AnalyticDerivative.stressCovector_apply,
    zero_apply] using h

end Option2.NativeStress.NativeT
#check Option2.NativeStress.NativeT.book_t_equilibrium
#print axioms Option2.NativeStress.NativeT.book_t_equilibrium
#check Option2.NativeStress.NativeT.originalSeed_t_equilibrium
#print axioms Option2.NativeStress.NativeT.originalSeed_t_equilibrium
#check Option2.NativeStress.NativeT.stressCovector_at_bookBase
#print axioms Option2.NativeStress.NativeT.stressCovector_at_bookBase
#check Option2.NativeStress.NativeT.all_real_directions_annihilated
#print axioms Option2.NativeStress.NativeT.all_real_directions_annihilated

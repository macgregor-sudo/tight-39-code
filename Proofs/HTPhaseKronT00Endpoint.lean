module

public import HTPhaseKronBridge4
public import HTPhaseKronT00Main
public import NativeTAnalyticBridge

@[expose] public section

/-! # T00 at every unit phase, in the accepted analytic form

For every `ξ` with `IsUnitPhase ξ` (resonant or not), the phased pure T00 covector `ellT00 ξ`
(entries `constant · (ξ/ξ_base)^m`, data `covT00`) annihilates the genuine Fréchet derivative of the
unchanged original `F` at the accepted literal configuration `pack (literalCfg ξ)`. The column premise is
`t00_phased_equilibrium` (one Laurent identity, kernel-checked by collection) transported by
`phi_bridge`; the analytic step is the accepted `stressCovector_originalF_derivative_zero_of_columns`.
First-party. -/

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Option2.NativeStress.HTPhaseKron
open CompactAlbert CKM.NativeFirstOrder NativePolynomial NativeH.Equilibrium
open QuadraticCertificate.ExactCKMConfiguration ConfigurationResidualIndices QuarticCertificate.RowBridge
open MvPolynomial PolynomialJets AnchorSupport

/-- The phased pure T00 covector as original row weights. -/
noncomputable def ellT00 (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Fin 2184 → ℂ := fun r =>
  (covT00.map fun pe => if fNumber pe.e.label = r then
    Q12.toComplex pe.e.coefficient.toQ12 * mono (Uph ξ hξ) pe.x else 0).sum

theorem sum_sparse (L : List PEntry) (f : PEntry → ℂ) (J : Fin 2184 → ℂ) :
    ∑ r : Fin 2184, (L.map fun pe => if fNumber pe.e.label = r then f pe else 0).sum * J r =
      (L.map fun pe => f pe * J (fNumber pe.e.label)).sum := by
  induction L with
  | nil => simp
  | cons pe L ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, ih, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem t00_columns (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (c : Fin 1053) :
    ∑ r : Fin 2184, ellT00 ξ hξ r * equationLinearMatrix
      (translatedRow
        (fun v => ((PartialAction.pack (literalCfg ξ) v : ℝ) : ℂ))) r c = 0 := by
  have hJ : ∀ r, equationLinearMatrix (translatedRow
      (fun v => ((PartialAction.pack (literalCfg ξ) v : ℝ) : ℂ))) r c =
      jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r (PhiR Q12.toComplex (Uph ξ hξ)) c := by
    intro r
    have hP : (fun v => ((PartialAction.pack (literalCfg ξ) v : ℝ) : ℂ)) =
        PhiR Q12.toComplex (Uph ξ hξ) := funext fun v => (phi_bridge ξ hξ v).symm
    rw [hP]
    exact equationLinearMatrix_translate_fRow _ _ _ r c
  simp only [hJ]
  unfold ellT00
  rw [sum_sparse]
  have h := t00_phased_equilibrium Q12.toComplex (Uph ξ hξ) (1/3 : ℂ) c
  rw [toComplex_half] at h
  simpa only [mul_assoc] using h

/-- **T00 equilibrium at every unit phase.** -/
theorem t00_stress_at_literal (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (AnalyticDerivative.stressCovector (ellT00 ξ hξ)).comp
      (fderiv ℝ Option2.NativeStress.originalF (PartialAction.pack (literalCfg ξ))) = 0 :=
  NativeT.stressCovector_originalF_derivative_zero_of_columns _ _ (t00_columns ξ hξ)

/-- Non-vacuity: the row of the first data entry is met by no other entry, so its weight is
`(1/2)·u^0 ≠ 0` at every phase. -/
noncomputable def firstRowUnique : Bool :=
  match covT00 with
  | pe :: rest => rest.all fun q => decide (fNumber q.e.label ≠ fNumber pe.e.label)
  | [] => false

theorem firstRowUnique_eq : firstRowUnique = true := by decide +kernel

end Option2.NativeStress.HTPhaseKron
#print axioms Option2.NativeStress.HTPhaseKron.t00_stress_at_literal

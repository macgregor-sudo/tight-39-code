module

public import HTPCValFacts
public import HTPCValK00
public import HTPCValK01
public import HTPCValK02
public import HTPCValK10
public import HTPCValK11
public import HTPCValK12
public import HTPCValK20
public import HTPCValK21
public import HTPCValK22
public import HTPCValK30
public import HTPCValK31
public import HTPCValK32
public import HTPCovAll
public import HTPhaseCompleteHPack

@[expose] public section

/-!
# T reproduction at every unit phase (first-party)

`residualTxi ξ hξ := residualOf (ellT ξ hξ)` (the twelve covectors `ellT`).
`T_reproduction_phase`: for every `ξ` with `IsUnitPhase ξ` (resonant included) and every `z`,
`residualTxi ξ hξ (originalF (Pξ + Vξ z)) = BookHT.T z`, with `Vxi` and the unchanged Book model.
Chain per component: `value_reduce` (F(Pξ)=0, tangency, gauge lemma, `Vξ = Re(K(y)·literalCfg ξ)`) →
`phi_bridge` → `engine_value` (row reduction, character form, packed block checks `HTPCValKXY`) →
`selectedT_eq_Book`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace Option2.NativeStress.HTPhaseComplete

open CKM.NativeFirstOrder NativePolynomial QuarticCertificate.RowBridge ConfigurationResidualIndices
open NativePolynomial.ConfigurationResiduals NativeH.Equilibrium PolynomialJets AnchorSupport

/-- The Book quadric as a finite sum. -/
theorem book_sum (z : BookHT.Blocks) (i : Fin 4) (a : Fin 3) :
    ∑ m : Fin 3, ((BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).2.2 : ℂ) *
        BookHT.Dictionary.realCoordinates z (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).1 *
        BookHT.Dictionary.realCoordinates z (BookHT.Dictionary.terms (BookHT.Dictionary.tIndex i a) m).2.1 =
      (BookHT.T z i).ofLp a := by
  rw [← BookHT.Dictionary.selectedT_eq_Book]
  simp only [BookHT.Dictionary.quadric, BookHT.Dictionary.termPolynomial, map_add, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, Fin.sum_univ_three]

/-- **One component.** Generic in the covector list. -/
theorem comp_value (L : List HTPhaseKron.PEntry) (i : Fin 4) (a : Fin 3)
    (ell : (ξ : Fin 4 → ℂ) → IsUnitPhase ξ → Fin 2184 → ℂ)
    (hell : ∀ ξ hξ, ell ξ hξ = fun r => (L.map fun pe => if fNumber pe.e.label = r then
      Q12.toComplex pe.e.coefficient.toQ12 * HTPhaseKron.mono (HTPhaseKron.Uph ξ hξ) pe.x else 0).sum)
    (hcol : ∀ ξ hξ c, ∑ r : Fin 2184, ell ξ hξ r * equationLinearMatrix
      (translatedRow (fun v => ((PartialAction.pack (literalCfg ξ) v : ℝ) : ℂ))) r c = 0)
    (hdata : ValEng.dataCheck L i a = true)
    (hbl : ∀ tt ∈ ValEng.pairs6, ValEng.blockCheck L i a tt.1 tt.2 = true)
    (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : BookHT.Blocks) :
    ∑ r : Fin 2184, ell ξ hξ r * ((Option2.NativeStress.originalF (Pxi ξ + Vxi ξ hξ z) r : ℝ) : ℂ) =
      (BookHT.T z i).ofLp a := by
  rw [value_reduce ξ hξ (ell ξ hξ) (hcol ξ hξ) z]
  have hX : Xc ξ = HTPhaseKron.PhiR Q12.toComplex (HTPhaseKron.Uph ξ hξ) :=
    funext fun v => (HTPhaseKron.phi_bridge ξ hξ v).symm
  rw [hX, hell, HTPhaseKron.sum_sparse, ← HTPhaseKron.toComplex_half]
  have := ValEng.engine_value Q12.toComplex (HTPhaseKron.Uph ξ hξ) (BookHT.Dictionary.realCoordinates z)
    ValEng.baseOK_eq ValEng.kPosOK_eq ValEng.closureOK_eq L i a hdata hbl
  unfold ValEng.Wv at this
  rw [this, book_sum]

/-- The T residual at phase ξ. -/
noncomputable def residualTxi (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : (Fin 2184 → ℝ) →L[ℝ] BookHT.Blocks :=
  residualOf (ellT ξ hξ)

/-- Row form of the twelve components. -/
theorem T_reproduction_rows (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : BookHT.Blocks) (i : Fin 4) (a : Fin 3) :
    ∑ r : Fin 2184, ellT ξ hξ i a r * ((Option2.NativeStress.originalF (Pxi ξ + Vxi ξ hξ z) r : ℝ) : ℂ) =
      (BookHT.T z i).ofLp a := by
  fin_cases i <;> fin_cases a
  · exact comp_value _ 0 0 HTPhaseKron.ellT00 (fun _ _ => rfl) t00_columns ValEng.data00 ValEng.blocks00 ξ hξ z
  · exact comp_value _ 0 1 ellT01 (fun _ _ => rfl) t01_columns ValEng.data01 ValEng.blocks01 ξ hξ z
  · exact comp_value _ 0 2 ellT02 (fun _ _ => rfl) t02_columns ValEng.data02 ValEng.blocks02 ξ hξ z
  · exact comp_value _ 1 0 ellT10 (fun _ _ => rfl) t10_columns ValEng.data10 ValEng.blocks10 ξ hξ z
  · exact comp_value _ 1 1 ellT11 (fun _ _ => rfl) t11_columns ValEng.data11 ValEng.blocks11 ξ hξ z
  · exact comp_value _ 1 2 ellT12 (fun _ _ => rfl) t12_columns ValEng.data12 ValEng.blocks12 ξ hξ z
  · exact comp_value _ 2 0 ellT20 (fun _ _ => rfl) t20_columns ValEng.data20 ValEng.blocks20 ξ hξ z
  · exact comp_value _ 2 1 ellT21 (fun _ _ => rfl) t21_columns ValEng.data21 ValEng.blocks21 ξ hξ z
  · exact comp_value _ 2 2 ellT22 (fun _ _ => rfl) t22_columns ValEng.data22 ValEng.blocks22 ξ hξ z
  · exact comp_value _ 3 0 ellT30 (fun _ _ => rfl) t30_columns ValEng.data30 ValEng.blocks30 ξ hξ z
  · exact comp_value _ 3 1 ellT31 (fun _ _ => rfl) t31_columns ValEng.data31 ValEng.blocks31 ξ hξ z
  · exact comp_value _ 3 2 ellT32 (fun _ _ => rfl) t32_columns ValEng.data32 ValEng.blocks32 ξ hξ z

/-- **T reproduction at every unit phase**. -/
theorem T_reproduction_phase (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : BookHT.Blocks) :
    residualTxi ξ hξ (Option2.NativeStress.originalF (Pxi ξ + Vxi ξ hξ z)) = BookHT.T z := by
  funext i
  ext a
  rw [residualTxi, residualOf_apply, T_reproduction_rows]

/-- **Block equilibrium**. -/
theorem residual_equilibrium (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (residualTxi ξ hξ).comp (fderiv ℝ Option2.NativeStress.originalF (Pxi ξ)) = 0 ∧
      (residualHxi ξ hξ).comp (fderiv ℝ Option2.NativeStress.originalF (Pxi ξ)) = 0 := by
  refine ⟨?_, residualHxi_equilibrium ξ hξ⟩
  ext W i a
  have h := congrArg (fun L : (Fin 1053 → ℝ) →L[ℝ] ℂ => L W) (T_equilibrium ξ hξ i a)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at h ⊢
  rw [residualTxi, residualOf_apply, ← AnalyticDerivative.stressCovector_apply, h]
  rfl

end Option2.NativeStress.HTPhaseComplete

#print axioms Option2.NativeStress.HTPhaseComplete.T_reproduction_phase
#print axioms Option2.NativeStress.HTPhaseComplete.T_reproduction_rows
#print axioms Option2.NativeStress.HTPhaseComplete.residual_equilibrium
#print axioms Option2.NativeStress.HTPhaseComplete.residualTxi

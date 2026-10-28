module

public import NativeTDataChecks00
public import NativeTDataChecks01
public import NativeTDataChecks02
public import NativeTDataChecks10
public import NativeTDataChecks11
public import NativeTDataChecks12
public import NativeTDataChecks20
public import NativeTDataChecks21
public import NativeTDataChecks22
public import NativeTDataChecks30
public import NativeTDataChecks31
public import NativeTDataChecks32
public import BookQuadricDictionary
public import NativeHEquilibriumTransport
public import OriginalFAnalyticDerivativeV2

@[expose] public section

/-! The twelve literal Book T representatives on all original2184 rows.
The accepted Dictionary.tIndex determines the order; T has no H sign/conjugation.
Sparse evaluation, exact Q12 interpretation and real continuous covectors are
reused from their accepted generic owners. No H anchor support is asserted. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.NativeT
open scoped BigOperators
open NativeH.Equilibrium ConfigurationResidualIndices QuarticCertificate.RowBridge
open PolynomialJets AnchorSupport
open QuadraticCertificate.ExactCKMConfiguration

def rawEntries : Fin 4 → Fin 3 → List NativeH.Entry :=
  ![![lambda42,lambda43,lambda45], ![lambda6,lambda12,lambda16],
    ![lambda7,lambda9,lambda17], ![lambda3,lambda13,lambda19]]

/-- The generic evaluator's orientation record, with both orientation flags false. -/
def tSpec (i : Fin 4) (a : Fin 3) : NativeH.HSpec :=
  ⟨BookHT.Dictionary.tIndex i a, false, false⟩

theorem rawEntries_rows_nodup (i : Fin 4) (a : Fin 3) :
    (originalRows (rawEntries i a)).Nodup := by
  fin_cases i <;> fin_cases a
  · exact lambda42_rows_nodup
  · exact lambda43_rows_nodup
  · exact lambda45_rows_nodup
  · exact lambda6_rows_nodup
  · exact lambda12_rows_nodup
  · exact lambda16_rows_nodup
  · exact lambda7_rows_nodup
  · exact lambda9_rows_nodup
  · exact lambda17_rows_nodup
  · exact lambda3_rows_nodup
  · exact lambda13_rows_nodup
  · exact lambda19_rows_nodup

def entries (i : Fin 4) (a : Fin 3) : List (Fin 2184 × ℂ) :=
  (rawEntries i a).map fun e => (fNumber e.label, e.coefficient.toComplex)

def weightT (i : Fin 4) (a : Fin 3) : Weights := NativeH.sparseWeight (entries i a)

theorem weightT_dense_sparse (i : Fin 4) (a : Fin 3) (g : Fin 2184 → ℂ) :
    (∑ r : Fin 2184, weightT i a r * g r) =
      ((entries i a).map fun e => e.2 * g e.1).sum :=
  NativeH.dense_sparse (entries i a) g

/-- The exact real continuous covector, retaining both complex components. -/
theorem stressCovector_apply (i : Fin 4) (a : Fin 3) (q : Fin 2184 → ℝ) :
    AnalyticDerivative.stressCovector (weightT i a) q =
      ((entries i a).map fun e => e.2 * (q e.1 : ℂ)).sum := by
  rw [AnalyticDerivative.stressCovector_apply, weightT_dense_sparse]

/-- This is a representation identity only; cancellation is proved separately. -/
theorem fastContraction_to_original_column (i : Fin 4) (a : Fin 3) (c : Fin 1053) :
    Q12.toComplex (fastContraction (rawEntries i a) (tSpec i a)
      (Q12.lit 1 0 0 0 2) baseQ12 c) =
    ∑ r : Fin 2184, weightT i a r *
      equationLinearMatrix (translatedRow (fun v => ((pointCoordinates v : ℝ) : ℂ))) r c := by
  rw [fastContraction_eq _ _ _ (Q12.lit 1 0 0 0 3), weightT_dense_sparse]
  simp only [entries, map_list_sum, List.map_map, Function.comp_def, map_mul]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e _
  rw [NativeH.orientedQ12_toComplex]
  change e.coefficient.toComplex * _ = e.coefficient.toComplex * _
  congr 1
  rw [jacobianEntry_map, halfQ12_complex, thirdQ12_complex, baseQ12_complex]
  exact (equationLinearMatrix_translate_fRow _ _ _ _ _).symm

end Option2.NativeStress.NativeT
#check Option2.NativeStress.NativeT.weightT
#print axioms Option2.NativeStress.NativeT.rawEntries_rows_nodup
#print axioms Option2.NativeStress.NativeT.fastContraction_to_original_column

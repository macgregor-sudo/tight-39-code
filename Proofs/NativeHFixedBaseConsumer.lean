module

public import NativeHEquilibriumEndpoint
public import BookNativeBaseBinding
public import NativeHStressFunctional

@[expose] public section

namespace Option2.NativeStress.NativeH.Equilibrium

open scoped BigOperators
open PolynomialJets AnchorSupport NativePolynomial.ConfigurationResiduals
open QuadraticCertificate.ExactCKMConfiguration
open AnalyticDerivative NativePolynomial.PartialAction

/-- The complete hL input, directly on the source-bound literal Book base. -/
theorem book_h_equilibrium (i : Fin 4) (a : Fin 3) (c : Fin 1053) :
    ∑ r : Fin 2184, weightC i a r * equationLinearMatrix
      (translatedRow (fun v => ((Option2.BookNativeBase.bookBase v : ℝ) : ℂ))) r c = 0 := by
  rw [Option2.BookNativeBase.bookBase_eq_pointCoordinates]
  exact all_columns i a c

/-- Exact complete hL premise of realStress_comp_fderiv_originalF_eq_zero. -/
theorem actual_h_equilibrium (i : Fin 4) (a : Fin 3) (c : Fin 1053) :
    ∑ r : Fin 2184, weightC i a r * equationLinearMatrix
      (translatedRow (complexPack Actual.actualConfiguration)) r c = 0 := by
  change (∑ r : Fin 2184, weightC i a r * equationLinearMatrix
    (translatedRow (fun v => ((pack Actual.actualConfiguration v : ℝ) : ℂ))) r c) = 0
  rw [Actual.pack_actualConfiguration]
  exact all_columns i a c

/-- The actual real H stress functional annihilates the original real derivative
at the accepted supplied native base, for all four panels and all Book weights. -/
theorem realStress_at_native_base (i : Fin 4) (w : BookHT.Blocks) :
    (realStressFunctional i w).comp
      (fderiv ℝ AnalyticDerivative.originalF Actual.actualConfiguration) = 0 :=
  realStress_comp_fderiv_originalF_eq_zero Actual.actualConfiguration
    Actual.actualConfiguration i w Actual.actual_input_all_fRows
    (actual_h_equilibrium i) (fun _ _ => rfl)

/-- The pre-existing supported continuation theorem now has its actual hL
premise discharged. Only the stated original anchor agreement at C remains. -/
theorem realStress_at_matching_anchors (C : RealConfiguration) (i : Fin 4) (w : BookHT.Blocks)
    (hanchor : ∀ v, AnchorCoordinate i v → pack C v = pack Actual.actualConfiguration v) :
    (realStressFunctional i w).comp (fderiv ℝ AnalyticDerivative.originalF C) = 0 :=
  realStress_comp_fderiv_originalF_eq_zero Actual.actualConfiguration C i w
    Actual.actual_input_all_fRows (actual_h_equilibrium i) hanchor

end Option2.NativeStress.NativeH.Equilibrium

#print axioms Option2.NativeStress.NativeH.Equilibrium.book_h_equilibrium
#print axioms Option2.NativeStress.NativeH.Equilibrium.actual_h_equilibrium
#print axioms Option2.NativeStress.NativeH.Equilibrium.realStress_at_native_base
#print axioms Option2.NativeStress.NativeH.Equilibrium.realStress_at_matching_anchors

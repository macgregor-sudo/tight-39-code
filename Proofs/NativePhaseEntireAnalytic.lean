module

public import NativePhaseEntireFamilies

@[expose] public section

/-! Power-series regularity of the explicit native entire families, proved
from their formulas rather than a multivariable differentiability converse. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Option2.NativeStress.PhaseEntireAnalyticA6
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CompactAlbert UnitaryErrorBases Matrix NativePolynomial
open PhaseEntireFamilyA6 PhaseBookComplexificationA6
open scoped BigOperators ComplexConjugate

theorem coordinate_analytic (k : ParamIndex) (z : ParamIndex → ℂ) :
    AnalyticAt ℂ (fun w : ParamIndex → ℂ => w k) z :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ParamIndex => ℂ) k).analyticAt z

theorem complexDer_analytic (z : ParamIndex → ℂ) : AnalyticAt ℂ complexDer z := by
  unfold complexDer
  apply Finset.analyticAt_fun_sum
  intro j hj
  exact (coordinate_analytic _ z).smul analyticAt_const

section MatrixNorm
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem suMatC_analytic (bar : Bool) (z : ParamIndex → ℂ) :
    AnalyticAt ℂ (suMatC bar) z := by
  unfold suMatC
  apply Finset.analyticAt_fun_sum
  intro j hj
  exact (coordinate_analytic _ z).smul analyticAt_const

theorem hiddenC_analytic (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (bar : Bool) (l : Label) (i j : Index) (z : ParamIndex → ℂ) :
    AnalyticAt ℂ (fun w => PhaseEntireFamiliesA6.hiddenC H ξ hξ bar w l i j) z := by
  have he : AnalyticAt ℂ (fun w => NormedSpace.exp (suMatC bar w)) z :=
    (NormedSpace.exp_analytic (𝕂 := ℂ) _).comp (suMatC_analytic bar z)
  have ha (b : Index) : AnalyticAt ℂ (fun w : ParamIndex → ℂ => angleC w b) z := by
    unfold angleC
    split_ifs
    · exact coordinate_analytic _ z
    · exact coordinate_analytic _ z
    · exact (coordinate_analytic _ z).neg.sub (coordinate_analytic _ z)
  have hp (b : Index) : AnalyticAt ℂ
      (fun w => phaseC (anchorTriple ξ hξ H) bar w b) z := by
    unfold phaseC
    split_ifs <;> exact analyticAt_const.mul ((analyticAt_const.mul (ha b)).cexp)
  have hmEntry (a b : Index) : AnalyticAt ℂ (fun w : ParamIndex → ℂ =>
      monomialC (anchorTriple ξ hξ H) bar w (gaugeLabel H l) a b) z := by
    unfold monomialC
    split_ifs <;> first | exact (hp b).mul analyticAt_const | exact analyticAt_const
  have heEntry (a b : Index) : AnalyticAt ℂ
      (fun w => NormedSpace.exp (suMatC bar w) a b) z :=
    ((matrixEntry a b).analyticAt _).comp he
  unfold PhaseEntireFamiliesA6.hiddenC
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  repeat' first
    | exact analyticAt_const
    | exact hmEntry _ _
    | exact heEntry _ _
    | apply AnalyticAt.mul
    | apply Finset.analyticAt_fun_sum; intro a ha

end MatrixNorm

theorem preExtension_analytic (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (z : ParamIndex → ℂ) : AnalyticAt ℂ (PhaseEntireFamiliesA6.preExtension H ξ hξ) z := by
  have hh : AnalyticAt ℂ (PhaseEntireFamiliesA6.hiddenCoordinates H ξ hξ) z := by
    apply AnalyticAt.pi
    intro j
    unfold PhaseEntireFamiliesA6.hiddenCoordinates
    split_ifs
    · exact ((hiddenC_analytic H ξ hξ false j.1 j.2.1 j.2.2.1 z).add
        (hiddenC_analytic H ξ hξ true j.1 j.2.1 j.2.2.1 z)).div_const
    · exact ((hiddenC_analytic H ξ hξ false j.1 j.2.1 j.2.2.1 z).sub
        (hiddenC_analytic H ξ hξ true j.1 j.2.1 j.2.2.1 z)).div_const
  exact analyticAt_const.add
    (((complexMap (PhaseEntireFamiliesA6.packedPreLin H)).toContinuousLinearMap.analyticAt _).comp hh)

theorem rawExtension_analyticAt (H : Fin 4) (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (z : ParamIndex → ℂ) : AnalyticAt ℂ (PhaseEntireFamiliesA6.rawExtension H ξ hξ) z := by
  have he : AnalyticAt ℂ (fun w => NormedSpace.exp (complexDer w)) z :=
    (NormedSpace.exp_analytic (𝕂 := ℂ) _).comp (complexDer_analytic z)
  have hp := preExtension_analytic H ξ hξ z
  apply AnalyticAt.pi
  intro k
  unfold PhaseEntireFamiliesA6.rawExtension PartialAction.pack
  have hu : AnalyticAt ℂ (fun w => fun j : Fin 27 =>
      PhaseEntireFamiliesA6.preExtension H ξ hξ w
        (finProdFinEquiv ((@Fin.divNat 39 27 k),j))) z := by
    apply AnalyticAt.pi
    intro j
    exact ((ContinuousLinearMap.proj
      (finProdFinEquiv ((@Fin.divNat 39 27 k),j))).analyticAt _).comp hp
  have ha := ((ContinuousLinearMap.apply ℂ CCoord).analyticAt_bilinear _).comp₂ hu he
  exact ((ContinuousLinearMap.proj (@Fin.modNat 39 27 k)).analyticAt _).comp ha

#print axioms Option2.NativeStress.PhaseEntireAnalyticA6.rawExtension_analyticAt
end Option2.NativeStress.PhaseEntireAnalyticA6

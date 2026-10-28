module

public import NativeTEquilibriumEndpoint
public import NativeHResidualQuadratic

@[expose] public section

/-! The literal twelve T covectors applied to the actual original residual.
The constant and linear terms vanish at the literal Book base. The remaining
quadratic evaluator is faithfully restricted through the unchanged realV map;
its equality with Book T is exposed as the remaining finite comparison. -/
set_option Elab.async false
set_option maxRecDepth 8192
set_option autoImplicit false
noncomputable section

namespace Option2.NativeStress.NativeT.Reproduction

open scoped BigOperators
open QuarticCertificate.RowBridge PolynomialJets
open NativePolynomial.ConfigurationResiduals AnchorSupport Option2.BookNativeBase
open BookHT.TangentCoordinates BookHT.Dictionary

def residualT (q : Fin 2184 → ℝ) : BookHT.Blocks :=
  fun i => WithLp.toLp 2 (fun a => AnalyticDerivative.stressCovector (weightT i a) q)

/-- Full original-row homogeneous evaluator, with the exact native half. -/
def homogeneousT (i : Fin 4) (a : Fin 3) (x : Fin 1053 → ℂ) : ℂ :=
  ∑ r : Fin 2184, weightT i a r * quadraticPartValue (1/2 : ℂ) r x

/-- The entire original residual contraction, for arbitrary real ambient x.
No tangent, H support, or quadratic reproduction premise occurs. -/
theorem residual_eq_homogeneous (x : NativeAmbient) (i : Fin 4) (a : Fin 3) :
    residualT (Option2.NativeStress.originalF (bookBase+x)) i a =
      homogeneousT i a (fun c => (x c : ℂ)) := by
  let p : Fin 1053 → ℂ := fun c => (bookBase c : ℂ)
  let v : Fin 1053 → ℂ := fun c => (x c : ℂ)
  have hp (r : Fin 2184) : rowValue (1/2 : ℂ) (1/3 : ℂ) r p = 0 := by
    change rowValue (1/2 : ℂ) (1/3 : ℂ) r (fun c => (bookBase c : ℂ)) = 0
    rw [← NativeH.Reproduction.originalF_complex, bookBase_originalF_zero]
    rfl
  have hc (c : Fin 1053) :
      (∑ r : Fin 2184, weightT i a r * jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r p c) = 0 := by
    have he := book_t_equilibrium i a c
    change (∑ r : Fin 2184, weightT i a r * equationLinearMatrix
      (fun r => translate p (fRow (1/2 : ℂ) (1/3 : ℂ) r)) r c) = 0 at he
    simpa only [equationLinearMatrix_translate_fRow] using he
  have hl : (∑ r : Fin 2184, weightT i a r *
      (∑ c : Fin 1053, jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r p c * v c)) = 0 := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro c _
    rw [← Finset.sum_mul, hc, zero_mul]
  change AnalyticDerivative.stressCovector (weightT i a) _ = _
  rw [AnalyticDerivative.stressCovector_apply]
  simp_rw [NativeH.Reproduction.originalF_complex]
  have hv : (fun c => ((bookBase+x) c : ℂ)) = p+v := by
    funext c
    simp [p,v]
  rw [hv]
  simp_rw [NativeH.Reproduction.rowValue_add, hp, zero_add, mul_add]
  rw [Finset.sum_add_distrib, hl, zero_add]
  rfl

def nativeTQuadraticAlongRealV (z : BookHT.Blocks) : BookHT.Blocks :=
  fun i => WithLp.toLp 2 (fun a => homogeneousT i a (V (realCoordinates z)))

/-- Exact supplied 24-coordinate substitution and all1053 packed coordinates. -/
theorem native_T_quadratic_variation (z : BookHT.Blocks) :
    residualT (Option2.NativeStress.originalF (bookBase+realV z)) =
      nativeTQuadraticAlongRealV z := by
  funext i
  ext a
  rw [residual_eq_homogeneous]
  have hv : (fun c => ((realV z c : ℝ) : ℂ)) = V (realCoordinates z) :=
    funext (realV_complex z)
  rw [hv]
  rfl

theorem native_quadratic_original_rows (z : BookHT.Blocks) (i : Fin 4) (a : Fin 3) :
    nativeTQuadraticAlongRealV z i a =
      ∑ r : Fin 2184, weightT i a r * MvPolynomial.eval (V (realCoordinates z))
        (MvPolynomial.homogeneousComponent 2
          (translate (fun c => ((bookBase c : ℝ) : ℂ))
            (fRow (1/2 : ℂ) (1/3 : ℂ) r))) := by
  simp only [eval_homogeneousComponent_two_translate_fRow]
  rfl

/-- No dropped native rows: this sparse list is the existing supplied T list. -/
theorem homogeneousT_sparse (i : Fin 4) (a : Fin 3) (x : Fin 1053 → ℂ) :
    homogeneousT i a x =
      ((entries i a).map fun e => e.2 * quadraticPartValue (1/2 : ℂ) e.1 x).sum :=
  weightT_dense_sparse i a _

/-- Reproduction is still the comparison with the independently defined Book T. -/
theorem reproduction_iff_homogeneous (z : BookHT.Blocks) :
    residualT (Option2.NativeStress.originalF (bookBase+realV z)) = BookHT.T z ↔
      nativeTQuadraticAlongRealV z = BookHT.T z := by
  rw [native_T_quadratic_variation]

/-- The exact remaining component comparison uses the accepted table selector;
this equivalence does not prove the comparison itself. -/
theorem reproduction_component_iff_selected_quadric
    (z : BookHT.Blocks) (i : Fin 4) (a : Fin 3) :
    residualT (Option2.NativeStress.originalF (bookBase+realV z)) i a = BookHT.T z i a ↔
      homogeneousT i a (V (realCoordinates z)) =
        MvPolynomial.eval (realCoordinates z) (quadric (tIndex i a)) := by
  rw [native_T_quadratic_variation, selectedT_eq_Book]
  rfl

end Option2.NativeStress.NativeT.Reproduction

#check Option2.NativeStress.NativeT.Reproduction.residual_eq_homogeneous
#print axioms Option2.NativeStress.NativeT.Reproduction.residual_eq_homogeneous
#check Option2.NativeStress.NativeT.Reproduction.native_T_quadratic_variation
#print axioms Option2.NativeStress.NativeT.Reproduction.native_T_quadratic_variation
#print axioms Option2.NativeStress.NativeT.Reproduction.native_quadratic_original_rows
#print axioms Option2.NativeStress.NativeT.Reproduction.homogeneousT_sparse
#print axioms Option2.NativeStress.NativeT.Reproduction.reproduction_iff_homogeneous
#check Option2.NativeStress.NativeT.Reproduction.reproduction_component_iff_selected_quadric
#print axioms Option2.NativeStress.NativeT.Reproduction.reproduction_component_iff_selected_quadric

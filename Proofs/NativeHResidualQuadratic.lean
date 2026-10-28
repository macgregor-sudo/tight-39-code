module

public import NativeHQuadraticCore
public import NativeHFixedBaseConsumer

@[expose] public section

namespace Option2.NativeStress.NativeH.Reproduction

open scoped BigOperators
open QuarticCertificate.RowBridge
open ConfigurationResidualIndices NativePolynomial.ConfigurationResiduals
open PolynomialJets AnchorSupport Option2.BookNativeBase

set_option maxRecDepth 8192

theorem quadraticValue_add (c : ℂ) (l : List (Fin 1053 × Fin 1053 × ℤ))
    (p x : Fin 1053 → ℂ) :
    quadraticValue c l (p+x) = quadraticValue c l p + quadraticValue c l x +
      ((l.flatMap fun e => [(e.1,c*(e.2.2:ℂ)*p e.2.1),
        (e.2.1,c*(e.2.2:ℂ)*p e.1)]).map fun e => e.2*x e.1).sum := by
  induction l with
  | nil => simp [quadraticValue]
  | cons e l ih =>
      simp only [quadraticValue, List.map_cons, List.sum_cons] at ih ⊢
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, Pi.add_apply, add_zero] at ih ⊢
      rw [ih]
      ring

theorem linearValue_add (l : List (Fin 1053 × ℤ)) (p x : Fin 1053 → ℂ) :
    linearValue l (p+x) = linearValue l p + linearValue l x := by
  induction l with
  | nil => simp [linearValue]
  | cons e l ih =>
      simp only [linearValue, List.map_cons, List.sum_cons] at ih ⊢
      simp only [Pi.add_apply] at ih ⊢
      rw [ih]
      ring

theorem shapeValue_add (h t : ℂ) (s : RowShape) (p x : Fin 1053 → ℂ) :
    shapeValue h t s (p+x) = shapeValue h t s p +
      (∑ c : Fin 1053, shapeJacobianEntry h s p c * x c) +
      quadraticValue (quadraticScale h s) s.quadratic x := by
  have hj : (∑ c : Fin 1053, shapeJacobianEntry h s p c * x c) =
      ((shapeJacobianRow h s p).map fun e => e.2*x e.1).sum := by
    simp_rw [← sparseLookup_shapeJacobianRow]
    exact dense_sparse (shapeJacobianRow h s p) x
  rw [hj]
  simp only [shapeValue, quadraticValue_add, linearValue_add, shapeJacobianRow,
    List.map_append, List.sum_append, List.map_map, Function.comp_def]
  unfold linearValue
  ring

theorem rowValue_add (h t : ℂ) (r : Fin 2184) (p x : Fin 1053 → ℂ) :
    rowValue h t r (p+x) = rowValue h t r p +
      (∑ c : Fin 1053, jacobianEntry h t r p c * x c) + quadraticPartValue h r x :=
  shapeValue_add h t (rowShape r) p x

theorem shapeValue_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (h t : R) (s : RowShape) (x : Fin 1053 → R) :
    f (shapeValue h t s x) = shapeValue (f h) (f t) s (fun c => f (x c)) := by
  simp only [shapeValue, quadraticValue, linearValue, map_add, map_list_sum,
    List.map_map, Function.comp_def, map_mul, map_intCast]
  simp [quadraticScale, constantTerm, apply_ite f]

theorem originalF_complex (x : NativeAmbient) (r : Fin 2184) :
    (Option2.NativeStress.originalF x r : ℂ) =
      rowValue (1/2 : ℂ) (1/3 : ℂ) r (fun c => (x c : ℂ)) := by
  unfold Option2.NativeStress.originalF
  rw [eval_fRow]
  change Complex.ofRealHom (shapeValue _ _ _ _) = _
  rw [shapeValue_map]
  norm_num [rowValue]

/-- At the literal Book base, the exact H contraction of the full residual is
its homogeneous quadratic evaluator for every real ambient displacement. -/
theorem residual_eq_homogeneous (x : NativeAmbient) (i : Fin 4) (a : Fin 3) :
    residualContraction (Option2.NativeStress.originalF (bookBase+x)) i a =
      homogeneousH i a (fun c => (x c : ℂ)) := by
  let p : Fin 1053 → ℂ := fun c => (bookBase c : ℂ)
  let v : Fin 1053 → ℂ := fun c => (x c : ℂ)
  have hp (r : Fin 2184) : rowValue (1/2 : ℂ) (1/3 : ℂ) r p = 0 := by
    change rowValue (1/2 : ℂ) (1/3 : ℂ) r (fun c => (bookBase c : ℂ)) = 0
    rw [← originalF_complex, bookBase_originalF_zero]
    rfl
  have hc (c : Fin 1053) :
      (∑ r : Fin 2184, weightC i a r * jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r p c) = 0 := by
    have he := Equilibrium.book_h_equilibrium i a c
    change (∑ r : Fin 2184, weightC i a r * equationLinearMatrix
      (fun r => translate p (fRow (1/2 : ℂ) (1/3 : ℂ) r)) r c) = 0 at he
    simpa only [equationLinearMatrix_translate_fRow] using he
  have hl : (∑ r : Fin 2184, weightC i a r *
      (∑ c : Fin 1053, jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r p c * v c)) = 0 := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro c _
    rw [← Finset.sum_mul, hc, zero_mul]
  rw [residualContraction_apply]
  simp_rw [originalF_complex]
  have hv : (fun c => ((bookBase+x) c : ℂ)) = p+v := by
    funext c
    simp [p,v]
  rw [hv]
  simp_rw [rowValue_add, hp, zero_add, mul_add]
  rw [Finset.sum_add_distrib, hl, zero_add]
  rfl

end Option2.NativeStress.NativeH.Reproduction

#print axioms Option2.NativeStress.NativeH.Reproduction.residual_eq_homogeneous

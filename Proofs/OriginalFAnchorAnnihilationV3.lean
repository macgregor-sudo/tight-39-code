module

public import OriginalFAnchorSupportV3

@[expose] public section

/-!
Full ambient first-order annihilation from the actual contracted quadratic.

This source composes the native original-F identity already derived in
OriginalFAnchorSupport with polynomial translation and degree-two homogeneity.
It does not repeat the residual-case expansion. The new base point need not
solve F, and the perturbation direction need not preserve the anchors.

Actual weights, their full base annihilation, contracted VARIABLE support,
phase domains and geometric reanchoring remain caller obligations. This is a conditional implication, not a native certificate.
-/

noncomputable section

namespace Option2.NativeStress.AnchorSupport

open scoped BigOperators
open MvPolynomial PolynomialJets

private def translationHom (U : Ambient) : Poly →+* Poly :=
  eval₂Hom MvPolynomial.C (fun v => X v + MvPolynomial.C (U v))

private theorem translate_translate (P U : Ambient) (p : Poly) :
    translate U (translate P p) = translate (P + U) p := by
  have h : (translationHom U).comp (translationHom P) = translationHom (P + U) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [translationHom]
    · intro v
      simp [translationHom, Pi.add_apply, add_assoc, add_comm, add_left_comm]
  exact congrArg (fun f : Poly →+* Poly => f p) h

private theorem translate_eq_self_of_vars_zero
    (U : Ambient) (p : Poly) (hzero : ∀ v ∈ p.vars, U v = 0) :
    translate U p = p := by
  change translationHom U p = (RingHom.id Poly) p
  apply MvPolynomial.hom_congr_vars
  · apply RingHom.ext
    intro a
    simp [translationHom]
  · intro v hv _
    simp [translationHom, hzero v hv]
  · rfl

private theorem translate_finite_sum {ι : Type*} [Fintype ι]
    (U : Ambient) (ell : ι → ℂ) (g : ι → Poly) :
    translate U (∑ r, ell r • g r) = ∑ r, ell r • translate U (g r) := by
  classical
  change translationHom U (∑ r, ell r • g r) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [translationHom, smul_eq_C_mul, map_mul, eval₂Hom_C]
  rfl

private theorem translate_contractedPolynomial
    (P U : Ambient) (ell : Weights) :
    translate U (contractedPolynomial P ell) = contractedPolynomial (P + U) ell := by
  classical
  simp only [contractedPolynomial, translate_finite_sum, translatedRow]
  apply Finset.sum_congr rfl
  intro r _
  exact congrArg (fun p : Poly => ell r • p) (translate_translate P U (row r))

private theorem eval_translate_at_point (P V : Ambient) (p : Poly) :
    eval V (translate P p) = eval (P + V) p := by
  rw [translate, ← MvPolynomial.eval_assoc]
  have hpoint : (eval V ∘ (fun j => X j + MvPolynomial.C (P j))) = P + V := by
    funext j
    simp only [Function.comp_apply, map_add, eval_X, eval_C, Pi.add_apply]
    exact add_comm _ _
  rw [hpoint]

private theorem eval_homogeneous_quadratic_smul
    (q : Poly) (hq : q.IsHomogeneous 2) (W : Ambient) (t : ℂ) :
    eval (t • W) q = t ^ 2 * eval W q := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdegree : (∑ v ∈ d.support, d v) = 2 :=
    (hq.degree_eq_sum_deg_support hd).symm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdegree]
  ring

/-- Moving the base point within the anchor-fixed affine slice leaves the
ENTIRE contracted translated polynomial equal to the same homogeneous quadratic.
No solution condition at C is assumed. -/
theorem contractedPolynomial_eq_quadratic_at_anchor
    (P : Ambient) (ell : Weights) (i : Fin 4)
    (hP : ∀ r, eval P (row r) = 0)
    (hL : ∀ c : Fin 1053,
      ∑ r, ell r * equationLinearMatrix (translatedRow P) r c = 0)
    (hsupport : HasAnchorSupport P ell i)
    (C : Ambient) (hanchor : ∀ v, AnchorCoordinate i v → C v = P v) :
    contractedPolynomial C ell = contractedQuadratic P ell := by
  have hpoint : P + (C - P) = C := by rw [add_comm, sub_add_cancel]
  have hzero : ∀ v ∈ (contractedQuadratic P ell).vars, (C - P) v = 0 := by
    unfold HasAnchorSupport at hsupport
    generalize hq : contractedQuadratic P ell = q at hsupport ⊢
    intro v hv
    exact sub_eq_zero.mpr (hanchor v (hsupport v hv))
  calc
    contractedPolynomial C ell = translate (C - P) (contractedPolynomial P ell) := by
      rw [translate_contractedPolynomial, hpoint]
    _ = translate (C - P) (contractedQuadratic P ell) :=
      congrArg (translate (C - P)) (contractedPolynomial_eq_quadratic P ell hP hL)
    _ = contractedQuadratic P ell :=
      translate_eq_self_of_vars_zero (C - P) (contractedQuadratic P ell) hzero

/-- The native scalar identity at an arbitrary ambient point is the quadratic
evaluated on its displacement from P; anchor matching is not needed here. -/
theorem contractedF_eq_quadratic_displacement
    (P : Ambient) (ell : Weights)
    (hP : ∀ r, eval P (row r) = 0)
    (hL : ∀ c : Fin 1053,
      ∑ r, ell r * equationLinearMatrix (translatedRow P) r c = 0)
    (C : Ambient) :
    contractedF ell C = eval (C - P) (contractedQuadratic P ell) := by
  have hpoint : P + (C - P) = C := by rw [add_comm, sub_add_cancel]
  simpa only [hpoint] using contractedF_add_eq_quadratic P ell hP hL (C - P)

/-- Every ambient perturbation at an anchor-matching point is governed by the
same quadratic. In particular W may move all selected anchors. -/
theorem contractedF_add_eq_quadratic_at_anchor
    (P : Ambient) (ell : Weights) (i : Fin 4)
    (hP : ∀ r, eval P (row r) = 0)
    (hL : ∀ c : Fin 1053,
      ∑ r, ell r * equationLinearMatrix (translatedRow P) r c = 0)
    (hsupport : HasAnchorSupport P ell i)
    (C : Ambient) (hanchor : ∀ v, AnchorCoordinate i v → C v = P v)
    (W : Ambient) :
    contractedF ell (C + W) = eval W (contractedQuadratic P ell) := by
  have h := congrArg (eval W)
    (contractedPolynomial_eq_quadratic_at_anchor P ell i hP hL hsupport C hanchor)
  simpa only [contractedPolynomial, contractedF, map_sum, smul_eval,
    translatedRow, eval_translate_at_point] using h

/-- Exact quadratic dependence on an unrestricted ambient line through C.
The absence of a linear term follows from homogeneity as well as support. -/
theorem contractedF_line_eq_quadratic_at_anchor
    (P : Ambient) (ell : Weights) (i : Fin 4)
    (hP : ∀ r, eval P (row r) = 0)
    (hL : ∀ c : Fin 1053,
      ∑ r, ell r * equationLinearMatrix (translatedRow P) r c = 0)
    (hsupport : HasAnchorSupport P ell i)
    (C : Ambient) (hanchor : ∀ v, AnchorCoordinate i v → C v = P v)
    (W : Ambient) (t : ℂ) :
    contractedF ell (C + t • W) = t ^ 2 * eval W (contractedQuadratic P ell) := by
  rw [contractedF_add_eq_quadratic_at_anchor P ell i hP hL hsupport C hanchor]
  exact eval_homogeneous_quadratic_smul (contractedQuadratic P ell)
    (equationAnnihilatorQuadric_isHomogeneous (translatedRow P) ell) W t

private theorem finite_columns_annihilated_of_quadratic {ι : Type*} [Fintype ι]
    (g : ι → Poly) (ell : ι → ℂ) (q : Poly) (hq : q.IsHomogeneous 2)
    (heq : (∑ r, ell r • g r) = q) (c : Fin 1053) :
    ∑ r, ell r * equationLinearMatrix g r c = 0 := by
  classical
  have hcoeff := congrArg (fun p : Poly => p.coeff (Finsupp.single c 1)) heq
  have hquad : q.coeff (Finsupp.single c 1) = 0 := hq.coeff_eq_zero (by simp)
  rw [hquad] at hcoeff
  simpa only [equationLinearMatrix, coeff_sum, coeff_smul, smul_eq_mul] using hcoeff

/-- Every one of the literal original-F linear Taylor columns is annihilated
at C. This is full ambient first-order annihilation, not only tangent-to-slice
annihilation, and F(C)=0 is not a hypothesis. -/
theorem all_columns_annihilated_at_anchor
    (P : Ambient) (ell : Weights) (i : Fin 4)
    (hP : ∀ r, eval P (row r) = 0)
    (hL : ∀ c : Fin 1053,
      ∑ r, ell r * equationLinearMatrix (translatedRow P) r c = 0)
    (hsupport : HasAnchorSupport P ell i)
    (C : Ambient) (hanchor : ∀ v, AnchorCoordinate i v → C v = P v)
    (c : Fin 1053) :
    ∑ r, ell r * equationLinearMatrix (translatedRow C) r c = 0 := by
  exact finite_columns_annihilated_of_quadratic (translatedRow C) ell
    (contractedQuadratic P ell)
    (equationAnnihilatorQuadric_isHomogeneous (translatedRow P) ell)
    (contractedPolynomial_eq_quadratic_at_anchor P ell i hP hL hsupport C hanchor) c

end Option2.NativeStress.AnchorSupport

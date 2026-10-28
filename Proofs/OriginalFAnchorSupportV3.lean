module

public import NativeConfigurationPolynomialDegree
public import Mathlib.Algebra.MvPolynomial.Variables

@[expose] public section

/-!
First-party composition of the accepted original-F degree bound and
the existing PolynomialJets quadratic decomposition/annihilator API. No new
four-case expansion, row-support premise, nonlinear identity assumption, native
covector certificate, analytic derivative or geometric reanchoring is supplied.

The imported degree theorem is over C, matching the native H covectors. The
real-cast importing Consumer makes the compact-real domain explicit. Quadratic
support below is support in AMBIENT VARIABLES of the contracted polynomial.
-/

noncomputable section

namespace Option2.NativeStress.AnchorSupport

open scoped BigOperators
open MvPolynomial PolynomialJets
open NativePolynomial.ConfigurationResiduals
open ConfigurationResidualIndices

abbrev Ambient := Fin 1053 → ℂ
abbrev Weights := Fin 2184 → ℂ
abbrev Poly := MvPolynomial (Fin 1053) ℂ

/-- The existing original numbered residual, at the actual normalization. -/
def row (r : Fin 2184) : Poly :=
  NativePolynomial.ConfigurationResiduals.fRow (1 / 2 : ℂ) (1 / 3 : ℂ) r

def translatedRow (P : Ambient) (r : Fin 2184) : Poly := translate P (row r)

def contractedF (ell : Weights) (X : Ambient) : ℂ :=
  ∑ r, ell r * eval X (row r)

def contractedPolynomial (P : Ambient) (ell : Weights) : Poly :=
  ∑ r, ell r • translatedRow P r

/-- The ACTUAL weighted degree-two part; no reduced tangent table is substituted. -/
def contractedQuadratic (P : Ambient) (ell : Weights) : Poly :=
  equationAnnihilatorQuadric (translatedRow P) ell

/-- Actual anchor frames 0 and 1+3i,2+3i,3+3i, with all81 coordinates per frame. -/
def AnchorCoordinate (i : Fin 4) (v : Fin 1053) : Prop :=
  v.val / 81 = 0 ∨ (1 + 3 * i.val ≤ v.val / 81 ∧ v.val / 81 ≤ 3 + 3 * i.val)

/-- Bind the arithmetic selector to the existing point-first and frame labels. -/
theorem anchorCoordinate_at_native_index
    (i : Fin 4) (f : Fin 13) (a : Fin 3) (k : Fin 27) :
    AnchorCoordinate i (variableIndex (framePointIndex f a) k) ↔
      f.val = 0 ∨ (1 + 3 * i.val ≤ f.val ∧ f.val ≤ 3 + 3 * i.val) := by
  have hi : (27 * (3 * f.val + a.val) + k.val) / 81 = f.val := by omega
  simp only [AnchorCoordinate, variableIndex_val, framePointIndex_val, hi]

/-- This is the contracted-variable-support hypothesis, not row support. -/
def HasAnchorSupport (P : Ambient) (ell : Weights) (i : Fin 4) : Prop :=
  ∀ v ∈ (contractedQuadratic P ell).vars, AnchorCoordinate i v

private theorem eval_translate_at (P V : Ambient) (p : Poly) :
    eval V (translate P p) = eval (P + V) p := by
  rw [translate, ← MvPolynomial.eval_assoc]
  have hpoint : (eval V ∘ (fun j => X j + C (P j))) = P + V := by
    funext j
    simp only [Function.comp_apply, map_add, eval_X, eval_C, Pi.add_apply]
    exact add_comm _ _
  rw [hpoint]

private theorem coeff_zero_translatedRow (P : Ambient) (r : Fin 2184) :
    (translatedRow P r).coeff 0 = eval P (row r) := by
  change constantCoeff (translate P (row r)) = _
  rw [← MvPolynomial.eval_zero]
  simpa only [add_zero] using eval_translate_at P 0 (row r)

/-- An actual solution has the existing exact linear-plus-quadratic expansion.
The degree bound is proved upstream for the literal rows, not a caller premise. -/
theorem translatedRow_eq_linear_add_quadratic
    (P : Ambient) (hP : ∀ r, eval P (row r) = 0) (r : Fin 2184) :
    translatedRow P r = homogeneousComponent 1 (translatedRow P r) +
      homogeneousComponent 2 (translatedRow P r) := by
  apply quadratic_eq_linear_add_quadratic
  · exact translated_fRow_totalDegree_le_two (1 / 2 : ℂ) (1 / 3 : ℂ) P r
  · rw [coeff_zero_translatedRow, hP]

/-- The nonlinear contracted identity is a CONCLUSION from the actual full
linear annihilator and degree-two rows. No such identity is assumed. -/
theorem contractedPolynomial_eq_quadratic
    (P : Ambient) (ell : Weights) (hP : ∀ r, eval P (row r) = 0)
    (hL : ∀ c : Fin 1053,
      ∑ r, ell r * equationLinearMatrix (translatedRow P) r c = 0) :
    contractedPolynomial P ell = contractedQuadratic P ell := by
  classical
  unfold contractedPolynomial contractedQuadratic equationAnnihilatorQuadric
  calc
    (∑ r, ell r • translatedRow P r) =
        ∑ r, ell r • (homogeneousComponent 1 (translatedRow P r) +
          homogeneousComponent 2 (translatedRow P r)) := by
      apply Finset.sum_congr rfl
      intro r _
      exact congrArg (fun p : Poly => ell r • p)
        (translatedRow_eq_linear_add_quadratic P hP r)
    _ = (∑ r, ell r • homogeneousComponent 1 (translatedRow P r)) +
        ∑ r, ell r • homogeneousComponent 2 (translatedRow P r) := by
      simp only [smul_add, Finset.sum_add_distrib]
    _ = ∑ r, ell r • homogeneousComponent 2 (translatedRow P r) := by
      rw [annihilator_linearCombination_eq_zero (translatedRow P) ell hL, zero_add]

/-- The same identity evaluated at every ambient perturbation. -/
theorem contractedF_add_eq_quadratic
    (P : Ambient) (ell : Weights) (hP : ∀ r, eval P (row r) = 0)
    (hL : ∀ c : Fin 1053,
      ∑ r, ell r * equationLinearMatrix (translatedRow P) r c = 0)
    (V : Ambient) :
    contractedF ell (P + V) = eval V (contractedQuadratic P ell) := by
  have h := congrArg (eval V) (contractedPolynomial_eq_quadratic P ell hP hL)
  simpa only [contractedPolynomial, contractedF, map_sum, smul_eval,
    translatedRow, eval_translate_at] using h

/-- Full nonlinear residual contraction depends only on the specified anchors
after the actual linear annihilation and contracted quadratic support are given. -/
theorem contractedF_eq_of_anchor_eq
    (P : Ambient) (ell : Weights) (i : Fin 4)
    (hP : ∀ r, eval P (row r) = 0)
    (hL : ∀ c : Fin 1053,
      ∑ r, ell r * equationLinearMatrix (translatedRow P) r c = 0)
    (hsupport : HasAnchorSupport P ell i)
    (U V : Ambient) (hanchors : ∀ v, AnchorCoordinate i v → U v = V v) :
    contractedF ell (P + U) = contractedF ell (P + V) := by
  rw [contractedF_add_eq_quadratic P ell hP hL U,
    contractedF_add_eq_quadratic P ell hP hL V]
  unfold HasAnchorSupport at hsupport
  generalize hq : contractedQuadratic P ell = q at hsupport ⊢
  have hvars : ∀ v : Fin 1053, v ∈ q.vars → U v = V v := by
    intro v hv
    have ha : AnchorCoordinate i v := hsupport v hv
    exact hanchors v ha
  exact MvPolynomial.eval₂Hom_congr'
    (f₁ := RingHom.id ℂ) (f₂ := RingHom.id ℂ)
    (g₁ := U) (g₂ := V) (p₁ := q) (p₂ := q)
    rfl (fun v hv _ => hvars v hv) rfl

/-- In particular it is exactly zero on the whole actual anchor-fixed affine
slice. This is a polynomial statement; no analyticity or sheet hypothesis. -/
theorem contractedF_eq_zero_on_anchor_fixed
    (P : Ambient) (ell : Weights) (i : Fin 4)
    (hP : ∀ r, eval P (row r) = 0)
    (hL : ∀ c : Fin 1053,
      ∑ r, ell r * equationLinearMatrix (translatedRow P) r c = 0)
    (hsupport : HasAnchorSupport P ell i)
    (V : Ambient) (hanchor : ∀ v, AnchorCoordinate i v → V v = 0) :
    contractedF ell (P + V) = 0 := by
  have h := contractedF_eq_of_anchor_eq P ell i hP hL hsupport V 0 hanchor
  simpa only [add_zero, contractedF, hP, mul_zero, Finset.sum_const_zero] using h

end Option2.NativeStress.AnchorSupport

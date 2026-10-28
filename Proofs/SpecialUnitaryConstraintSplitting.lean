module

public import UEBDeterminantDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

@[expose] public section

/-!
The literal SU3 constraint differential at identity and its explicit normal
splitting. The target is the actual Hermitian part of Mat together with a real
determinant-imaginary coordinate, expressed by exact raw-matrix identities.
No rank, surjectivity, tangent representation or local-chart premise is assumed.
This is a regular-level-set ingredient, not an implicit-function or manifold result.
First-party composition of the accepted determinant owner and pinned mathlib APIs;
no upstream proof body copied. Thanks to the Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, 1676. https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
namespace UnitaryErrorBases.SpecialUnitaryConstraints

/-- The actual unitary Gram constraint and imaginary determinant coordinate. -/
def constraintMap (Q : Mat) : Mat × ℝ := (Q.conjTranspose * Q, Q.det.im)

private def traceCLM : Mat →L[ℝ] ℂ :=
  (Matrix.traceLinearMap Index ℝ ℂ).toContinuousLinearMap

/-- The real continuous-linear constraint differential at the identity. -/
def constraintDifferential : Mat →L[ℝ] Mat × ℝ :=
  (((starL' ℝ : Mat ≃L[ℝ] Mat) : Mat →L[ℝ] Mat) + ContinuousLinearMap.id ℝ Mat).prod
    (Complex.imCLM.comp (Matrix.traceLinearMap Index ℝ ℂ).toContinuousLinearMap)

theorem constraintDifferential_apply (A : Mat) :
    constraintDifferential A = (A.conjTranspose + A, (Matrix.trace A).im) := rfl

private def entry (i j : Index) : Mat →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Index => ℂ) j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Index => Index → ℂ) i)

private theorem gram_hasFDerivAt_one :
    HasFDerivAt (fun Q : Mat => Q.conjTranspose * Q)
      (((starL' ℝ : Mat ≃L[ℝ] Mat) : Mat →L[ℝ] Mat) + ContinuousLinearMap.id ℝ Mat)
      (1 : Mat) := by
  apply hasFDerivAt_pi'.mpr
  intro i
  apply hasFDerivAt_pi'.mpr
  intro j
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    ((entry k i).hasFDerivAt (x := (1 : Mat))).star.mul
      ((entry k j).hasFDerivAt (x := (1 : Mat))))
  convert h using 1
  · rfl
  · ext A
    change star (A j i) + A i j =
      ∑ k : Index, (star ((1 : Mat) k i) * A k j + (1 : Mat) k j * star (A k i))
    simp [Matrix.one_apply, Finset.sum_add_distrib, add_comm]

/-- The derivative of the exact ambient constraint map, with no unitary assumption. -/
theorem constraintMap_hasFDerivAt_one :
    HasFDerivAt constraintMap constraintDifferential (1 : Mat) := by
  have hdet := ArchitectureUEBDerivative.hasFDerivAt_det (1 : Mat)
  have heq : ArchitectureUEBDerivative.detMultilinear.linearDeriv (1 : Mat) = traceCLM := by
    exact ContinuousLinearMap.ext fun (A : Mat) => by
      change ArchitectureUEBDerivative.detMultilinear.linearDeriv (1 : Mat) A = Matrix.trace A
      simpa only [Matrix.conjTranspose_one, Matrix.one_mul] using
        ArchitectureUEBDerivative.detDerivative_apply_of_specialUnitary
          (1 : Mat) A (by simp [IsSpecialUnitary])
  rw [heq] at hdet
  exact gram_hasFDerivAt_one.prodMk (Complex.imCLM.hasFDerivAt.comp (1 : Mat) hdet)

/-- The ambient real derivative has precisely the usual traceless skew-Hermitian kernel. -/
theorem constraintDifferential_kernel (A : Mat) :
    constraintDifferential A = 0 ↔ A.conjTranspose = -A ∧ Matrix.trace A = 0 := by
  rw [constraintDifferential_apply, Prod.mk_eq_zero]
  constructor
  · rintro ⟨hg, hi⟩
    have hs : A.conjTranspose = -A := eq_neg_of_add_eq_zero_left hg
    have ht : star (Matrix.trace A) = -(Matrix.trace A) := by
      rw [← Matrix.trace_conjTranspose, hs, Matrix.trace_neg]
    have hre : (Matrix.trace A).re = 0 := by
      have h := congrArg Complex.re ht
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h
      linarith
    exact ⟨hs, Complex.ext hre hi⟩
  · rintro ⟨hs, ht⟩
    simp [hs, ht]

/-- The explicit normal preimage for a Hermitian matrix and a real coordinate. -/
def constraintNormal (H : Mat) (r : ℝ) : Mat :=
  (1 / 2 : ℝ) • H + (Complex.I * (r / 3 : ℝ)) • (1 : Mat)

/-- The differential always lands in actual Hermitian matrices times the reals. -/
theorem constraintDifferential_isHermitian (A : Mat) :
    (constraintDifferential A).1.IsHermitian := by
  rw [constraintDifferential_apply]
  exact Matrix.isHermitian_transpose_add_self A

/-- Exact right inverse on the actual Hermitian target; no surjectivity premise. -/
theorem constraintDifferential_normal (H : Mat) (hH : H.IsHermitian) (r : ℝ) :
    constraintDifferential (constraintNormal H r) = (H, r) := by
  have him : (Matrix.trace H).im = 0 := by
    have ht : star (Matrix.trace H) = Matrix.trace H := by
      rw [← Matrix.trace_conjTranspose, hH.eq]
    have h := congrArg Complex.im ht
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  rw [constraintDifferential_apply]
  apply Prod.ext
  · change (constraintNormal H r).conjTranspose + constraintNormal H r = H
    simp only [constraintNormal, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      hH.eq, star_trivial, Matrix.conjTranspose_one, star_mul, Complex.star_def,
      Complex.conj_I, Complex.conj_ofReal]
    module
  · change (Matrix.trace (constraintNormal H r)).im = r
    simp [constraintNormal, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
      Index, him, Complex.mul_im]

/-- A precise raw-matrix surjectivity statement onto the Hermitian target. -/
theorem constraintDifferential_range :
    Set.range constraintDifferential = {p : Mat × ℝ | p.1.IsHermitian} := by
  ext p
  constructor
  · rintro ⟨A, rfl⟩
    exact constraintDifferential_isHermitian A
  · intro hp
    exact ⟨constraintNormal p.1 p.2, constraintDifferential_normal p.1 hp p.2⟩

/-- Subtracting the explicit normal component leaves exactly a traceless
skew-Hermitian matrix, giving the actual tangent/normal splitting. -/
theorem constraintNormal_remainder (A : Mat) :
    let T := A - constraintNormal (constraintDifferential A).1 (constraintDifferential A).2
    T.conjTranspose = -T ∧ Matrix.trace T = 0 := by
  apply (constraintDifferential_kernel _).mp
  rw [map_sub, constraintDifferential_normal _ (constraintDifferential_isHermitian A)]
  exact sub_self _

end UnitaryErrorBases.SpecialUnitaryConstraints

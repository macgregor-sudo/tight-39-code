module

public import ThreeCycleNormalizedDifferential
public import UEBDeterminantDerivative
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

/-!
# Recovering actual special-unitary curve tangents

Differentiate the original unitary and determinant-one
equations, then reuse the frozen actual normalized-family differential. The
curve domain is the original special-unitary subtype at every real time.
No skew, trace, represented-velocity, solution or manifold premise is supplied.
No quotient charts or analytic immersion are declared.

First-party composition of the frozen ThreeCycleNormalizedDifferential and
the cached UEBDeterminantDerivative owner (source SHA256
5ba3ab08dc051b57f985258e9f88eb3a5c4b277a63288ac70b96298bdc145dee).
Only public declarations are used; no upstream proof body is copied.
Imported owners retain their provenance and licenses. Thanks to the native-model,
CKM, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
open scoped Matrix.Norms.Elementwise

namespace UnitaryErrorBases.ThreeCycleNormalized

private lemma gramCurve_hasDerivAt {Q : ℝ → Mat} {V : Mat} {t : ℝ}
    (hQ : HasDerivAt Q V t) :
    HasDerivAt (fun s => (Q s).conjTranspose * Q s)
      (V.conjTranspose * Q t + (Q t).conjTranspose * V) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp hQ k) i).star.mul
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hQ k) j))
  simpa only [Matrix.mul_apply, Matrix.add_apply, Matrix.conjTranspose_apply,
    Finset.sum_add_distrib, Pi.mul_apply] using h

/-- Every actual special-unitary curve derivative has the uniquely represented
form `Q * A` with `A = Q† * V`, and its skew/trace constraints are consequences
of the original equations rather than additional caller hypotheses. -/
theorem specialUnitaryCurve_tangent
    (Q : ℝ → {M : Mat // IsSpecialUnitary M}) (V : Mat) (t : ℝ)
    (hQ : HasDerivAt (fun s => (Q s).val) V t) :
    V = (Q t).val * ((Q t).val.conjTranspose * V) ∧
      ((Q t).val.conjTranspose * V).conjTranspose = -((Q t).val.conjTranspose * V) ∧
      Matrix.trace ((Q t).val.conjTranspose * V) = 0 := by
  have hunit : (Q t).val * (Q t).val.conjTranspose = 1 :=
    mul_eq_one_comm.mp (Q t).property.1
  have hrep : V = (Q t).val * ((Q t).val.conjTranspose * V) := by
    rw [← Matrix.mul_assoc, hunit, Matrix.one_mul]
  have hgram := gramCurve_hasDerivAt hQ
  have hgramfun : (fun s => (Q s).val.conjTranspose * (Q s).val) =
      (fun _ : ℝ => (1 : Mat)) := funext fun s => (Q s).property.1
  rw [hgramfun] at hgram
  have hgramzero := hgram.unique (hasDerivAt_const t (1 : Mat))
  have hskew : ((Q t).val.conjTranspose * V).conjTranspose =
      -((Q t).val.conjTranspose * V) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    exact eq_neg_of_add_eq_zero_left hgramzero
  have hdet := (ArchitectureUEBDerivative.hasFDerivAt_det (Q t).val).comp_hasDerivAt t hQ
  have hdetfun : (fun s => Matrix.det (Q s).val) = (fun _ : ℝ => (1 : ℂ)) :=
    funext fun s => (Q s).property.2
  change HasDerivAt (fun s => Matrix.det (Q s).val)
    (ArchitectureUEBDerivative.detMultilinear.linearDeriv (Q t).val V) t at hdet
  rw [ArchitectureUEBDerivative.detDerivative_apply_of_specialUnitary
    (Q t).val V (Q t).property, hdetfun] at hdet
  exact ⟨hrep, hskew, hdet.unique (hasDerivAt_const t (1 : ℂ))⟩

/-- The real derivative of the same normalized family along actual constrained
curves, with only the ordinary coordinate-derivative assumptions. -/
theorem normalizedFamily_hasDerivAt_of_specialUnitaryCurve
    (Q : ℝ → {M : Mat // IsSpecialUnitary M}) (d : ℝ → PhaseTriple)
    (V : Mat) (v : Index → ℂ) (t : ℝ)
    (hQ : HasDerivAt (fun s => (Q s).val) V t)
    (hd : HasDerivAt (fun s => (d s).val) v t) :
    HasDerivAt (fun s => normalizedFamily (Q s).val (d s))
      (normalizedVelocity (Q t).val (d t) ((Q t).val.conjTranspose * V) v) t := by
  obtain ⟨hrep, hskew, _⟩ := specialUnitaryCurve_tangent Q V t hQ
  apply normalizedFamily_hasDerivAt (fun s => (Q s).val) d _ v t _ hd hskew
  rwa [← hrep]

/-- Zero family derivative forces both actual coordinate velocities to vanish.
All former skew/trace/represented-velocity premises have been derived above. -/
theorem normalizedFamily_zero_derivative_of_specialUnitaryCurve
    (Q : ℝ → {M : Mat // IsSpecialUnitary M}) (d : ℝ → PhaseTriple)
    (V : Mat) (v : Index → ℂ) (t : ℝ)
    (hQ : HasDerivAt (fun s => (Q s).val) V t)
    (hd : HasDerivAt (fun s => (d s).val) v t)
    (hzero : HasDerivAt (fun s => normalizedFamily (Q s).val (d s)) 0 t) :
    V = 0 ∧ v = 0 := by
  obtain ⟨hrep, hskew, htrace⟩ := specialUnitaryCurve_tangent Q V t hQ
  have hQ' : HasDerivAt (fun s => (Q s).val)
      ((Q t).val * ((Q t).val.conjTranspose * V)) t := by rwa [← hrep]
  obtain ⟨hA, hv⟩ := normalizedFamily_zero_derivative_recovers_velocity
    (fun s => (Q s).val) d ((Q t).val.conjTranspose * V) v t
    (Q t).property hQ' hd hskew htrace hzero
  refine ⟨?_, hv⟩
  simpa only [hA, Matrix.mul_zero] using hrep

end UnitaryErrorBases.ThreeCycleNormalized

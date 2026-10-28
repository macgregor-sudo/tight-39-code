module

public import EuclideanUpperBoundActual
public import EuclideanLowerBound
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

@[expose] public section

/-! Normalization of Mathlib's actual small inductive dimension on Euclidean
spaces and every nonempty open Euclidean subtype. The upper proof uses actual
D2 closed sums; the lower proof uses actual dimension-lowering separators and
Brouwer cube separation. No dimension contract remains in these endpoints.

-/
noncomputable section
namespace SmallInductiveEuclideanA7
open Set

/-- Euclidean normalization, including the nonempty zero-dimensional space. -/
theorem euclidean_smallInductiveDimension_eq (n : ℕ) :
    smallInductiveDimension (EuclideanSpace ℝ (Fin n)) = (n : WithBot ℕ∞) :=
  le_antisymm (euclidean_smallInductiveDimension_upper_bound n)
    (euclidean_smallInductiveDimension_lower_bound n)

/-- Positive-radius open Euclidean balls retain the ambient dimension. -/
theorem euclidean_ball_smallInductiveDimension_eq (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    smallInductiveDimension ↥(Metric.ball x r) = (n : WithBot ℕ∞) := by
  let e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
    OpenPartialHomeomorph.univBall x r
  have hs : e.source = Set.univ := OpenPartialHomeomorph.univBall_source x r
  have ht : e.target = Metric.ball x r := OpenPartialHomeomorph.univBall_target x hr
  calc
    smallInductiveDimension ↥(Metric.ball x r) = smallInductiveDimension ↥e.target :=
      (Homeomorph.setCongr ht).smallInductiveDimension_congr.symm
    _ = smallInductiveDimension ↥e.source := e.toHomeomorphSourceTarget.smallInductiveDimension_congr.symm
    _ = smallInductiveDimension (EuclideanSpace ℝ (Fin n)) := by
      rw [hs]
      exact (Homeomorph.Set.univ _).smallInductiveDimension_congr
    _ = (n : WithBot ℕ∞) := euclidean_smallInductiveDimension_eq n

/-- Every nonempty open Euclidean subspace has exactly the ambient small
inductive dimension. No homogeneity/locality theorem is assumed: a positive
ball sits inside it and supplies the lower bound by actual subspace monotonicity. -/
theorem euclidean_open_smallInductiveDimension_eq (n : ℕ)
    (A : Set (EuclideanSpace ℝ (Fin n))) (hA : IsOpen A) (hne : A.Nonempty) :
    smallInductiveDimension A = (n : WithBot ℕ∞) := by
  apply le_antisymm (euclidean_subtype_smallInductiveDimension_upper_bound n A)
  obtain ⟨x,hx⟩ := hne
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.1 (hA.mem_nhds hx)
  have hle : smallInductiveDimension ↥(Metric.ball x r) ≤ smallInductiveDimension A :=
    (Topology.IsEmbedding.inclusion hball).toIsInducing.smallInductiveDimension_le
  rwa [euclidean_ball_smallInductiveDimension_eq n x hr] at hle

#print axioms euclidean_smallInductiveDimension_eq
#print axioms euclidean_ball_smallInductiveDimension_eq
#print axioms euclidean_open_smallInductiveDimension_eq
end SmallInductiveEuclideanA7

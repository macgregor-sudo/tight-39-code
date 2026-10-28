module

public import FiniteOrbitTypeCover
public import MetricDimensionLocality

@[expose] public section

/-! The needed finite-isometric quotient upper bound for actual small inductive
dimension. Local isometric charts bound each quotient stratum, then the finite
locally-closed cover gives the quotient bound. No alternative dimension notion
or unproved dimension-preservation assumption occurs. -/
noncomputable section
namespace FiniteIsometricStrata
open TopologicalSpace
variable {G X : Type*} [Group G] [Finite G] [MetricSpace X]
  [MulAction G X] [IsIsometricSMul G X] [SecondCountableTopology X]

theorem quotientStratum_dimension_le (H : Subgroup G) (n : ℕ)
    (hdim : HasSmallInductiveDimensionLE X n) :
    HasSmallInductiveDimensionLE (quotientStratum (X := X) H) n := by
  letI : SecondCountableTopology (OrbitQuotient G X) :=
    Topology.IsOpenQuotientMap.secondCountableTopology
      (MulAction.isOpenQuotientMap_quotientMk (Γ := G) (T := X))
  apply SmallInductiveClosedSum.dimension_le_of_open_neighborhoods n
  intro q
  obtain ⟨p, hp, hpq⟩ := q.2
  obtain ⟨r, hr, f, hfval, hf, hfo⟩ := quotient_stratum_local_isometry_open_range H p hp
  let p' : (exactStabilizerSet H ∩ Metric.ball p r : Set X) :=
    ⟨p, hp, Metric.mem_ball_self hr⟩
  have hfp : f p' = q := Subtype.ext ((hfval p').trans hpq)
  refine ⟨Set.range f, hfo, ⟨p', hfp⟩, ?_⟩
  have hdomain : HasSmallInductiveDimensionLE
      (exactStabilizerSet H ∩ Metric.ball p r : Set X) n :=
    Topology.IsInducing.subtypeVal.hasSmallInductiveDimensionLE hdim
  exact (hf.isometryEquivOnRange.toHomeomorph.hasSmallInductiveDimensionLE n).mp hdomain

/-- Finite isometric orbit quotients cannot increase small inductive dimension
in a second-countable metric space. The quotient metric has the actual quotient topology. -/
theorem finite_isometric_quotient_dimension_le (n : ℕ)
    (hdim : HasSmallInductiveDimensionLE X n) :
    HasSmallInductiveDimensionLE (OrbitQuotient G X) n := by
  letI : SecondCountableTopology (OrbitQuotient G X) :=
    Topology.IsOpenQuotientMap.secondCountableTopology
      (MulAction.isOpenQuotientMap_quotientMk (Γ := G) (T := X))
  exact SmallInductiveClosedSum.countable_locallyClosed_cover n
    (quotientStratum (X := X)) isLocallyClosed_quotientStratum
    (fun H => quotientStratum_dimension_le H n hdim) quotientStratum_cover

#print axioms quotientStratum_dimension_le
#print axioms finite_isometric_quotient_dimension_le
end FiniteIsometricStrata

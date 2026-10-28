module

public import ThreeCycleNormalizedProjectiveUnitary
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Covering.Quotient

@[expose] public section

/-!
Finiteness and local lifts for the literal standard special-unitary center quotient.
This composes the retained actual-center classification with pinned mathlib APIs;
no topology, group, center relation, analytic chart or manifold is postulated.
First-party composition; no upstream implementation is copied.
Thanks to the Lean and mathlib contributors; imported notices remain theirs.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, 1676. https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
namespace UnitaryErrorBases.ThreeCycleNormalized

/-- The full center of the actual standard group is finite. -/
theorem finite_standard_center :
    Set.Finite (Subgroup.center StandardSpecialUnitary : Set StandardSpecialUnitary) := by
  classical
  have hroots : Set.Finite {c : ℂ | c ^ 3 = 1} := by
    convert (Polynomial.nthRoots 3 (1 : ℂ)).toFinset.finite_toSet using 1
    ext c
    simp only [Finset.mem_coe, Multiset.mem_toFinset,
      Polynomial.mem_nthRoots (by decide : 0 < 3), Set.mem_ofPred_eq]
  have hmat := hroots.image (fun c : ℂ => c • (1 : Mat))
  apply (hmat.preimage Subtype.val_injective.injOn).subset
  intro Q hQ
  obtain ⟨c, hc, hQc⟩ := (mem_standard_center_iff_scalar Q).mp hQ
  exact ⟨c, hc, hQc.symm⟩

/-- Discreteness uses the inherited matrix/subtype topology. -/
theorem isDiscrete_standard_center :
    IsDiscrete (Subgroup.center StandardSpecialUnitary : Set StandardSpecialUnitary) :=
  finite_standard_center.isDiscrete

-- The standard inverse is conjugate transpose in the existing subtype topology.
local instance : IsTopologicalGroup StandardSpecialUnitary where
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.star

/-- The literal quotient projection is a covering map. -/
theorem isCoveringMap_standard_center_projection :
    IsCoveringMap
      (QuotientGroup.mk : StandardSpecialUnitary → SpecialUnitaryCenterQuotient) :=
  ((Subgroup.center StandardSpecialUnitary).isQuotientCoveringMap
    isDiscrete_standard_center).isCoveringMap

/-- In particular, the literal projection is a local homeomorphism. -/
theorem isLocalHomeomorph_standard_center_projection :
    IsLocalHomeomorph
      (QuotientGroup.mk : StandardSpecialUnitary → SpecialUnitaryCenterQuotient) :=
  isCoveringMap_standard_center_projection.isLocalHomeomorph

/-- A local lift through any chosen actual representative. -/
def standardCenterLocalLift (Q : StandardSpecialUnitary) :
    OpenPartialHomeomorph SpecialUnitaryCenterQuotient StandardSpecialUnitary :=
  isLocalHomeomorph_standard_center_projection.localInverseAt Q

/-- The quotient point lies in the open source of the lift. -/
theorem standardCenterLocalLift_mem_source (Q : StandardSpecialUnitary) :
    QuotientGroup.mk Q ∈ (standardCenterLocalLift Q).source :=
  isLocalHomeomorph_standard_center_projection.apply_self_mem_localInverseAt_source

/-- The lift is a section of the actual quotient projection on its source. -/
theorem standardCenterLocalLift_section (Q : StandardSpecialUnitary)
    (z : SpecialUnitaryCenterQuotient) (hz : z ∈ (standardCenterLocalLift Q).source) :
    QuotientGroup.mk (standardCenterLocalLift Q z) = z :=
  isLocalHomeomorph_standard_center_projection.apply_localInverseAt_of_mem hz

/-- The local lift passes through the specified representative, not just its coset. -/
theorem standardCenterLocalLift_apply_self (Q : StandardSpecialUnitary) :
    standardCenterLocalLift Q (QuotientGroup.mk Q) = Q :=
  isLocalHomeomorph_standard_center_projection.localInverseAt_apply_self

/-- Every actual quotient point has a continuous local section. -/
theorem exists_standard_center_local_section (z : SpecialUnitaryCenterQuotient) :
    ∃ U : Set SpecialUnitaryCenterQuotient, IsOpen U ∧ z ∈ U ∧
      ∃ s : SpecialUnitaryCenterQuotient → StandardSpecialUnitary,
        ContinuousOn s U ∧ ∀ y ∈ U, QuotientGroup.mk (s y) = y := by
  obtain ⟨Q, rfl⟩ := QuotientGroup.mk_surjective z
  exact ⟨(standardCenterLocalLift Q).source, (standardCenterLocalLift Q).open_source,
    standardCenterLocalLift_mem_source Q, standardCenterLocalLift Q,
    (standardCenterLocalLift Q).continuousOn, standardCenterLocalLift_section Q⟩

end UnitaryErrorBases.ThreeCycleNormalized

module

public import FiniteOrbitStratumOpen
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.LocallyClosed

@[expose] public section

/-! Locally closed orbit types via a finite fixed-set/cardinality cutout.
No closure property for arbitrary finite unions of locally closed sets is used.
All quotient statements use the original orbit quotient topology. -/
noncomputable section
namespace FiniteIsometricStrata
variable {G X : Type*} [Group G] [Finite G] [MetricSpace X]
  [MulAction G X] [IsIsometricSMul G X]

def fixedBySubgroup (H : Subgroup G) : Set X := {x | H ≤ MulAction.stabilizer G x}

theorem isClosed_fixedBySubgroup (H : Subgroup G) :
    IsClosed (fixedBySubgroup (X := X) H) := by
  have heq : fixedBySubgroup (X := X) H = ⋂ g : H, {x | g.1 • x = x} := by
    ext x
    simp only [fixedBySubgroup, Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h g => h g.2, fun h g hg => h ⟨g, hg⟩⟩
  rw [heq]
  exact isClosed_iInter fun g => isClosed_eq (continuous_const_smul g.1) continuous_id

def largerStabilizers (n : ℕ) : Set X := {x | n < Nat.card (MulAction.stabilizer G x)}

theorem isClosed_largerStabilizers (n : ℕ) : IsClosed (largerStabilizers (G := G) (X := X) n) := by
  have heq : largerStabilizers (G := G) (X := X) n =
      ⋃ K : {K : Subgroup G // n < Nat.card K}, fixedBySubgroup (X := X) K.1 := by
    ext x
    simp only [largerStabilizers, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hx
      exact ⟨⟨MulAction.stabilizer G x, hx⟩, show MulAction.stabilizer G x ≤ MulAction.stabilizer G x from le_rfl⟩
    · rintro ⟨K, hK⟩
      exact lt_of_lt_of_le K.2 (Subgroup.card_le_of_le hK)
  rw [heq]
  exact isClosed_iUnion_of_finite fun K => isClosed_fixedBySubgroup K.1

theorem stabilizer_card_of_orbitRel {x y : X} (h : MulAction.orbitRel G X x y) :
    Nat.card (MulAction.stabilizer G x) = Nat.card (MulAction.stabilizer G y) := by
  obtain ⟨g, hg⟩ := h
  exact (Nat.card_congr (MulAction.stabilizerEquivStabilizer (G := G) hg.symm).toEquiv).symm

/-- The finite-action projection is closed, because saturating a closed set
is a finite union of closed translates. -/
theorem isClosedMap_orbitQuotient : IsClosedMap (Quotient.mk (MulAction.orbitRel G X)) := by
  intro s hs
  apply (isQuotientMap_quotient_mk').isClosed_preimage.mp
  change IsClosed ((@Quotient.mk' X (MulAction.orbitRel G X)) ⁻¹'
    (@Quotient.mk' X (MulAction.orbitRel G X)) '' s)
  rw [MulAction.quotient_preimage_image_eq_union_mul]
  exact isClosed_iUnion_of_finite fun g => isClosedMap_smul g s hs

/-- The quotient orbit type is a closed fixed-set image minus the closed image
of points with strictly larger stabilizer. -/
theorem quotientStratum_eq_fixed_cutout (H : Subgroup G) :
    quotientStratum (X := X) H =
      Quotient.mk (MulAction.orbitRel G X) '' fixedBySubgroup H \
      Quotient.mk (MulAction.orbitRel G X) '' largerStabilizers (G := G) (Nat.card H) := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : MulAction.stabilizer G x = H := hx
    refine ⟨⟨x, ?_, rfl⟩, ?_⟩
    · change H ≤ MulAction.stabilizer G x
      rw [hx']
    · rintro ⟨y, hy, heq⟩
      have hc := stabilizer_card_of_orbitRel (Quotient.exact heq)
      change Nat.card H < Nat.card (MulAction.stabilizer G y) at hy
      rw [hc, hx'] at hy
      exact (lt_irrefl _ hy)
  · rintro ⟨⟨x, hx, rfl⟩, hnot⟩
    have hcard : Nat.card (MulAction.stabilizer G x) ≤ Nat.card H := by
      by_contra hc
      exact hnot ⟨x, Nat.lt_of_not_ge hc, rfl⟩
    have heq := Subgroup.eq_of_le_of_card_ge hx hcard
    exact ⟨x, heq.symm, rfl⟩

theorem isLocallyClosed_quotientStratum (H : Subgroup G) :
    IsLocallyClosed (quotientStratum (X := X) H) := by
  rw [quotientStratum_eq_fixed_cutout]
  have hA := isClosedMap_orbitQuotient (G := G) (fixedBySubgroup (X := X) H) (isClosed_fixedBySubgroup H)
  have hB := isClosedMap_orbitQuotient (G := G) (largerStabilizers (G := G) (X := X) (Nat.card H))
    (isClosed_largerStabilizers (Nat.card H))
  exact ⟨_, _, hB.isOpen_compl, hA, Set.diff_eq_compl_inter⟩

/-- The full orbit type upstairs, namely the union of all translates of the
exact stabilizer set (equivalently all conjugate stabilizer sets). -/
def orbitType (H : Subgroup G) : Set X :=
  Quotient.mk (MulAction.orbitRel G X) ⁻¹' quotientStratum H

theorem orbitType_eq_union_translates (H : Subgroup G) :
    orbitType (X := X) H = ⋃ g : G, (g • ·) '' exactStabilizerSet H :=
  MulAction.quotient_preimage_image_eq_union_mul _

theorem isLocallyClosed_orbitType (H : Subgroup G) :
    IsLocallyClosed (orbitType (X := X) H) :=
  (isLocallyClosed_quotientStratum H).preimage continuous_quotient_mk'

#print axioms isLocallyClosed_quotientStratum
#print axioms isLocallyClosed_orbitType
end FiniteIsometricStrata

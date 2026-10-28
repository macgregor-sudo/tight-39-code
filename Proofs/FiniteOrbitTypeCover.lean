module

public import FiniteOrbitTypeLocallyClosed

@[expose] public section

/-! Finite relative-clopen stabilizer cover of each orbit type, and finite
locally-closed covers upstairs and downstairs. These are geometric inputs to
dimension locality, not an assertion of a dimension theorem or a finite atlas. -/
noncomputable section
namespace FiniteIsometricStrata
variable {G X : Type*} [Group G] [Finite G] [MetricSpace X]
  [MulAction G X] [IsIsometricSMul G X]

theorem orbitType_stabilizer_card (H : Subgroup G) {x : X}
    (hx : x ∈ orbitType H) : Nat.card (MulAction.stabilizer G x) = Nat.card H := by
  obtain ⟨y, hy, heq⟩ := hx
  have hc := stabilizer_card_of_orbitRel (Quotient.exact heq.symm)
  change MulAction.stabilizer G y = H at hy
  rwa [hy] at hc

theorem isOpen_stabilizer_le (K : Subgroup G) :
    IsOpen {x : X | MulAction.stabilizer G x ≤ K} := by
  have heq : {x : X | MulAction.stabilizer G x ≤ K} =
      ⋂ g : {g : G // g ∉ K}, {x : X | g.1 • x ≠ x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hx g hfix
      exact g.2 (hx hfix)
    · intro hx g hg
      by_contra hn
      exact hx ⟨g, hn⟩ hg
  rw [heq]
  exact isOpen_iInter_of_finite fun g =>
    (isClosed_eq (continuous_const_smul g.1) continuous_id).isOpen_compl

/-- Each exact stabilizer piece is relatively clopen in a fixed conjugacy
orbit type. Subgroups of the wrong conjugacy class simply give empty pieces. -/
theorem isClopen_exact_piece (H K : Subgroup G) (hcard : Nat.card K = Nat.card H) :
    IsClopen {x : orbitType (X := X) H | MulAction.stabilizer G x.1 = K} := by
  have heqClosed : {x : orbitType (X := X) H | MulAction.stabilizer G x.1 = K} =
      Subtype.val ⁻¹' fixedBySubgroup (X := X) K := by
    ext x
    constructor
    · intro hx
      change K ≤ MulAction.stabilizer G x.1
      rw [hx]
    · intro hx
      exact (Subgroup.eq_of_le_of_card_ge hx
        (le_of_eq ((orbitType_stabilizer_card H x.2).trans hcard.symm))).symm
  have heqOpen : {x : orbitType (X := X) H | MulAction.stabilizer G x.1 = K} =
      Subtype.val ⁻¹' {x : X | MulAction.stabilizer G x ≤ K} := by
    ext x
    constructor
    · intro hx
      change MulAction.stabilizer G x.1 ≤ K
      rw [hx]
    · intro hx
      exact Subgroup.eq_of_le_of_card_ge hx
        (le_of_eq (hcard.trans (orbitType_stabilizer_card H x.2).symm))
  exact ⟨heqClosed ▸ (isClosed_fixedBySubgroup K).preimage continuous_subtype_val,
    heqOpen ▸ (isOpen_stabilizer_le K).preimage continuous_subtype_val⟩

/-- This cover is finite because the indexing subgroups belong to a finite group.
It covers by relatively clopen exact-stabilizer pieces, not by finitely many charts. -/
theorem exact_piece_cover (H : Subgroup G) :
    (⋃ K : {K : Subgroup G // Nat.card K = Nat.card H},
      {x : orbitType (X := X) H | MulAction.stabilizer G x.1 = K.1}) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr ⟨⟨MulAction.stabilizer G x.1, orbitType_stabilizer_card H x.2⟩, rfl⟩

theorem quotientStratum_cover :
    (⋃ H : Subgroup G, quotientStratum (X := X) H) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  induction q using Quotient.inductionOn with | h x => ?_
  exact Set.mem_iUnion.mpr ⟨MulAction.stabilizer G x, x, rfl, rfl⟩

theorem orbitType_cover : (⋃ H : Subgroup G, orbitType (X := X) H) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr ⟨MulAction.stabilizer G x, x, rfl, rfl⟩

theorem exactStabilizer_cover : (⋃ H : Subgroup G, exactStabilizerSet (X := X) H) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr ⟨MulAction.stabilizer G x, rfl⟩

#print axioms isClopen_exact_piece
#print axioms exact_piece_cover
#print axioms quotientStratum_cover
end FiniteIsometricStrata

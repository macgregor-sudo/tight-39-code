module

public import ThreeCycleNormalizedParameterHomeomorphism
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

/-!
Concrete center and quotient bridge to mathlib's actual special-unitary group.
The topology, parameter homeomorphism and continuity results are imported.
The actual matrix subtype is identified by unchanged entries and equations;
the group center is proved to be exactly the cubic scalars. Only then is its
group quotient identified homeomorphically with the existing matrix quotient.
No new differential, dimension, native-frame, exhaustion or physics claim.
First-party composition of retained project results and pinned mathlib APIs;
no private clock/shift proof or upstream implementation is copied.
Thanks to the Lean and mathlib contributors; imported notices remain theirs.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, 1676. https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
namespace UnitaryErrorBases.ThreeCycleNormalized

/-- Mathlib's existing special-unitary group on the original cyclic matrix indices. -/
abbrev StandardSpecialUnitary := Matrix.specialUnitaryGroup Index ℂ

/-- The original one-sided Gram convention is exactly standard special-unitarity. -/
theorem isSpecialUnitary_iff_mem_standard (Q : Mat) :
    IsSpecialUnitary Q ↔ Q ∈ Matrix.specialUnitaryGroup Index ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
  rfl

/-- Identity on actual matrix entries, with the standard subtype topologies. -/
def specialUnitaryParameterHomeomorph : SpecialUnitaryParameter ≃ₜ StandardSpecialUnitary where
  toFun Q := ⟨Q.val, (isSpecialUnitary_iff_mem_standard Q.val).mp Q.property⟩
  invFun Q := ⟨Q.val, (isSpecialUnitary_iff_mem_standard Q.val).mpr Q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

private def identityPhases : PhaseTriple := ⟨fun _ => 1, by constructor <;> simp⟩

/-- The full actual special-unitary commutant, proved via the accepted family fibres. -/
theorem commutes_specialUnitary_iff_scalar (Q : Mat) (hQ : IsSpecialUnitary Q) :
    (∀ A : Mat, IsSpecialUnitary A → Q * A = A * Q) ↔
      ∃ c : ℂ, c ^ 3 = 1 ∧ Q = c • (1 : Mat) := by
  constructor
  · intro hcomm
    have hI : IsSpecialUnitary (1 : Mat) := by simp [IsSpecialUnitary]
    have heq : normalizedFamily 1 identityPhases = normalizedFamily Q identityPhases := by
      funext p
      unfold normalizedFamily
      rw [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one,
        hcomm _ (ThreeCycleMatrix.monomialFamily_specialUnitary identityPhases p),
        Matrix.mul_assoc, mul_eq_one_comm.mp hQ.1, Matrix.mul_one]
    exact ((normalizedFamily_eq_iff 1 Q identityPhases identityPhases hI hQ).mp heq).2
  · rintro ⟨c, _hcube, rfl⟩ A _hA
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

/-- The center of the standard group is exactly the scalar cube roots of one. -/
theorem mem_standard_center_iff_scalar (Q : StandardSpecialUnitary) :
    Q ∈ Subgroup.center StandardSpecialUnitary ↔
      ∃ c : ℂ, c ^ 3 = 1 ∧ Q.val = c • (1 : Mat) := by
  constructor
  · intro hcenter
    apply (commutes_specialUnitary_iff_scalar Q.val
      ((isSpecialUnitary_iff_mem_standard Q.val).mpr Q.property)).mp
    intro A hA
    let A' : StandardSpecialUnitary := ⟨A, (isSpecialUnitary_iff_mem_standard A).mp hA⟩
    exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hcenter) A')).symm
  · rintro ⟨c, _hcube, hscalar⟩
    apply Subgroup.mem_center_iff.mpr
    intro A
    apply Subtype.ext
    change A.val * Q.val = Q.val * A.val
    rw [hscalar]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

/-- The existing cyclic-scalar relation is the actual group-center coset relation.
The same scalar c occurs in Q'=cQ and Q⁻¹Q'=cI; its cube remains one. -/
theorem standard_center_relation_iff (Q Q' : SpecialUnitaryParameter) :
    QuotientGroup.leftRel (Subgroup.center StandardSpecialUnitary)
        (specialUnitaryParameterHomeomorph Q) (specialUnitaryParameterHomeomorph Q') ↔
      matrixCentralRelation Q Q' := by
  rw [QuotientGroup.leftRel_apply, mem_standard_center_iff_scalar]
  constructor
  · rintro ⟨c, hcube, hscalar⟩
    refine ⟨c, hcube, ?_⟩
    change Q.val.conjTranspose * Q'.val = c • (1 : Mat) at hscalar
    have h := congrArg (fun A : Mat => Q.val * A) hscalar
    rw [← Matrix.mul_assoc, mul_eq_one_comm.mp Q.property.1, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one] at h
    exact h
  · rintro ⟨c, hcube, hscalar⟩
    refine ⟨c, hcube, ?_⟩
    change Q.val.conjTranspose * Q'.val = c • (1 : Mat)
    rw [hscalar, Matrix.mul_smul, Q.property.1]

/-- The standard group quotient by its proved full center, not a renamed relation. -/
abbrev SpecialUnitaryCenterQuotient :=
  StandardSpecialUnitary ⧸ Subgroup.center StandardSpecialUnitary

/-- Actual quotient-topology identification with the standard group-center quotient. -/
def matrixCentralQuotientHomeomorph : MatrixCentralQuotient ≃ₜ SpecialUnitaryCenterQuotient where
  toEquiv := Quotient.congr specialUnitaryParameterHomeomorph.toEquiv
    (fun Q Q' => (standard_center_relation_iff Q Q').symm)
  continuous_toFun := continuous_quot_map
    (fun Q Q' h => (standard_center_relation_iff Q Q').mpr h)
    specialUnitaryParameterHomeomorph.continuous
  continuous_invFun := continuous_quot_map
    (fun Q Q' h => (standard_center_relation_iff
      (specialUnitaryParameterHomeomorph.symm Q)
      (specialUnitaryParameterHomeomorph.symm Q')).mp h)
    specialUnitaryParameterHomeomorph.symm.continuous

theorem matrixCentralQuotientHomeomorph_mk (Q : SpecialUnitaryParameter) :
    matrixCentralQuotientHomeomorph (Quotient.mk matrixCentralSetoid Q) =
      QuotientGroup.mk (specialUnitaryParameterHomeomorph Q) := rfl

/-- Product coordinates using the actual standard group-center quotient and two circles. -/
def projectiveCircleParameterHomeomorph :
    MatrixCentralQuotient × (Circle × Circle) ≃ₜ SpecialUnitaryCenterQuotient × (Circle × Circle) :=
  matrixCentralQuotientHomeomorph.prodCongr (Homeomorph.refl (Circle × Circle))

/-- The existing family transported to its standard group-center quotient parameters. -/
def projectiveNormalizedFamily : SpecialUnitaryCenterQuotient × (Circle × Circle) → Family :=
  circleParameterizedNormalizedFamily ∘ projectiveCircleParameterHomeomorph.symm

theorem projectiveNormalizedFamily_mk (Q : SpecialUnitaryParameter) (z : Circle × Circle) :
    projectiveNormalizedFamily (QuotientGroup.mk (specialUnitaryParameterHomeomorph Q), z) =
      normalizedFamily Q.val (phaseOfCircles z) := rfl

/-- Transfer of the existing closed embedding to the standard projective parameters. -/
theorem isClosedEmbedding_projectiveNormalizedFamily :
    Topology.IsClosedEmbedding projectiveNormalizedFamily :=
  isClosedEmbedding_circleParameterizedNormalizedFamily.comp
    projectiveCircleParameterHomeomorph.symm.isClosedEmbedding

end UnitaryErrorBases.ThreeCycleNormalized

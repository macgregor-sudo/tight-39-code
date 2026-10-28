module

public import SpecialUnitaryLocalConstraints
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# Actual special-unitary translation of the local constraint equations

Forward translation is exactly Q₀†A and inverse translation
Q₀B, for an actual standard special-unitary Q₀. Existing matrix norms/topologies
are retained. The identity's explicit open defining-equation neighborhood is
transported through this proved analytic two-sided map. No nonlinear chart,
Lie manifold, implicit-function result or immersion is assumed or asserted.
First-party composition of admitted constraints and pinned linear/analytic APIs.
Imported owners retain their notices; no upstream proof body copied. Thanks to
the contributors. “If I have seen further it is by standing on the sholders of
Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
open scoped Matrix.Norms.Elementwise Topology
namespace UnitaryErrorBases.ThreeCycleNormalized

/-- Actual matrix translation to the identity, with its exact matrix inverse. -/
def specialUnitaryLeftTranslation (Q₀ : StandardSpecialUnitary) : Mat ≃L[ℝ] Mat :=
  ({ toFun := fun A => Q₀.val.conjTranspose * A
     invFun := fun B => Q₀.val * B
     left_inv := by
       intro A
       change Q₀.val * (Q₀.val.conjTranspose * A) = A
       have h := (isSpecialUnitary_iff_mem_standard Q₀.val).mpr Q₀.property
       rw [← Matrix.mul_assoc, mul_eq_one_comm.mp h.1, Matrix.one_mul]
     right_inv := by
       intro B
       change Q₀.val.conjTranspose * (Q₀.val * B) = B
       have h := (isSpecialUnitary_iff_mem_standard Q₀.val).mpr Q₀.property
       rw [← Matrix.mul_assoc, h.1, Matrix.one_mul]
     map_add' := by intro A B; exact Matrix.mul_add _ _ _
     map_smul' := by intro r A; exact Matrix.mul_smul _ _ _
   } : Mat ≃ₗ[ℝ] Mat).toContinuousLinearEquiv

theorem specialUnitaryLeftTranslation_apply (Q₀ : StandardSpecialUnitary) (A : Mat) :
    specialUnitaryLeftTranslation Q₀ A = Q₀.val.conjTranspose * A := rfl

theorem specialUnitaryLeftTranslation_symm_apply (Q₀ : StandardSpecialUnitary) (B : Mat) :
    (specialUnitaryLeftTranslation Q₀).symm B = Q₀.val * B := rfl

theorem specialUnitaryLeftTranslation_apply_self (Q₀ : StandardSpecialUnitary) :
    specialUnitaryLeftTranslation Q₀ Q₀.val = 1 :=
  ((isSpecialUnitary_iff_mem_standard Q₀.val).mpr Q₀.property).1

theorem specialUnitaryLeftTranslation_symm_one (Q₀ : StandardSpecialUnitary) :
    (specialUnitaryLeftTranslation Q₀).symm 1 = Q₀.val := Matrix.mul_one _

/-- Left translation by an actual special-unitary preserves the Gram matrix. -/
theorem specialUnitaryLeftTranslation_gram (Q₀ : StandardSpecialUnitary) (A : Mat) :
    (specialUnitaryLeftTranslation Q₀ A).conjTranspose *
      specialUnitaryLeftTranslation Q₀ A = A.conjTranspose * A := by
  have h := (isSpecialUnitary_iff_mem_standard Q₀.val).mpr Q₀.property
  change (Q₀.val.conjTranspose * A).conjTranspose * (Q₀.val.conjTranspose * A) = _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    (A.conjTranspose * Q₀.val) * (Q₀.val.conjTranspose * A) =
        (A.conjTranspose * (Q₀.val * Q₀.val.conjTranspose)) * A := by
      simp only [Matrix.mul_assoc]
    _ = A.conjTranspose * A := by
      rw [mul_eq_one_comm.mp h.1, Matrix.mul_one]

theorem specialUnitaryLeftTranslation_det (Q₀ : StandardSpecialUnitary) (A : Mat) :
    (specialUnitaryLeftTranslation Q₀ A).det = A.det := by
  have h := (isSpecialUnitary_iff_mem_standard Q₀.val).mpr Q₀.property
  simp [specialUnitaryLeftTranslation_apply, Matrix.det_mul, Matrix.det_conjTranspose, h.2]

/-- Membership is in mathlib's actual standard group on the original Index. -/
theorem specialUnitaryLeftTranslation_mem_iff (Q₀ : StandardSpecialUnitary) (A : Mat) :
    specialUnitaryLeftTranslation Q₀ A ∈ Matrix.specialUnitaryGroup Index ℂ ↔
      A ∈ Matrix.specialUnitaryGroup Index ℂ := by
  simp only [← isSpecialUnitary_iff_mem_standard, IsSpecialUnitary,
    specialUnitaryLeftTranslation_gram, specialUnitaryLeftTranslation_det]

theorem specialUnitaryLeftTranslation_symm_mem_iff (Q₀ : StandardSpecialUnitary) (B : Mat) :
    (specialUnitaryLeftTranslation Q₀).symm B ∈ Matrix.specialUnitaryGroup Index ℂ ↔
      B ∈ Matrix.specialUnitaryGroup Index ℂ := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (specialUnitaryLeftTranslation_mem_iff Q₀ ((specialUnitaryLeftTranslation Q₀).symm B)).symm

/-- Both maps are globally real analytic on the unchanged ambient matrix space. -/
theorem analyticOnNhd_specialUnitaryLeftTranslation (Q₀ : StandardSpecialUnitary) :
    AnalyticOnNhd ℝ (specialUnitaryLeftTranslation Q₀) Set.univ := by
  intro A _
  exact (specialUnitaryLeftTranslation Q₀).toContinuousLinearMap.analyticAt A

theorem analyticOnNhd_specialUnitaryLeftTranslation_symm (Q₀ : StandardSpecialUnitary) :
    AnalyticOnNhd ℝ (specialUnitaryLeftTranslation Q₀).symm Set.univ := by
  intro B _
  exact (specialUnitaryLeftTranslation Q₀).symm.toContinuousLinearMap.analyticAt B

/-- The literal residual is preserved on every ambient matrix. -/
theorem specialUnitaryLocalResidual_leftTranslation (Q₀ : StandardSpecialUnitary) (A : Mat) :
    specialUnitaryLocalResidual (specialUnitaryLeftTranslation Q₀ A) =
      specialUnitaryLocalResidual A := by
  simp only [specialUnitaryLocalResidual, specialUnitaryLeftTranslation_gram,
    specialUnitaryLeftTranslation_det]

theorem analyticOnNhd_specialUnitaryTranslatedResidual (Q₀ : StandardSpecialUnitary) :
    AnalyticOnNhd ℝ
      (fun A => specialUnitaryLocalResidual (specialUnitaryLeftTranslation Q₀ A)) Set.univ := by
  simpa only [specialUnitaryLocalResidual_leftTranslation] using
    analyticOnNhd_specialUnitaryLocalResidual

/-- The actual preimage of the explicit identity constraint neighborhood. -/
def specialUnitaryTranslatedConstraintDomain (Q₀ : StandardSpecialUnitary) : Set Mat :=
  specialUnitaryLeftTranslation Q₀ ⁻¹' specialUnitaryConstraintDomain

theorem isOpen_specialUnitaryTranslatedConstraintDomain (Q₀ : StandardSpecialUnitary) :
    IsOpen (specialUnitaryTranslatedConstraintDomain Q₀) :=
  isOpen_specialUnitaryConstraintDomain.preimage (specialUnitaryLeftTranslation Q₀).continuous

theorem self_mem_specialUnitaryTranslatedConstraintDomain (Q₀ : StandardSpecialUnitary) :
    Q₀.val ∈ specialUnitaryTranslatedConstraintDomain Q₀ := by
  change specialUnitaryLeftTranslation Q₀ Q₀.val ∈ specialUnitaryConstraintDomain
  rw [specialUnitaryLeftTranslation_apply_self]
  exact one_mem_specialUnitaryConstraintDomain

/-- This particular determinant-positive neighborhood is left-SU3-invariant.
No claim is made that it is an injective nonlinear chart domain. -/
theorem specialUnitaryTranslatedConstraintDomain_eq (Q₀ : StandardSpecialUnitary) :
    specialUnitaryTranslatedConstraintDomain Q₀ = specialUnitaryConstraintDomain := by
  ext A
  change 0 < (specialUnitaryLeftTranslation Q₀ A).det.re ↔ 0 < A.det.re
  rw [specialUnitaryLeftTranslation_det]

/-- Actual SU3 membership is exactly the translated literal zero equations on
this explicit open neighborhood of any standard special-unitary basepoint. -/
theorem mem_specialUnitary_iff_translated_residual_eq_zero
    (Q₀ : StandardSpecialUnitary) (A : Mat)
    (hA : A ∈ specialUnitaryTranslatedConstraintDomain Q₀) :
    A ∈ Matrix.specialUnitaryGroup Index ℂ ↔
      specialUnitaryLocalResidual (specialUnitaryLeftTranslation Q₀ A) = 0 :=
  (specialUnitaryLeftTranslation_mem_iff Q₀ A).symm.trans
    (mem_specialUnitary_iff_residual_eq_zero (specialUnitaryLeftTranslation Q₀ A) hA)

theorem eventually_mem_specialUnitary_iff_translated_residual_eq_zero
    (Q₀ : StandardSpecialUnitary) :
    ∀ᶠ A : Mat in 𝓝 Q₀.val,
      A ∈ Matrix.specialUnitaryGroup Index ℂ ↔
        specialUnitaryLocalResidual (specialUnitaryLeftTranslation Q₀ A) = 0 := by
  filter_upwards [(isOpen_specialUnitaryTranslatedConstraintDomain Q₀).mem_nhds
    (self_mem_specialUnitaryTranslatedConstraintDomain Q₀)] with A hA
  exact mem_specialUnitary_iff_translated_residual_eq_zero Q₀ A hA

end UnitaryErrorBases.ThreeCycleNormalized

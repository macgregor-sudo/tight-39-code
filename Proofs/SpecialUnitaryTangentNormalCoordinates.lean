module

public import SpecialUnitaryConstraintSplitting
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
Concrete tangent/normal coordinates on the actual ambient Mat, with the literal
kernel and range of the frozen constraint differential. The normal section is
the existing explicit formula, now represented as a real continuous-linear map.
No splitting premise, new constraint, determinant reproof, IFT or chart is used.
First-party composition of the source-admitted splitting and pinned linear APIs;
no upstream implementation copied. Thanks to their contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, 1676. https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
open scoped Matrix.Norms.Elementwise
namespace UnitaryErrorBases.SpecialUnitaryConstraints

/-- The existing normal formula as a real continuous-linear map on the raw target. -/
def constraintNormalCLM : (Mat × ℝ) →L[ℝ] Mat :=
  (1 / 2 : ℝ) • ContinuousLinearMap.fst ℝ Mat ℝ +
    (ContinuousLinearMap.snd ℝ Mat ℝ).smulRight ((1 / 3 : ℝ) • (Complex.I • (1 : Mat)))

theorem constraintNormalCLM_apply (p : Mat × ℝ) :
    constraintNormalCLM p = constraintNormal p.1 p.2 := by
  change (1 / 2 : ℝ) • p.1 + p.2 • ((1 / 3 : ℝ) • (Complex.I • (1 : Mat))) =
    (1 / 2 : ℝ) • p.1 + (Complex.I * (p.2 / 3 : ℝ)) • (1 : Mat)
  congr 1
  rw [smul_smul, ← smul_assoc]
  congr 1
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_one, div_eq_mul_inv]
  ring

/-- The normal section is a right inverse on the literal range of D. -/
theorem constraintNormalCLM_rightInverse
    (N : LinearMap.range constraintDifferential.toLinearMap) :
    constraintDifferential (constraintNormalCLM N.val) = N.val := by
  obtain ⟨A, hA⟩ := N.property
  rw [← hA, constraintNormalCLM_apply]
  exact constraintDifferential_normal _ (constraintDifferential_isHermitian A) _

/-- The actual ambient space is continuously and linearly split into the literal
kernel and range of the unchanged constraint differential. -/
def tangentNormalCoordinates : Mat ≃L[ℝ]
    (LinearMap.ker constraintDifferential.toLinearMap) ×
      (LinearMap.range constraintDifferential.toLinearMap) :=
  ({
    toFun := fun A =>
      (⟨A - constraintNormalCLM (constraintDifferential A), by
          change constraintDifferential (A - constraintNormalCLM (constraintDifferential A)) = 0
          rw [map_sub, constraintNormalCLM_apply,
            constraintDifferential_normal _ (constraintDifferential_isHermitian A)]
          exact sub_self _⟩,
        ⟨constraintDifferential A, ⟨A, rfl⟩⟩)
    invFun := fun p => p.1.val + constraintNormalCLM p.2.val
    left_inv := fun A => sub_add_cancel _ _
    right_inv := by
      intro p
      have hk : constraintDifferential p.1.val = 0 := p.1.property
      have hn := constraintNormalCLM_rightInverse p.2
      apply Prod.ext
      · apply Subtype.ext
        change p.1.val + constraintNormalCLM p.2.val -
          constraintNormalCLM (constraintDifferential (p.1.val + constraintNormalCLM p.2.val)) = p.1.val
        rw [map_add, hk, hn, zero_add, add_sub_cancel_right]
      · apply Subtype.ext
        change constraintDifferential (p.1.val + constraintNormalCLM p.2.val) = p.2.val
        rw [map_add, hk, hn, zero_add]
    map_add' := by
      intro A B
      apply Prod.ext
      · apply Subtype.ext
        change A + B - constraintNormalCLM (constraintDifferential (A + B)) =
          (A - constraintNormalCLM (constraintDifferential A)) +
          (B - constraintNormalCLM (constraintDifferential B))
        rw [map_add, map_add]
        abel
      · apply Subtype.ext
        exact map_add constraintDifferential A B
    map_smul' := by
      intro c A
      apply Prod.ext
      · apply Subtype.ext
        change c • A - constraintNormalCLM (constraintDifferential (c • A)) =
          c • (A - constraintNormalCLM (constraintDifferential A))
        rw [map_smul, map_smul, smul_sub]
      · apply Subtype.ext
        exact map_smul constraintDifferential c A
  } : Mat ≃ₗ[ℝ] (LinearMap.ker constraintDifferential.toLinearMap) ×
      (LinearMap.range constraintDifferential.toLinearMap)).toContinuousLinearEquiv

/-- The forward tangent component is the specified actual normal subtraction. -/
theorem tangentNormalCoordinates_fst (A : Mat) :
    (tangentNormalCoordinates A).1.val =
      A - constraintNormal (constraintDifferential A).1 (constraintDifferential A).2 := by
  change A - constraintNormalCLM (constraintDifferential A) = _
  rw [constraintNormalCLM_apply]

/-- The forward normal coordinate is exactly D A in its literal range. -/
theorem tangentNormalCoordinates_snd (A : Mat) :
    (tangentNormalCoordinates A).2.val = constraintDifferential A := rfl

/-- The inverse reconstructs the actual matrix with the existing normal formula. -/
theorem tangentNormalCoordinates_symm_apply
    (p : (LinearMap.ker constraintDifferential.toLinearMap) ×
      (LinearMap.range constraintDifferential.toLinearMap)) :
    tangentNormalCoordinates.symm p = p.1.val + constraintNormal p.2.val.1 p.2.val.2 := by
  change p.1.val + constraintNormalCLM p.2.val = _
  rw [constraintNormalCLM_apply]

/-- In the concrete coordinates, the original differential is the normal projection. -/
theorem constraintDifferential_tangentNormalCoordinates_symm
    (p : (LinearMap.ker constraintDifferential.toLinearMap) ×
      (LinearMap.range constraintDifferential.toLinearMap)) :
    constraintDifferential (tangentNormalCoordinates.symm p) = p.2.val := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (tangentNormalCoordinates_snd (tangentNormalCoordinates.symm p)).symm

end UnitaryErrorBases.SpecialUnitaryConstraints

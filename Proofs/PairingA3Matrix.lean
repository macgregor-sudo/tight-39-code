module
public import PairingDefinitions
public import ThreeCycleNormalForm
public import ThreeCycleUnitaryErrorBasis
public import UEBResidualDerivative
@[expose] public section
open scoped BigOperators Matrix.Norms.Elementwise
noncomputable section
namespace Option2StatementA3Matrix
end Option2StatementA3Matrix

namespace Option2StatementA3Matrix
/- The entire derivative kernel is the unrestricted finite equation system,
with a real-linear normal form and its explicit reconstruction map. -/
theorem unrestricted_matrix_normal_form (d : PhaseTriple) :
    (∀ V : Family, V ∈ firstOrderSpace (monomialFamily d) ↔
      SatisfiesFirstOrder (monomialFamily d) V) ∧
    ∃ e : firstOrderSpace (monomialFamily d) ≃ₗ[ℝ] NormalForm d,
      (∀ x, (e.symm x).val = tangentOfNormalForm d x) ∧
      (∀ V, e.symm (e V) = V) ∧ (∀ x, e (e.symm x) = x) := by
  refine ⟨?_, ?_⟩
  · intro V
    exact ArchitectureUEBDerivative.first_order_mem_iff _ V
      (UnitaryErrorBases.ThreeCycleMatrix.monomial_family_is_unitary_error_basis d)
  · let e : firstOrderSpace (monomialFamily d) ≃ₗ[ℝ] NormalForm d :=
      UnitaryErrorBases.ThreeCycleMatrix.firstOrderNormalForm d
    exact ⟨e, (fun _ => rfl), e.symm_apply_apply, e.apply_symm_apply⟩
end Option2StatementA3Matrix

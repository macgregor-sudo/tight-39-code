module

public import A3Interfaces

@[expose] public section

/-!
# The four anchor phase triples are unit, determinant-one triples
-/

noncomputable section

namespace CKM.NativeFirstOrder

theorem anchorPhases_isPhaseTriple (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    (∀ j, Complex.normSq (anchorPhases ξ H j) = 1) ∧ ∏ j, anchorPhases ξ H j = 1 := by
  have h0 : ξ 0 ≠ 0 := fun h => by simpa [h] using hξ 0
  have h1 : ξ 1 ≠ 0 := fun h => by simpa [h] using hξ 1
  have h2 : ξ 2 ≠ 0 := fun h => by simpa [h] using hξ 2
  have h3 : ξ 3 ≠ 0 := fun h => by simpa [h] using hξ 3
  have n0 := hξ 0
  have n1 := hξ 1
  have n2 := hξ 2
  have n3 := hξ 3
  have hprod : ∀ d : UnitaryErrorBases.Index → ℂ, ∏ j, d j = d 0 * d 1 * d 2 := fun d =>
    Fin.prod_univ_three d
  refine ⟨fun j => ?_, ?_⟩
  · fin_cases H <;> fin_cases j <;>
      simp [anchorPhases, map_mul, map_div₀, map_inv₀, Complex.normSq_neg, n0, n1, n2, n3]
  · rw [hprod]
    fin_cases H <;> simp [anchorPhases] <;> field_simp

/-- The anchor phase triple `d_H(ξ)` as an accepted `PhaseTriple`. -/
def anchorTriple (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) : UnitaryErrorBases.PhaseTriple :=
  ⟨anchorPhases ξ H, anchorPhases_isPhaseTriple ξ hξ H⟩

end CKM.NativeFirstOrder

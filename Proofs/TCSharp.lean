module

public import TCDefs
public import A3Family

@[expose] public section

/-!
# A7: the bound is attained by the accepted literal code 

The known construction is Cohn–Kumar–Minton, arXiv:1308.3188v4, §8.2, Theorem 8.3 (p. 49).

Uses only the accepted A3 interfaces: `CKM.NativeFirstOrder.literal_frame` (each of the thirteen
literal frames is a `Glennie.Frame`, hence purity) and `literalCfg_originalEquations` (its `pair`
field, with `CoordinateMaps.coordinatePairing_upperCoordinates_eq_native_trace`, gives distinct
overlaps `0` in a frame and `1/3` across frames), at any unit phase.
-/

noncomputable section

namespace CKM.NativeTightCode

open Glennie CKM.NativeFirstOrder

theorem literalPoint_pure (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 39) :
    IsPure (literalPoint ξ i) := by
  rw [← framePointIndex_div_mod i]
  have hfr := literal_frame ξ hξ ⟨i.val / 3, by omega⟩
  exact ⟨hfr.idempotent _, hfr.trace_one _⟩

theorem literalPoint_overlapBound (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    OverlapBound (literalPoint ξ) := by
  have hlt : ∀ i j : Fin 39, i < j → inner (literalPoint ξ i) (literalPoint ξ j) ≤ (1 / 3 : ℝ) := by
    intro i j hij
    have h := (literalCfg_originalEquations ξ hξ).pair ⟨(i, j), hij⟩
    simp only at h
    rw [show literalCfg ξ i = NativePolynomial.upperCoordinates (literalPoint ξ i) from rfl,
      show literalCfg ξ j = NativePolynomial.upperCoordinates (literalPoint ξ j) from rfl,
      NativePolynomial.CoordinateMaps.coordinatePairing_upperCoordinates_eq_native_trace] at h
    show trace (jordan (literalPoint ξ i) (literalPoint ξ j)) ≤ 1 / 3
    rw [h]
    split_ifs <;> norm_num
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · rw [Glennie.inner_comm]
    exact hlt j i h

/-- The bound `39` is attained by native pure points. -/
theorem exists_tight_code : ∃ P : Fin 39 → Albert, (∀ i, IsPure (P i)) ∧ OverlapBound P := by
  have h1 : IsUnitPhase (fun _ : Fin 4 => (1 : ℂ)) := fun _ => Complex.normSq_one
  exact ⟨literalPoint (fun _ => 1), literalPoint_pure _ h1, literalPoint_overlapBound _ h1⟩

#print axioms literalPoint_pure
#print axioms literalPoint_overlapBound
#print axioms exists_tight_code

end CKM.NativeTightCode

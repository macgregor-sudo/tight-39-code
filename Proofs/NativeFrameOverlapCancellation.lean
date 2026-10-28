module

public import NativePolynomialEvaluationStaged
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
Exact cross-frame deviation cancellation for the existing native Albert carrier.
The imported native declarations retain their existing provenance and notices;
no native algebra declaration or proof body is copied into this module.
This is an optional overlap-loss prerequisite, not a robustness theorem.
-/

namespace SupportedStress.NativeFrames

/-- The nine cross-frame overlaps have total deviation zero from `1 / 3`.
The row totals are derived from the actual frame sum and trace-one fields. -/
theorem frame_pair_deviation_sum_zero
    (p q : Fin 3 → Glennie.Albert)
    (hp : Glennie.Frame p) (hq : Glennie.Frame q) :
    ∑ i : Fin 3, ∑ j : Fin 3,
      (Glennie.trace (Glennie.jordan (p i) (q j)) - (1 / 3 : ℝ)) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hrow := congrArg
    (fun x : Glennie.Albert => Glennie.trace (Glennie.jordan (p i) x))
    hq.sum_unit
  simp only [Glennie.jordan_add_right, Glennie.trace_add,
    Glennie.jordan_unit_right, hp.trace_one] at hrow
  rw [Fin.sum_univ_three]
  linarith

end SupportedStress.NativeFrames

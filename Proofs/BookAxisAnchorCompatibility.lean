module

public import BookAxisAnchorSheet0
public import BookAxisAnchorSheet1
public import BookAxisAnchorSheet2
public import BookAxisAnchorSheet3

set_option Elab.async false

@[expose] public section

/-!
The actual supplied D6 lists avoid their original four anchor frames. Their
accepted eigenvector permutation and real-form map therefore send a Book axis
to zero on that axis's literal AnchorCoordinate set. The resulting affine
agreement holds at every packed real base, without claiming tangent membership,
solution validity, a metric comparison or native stress cancellation.
-/

noncomputable section

namespace Option2.NativeStress.BookHT.TangentCoordinates

open scoped BigOperators ComplexConjugate
open Dictionary AnchorSupport

/-- All 24 original D6 columns avoid the corresponding native anchor set. -/
theorem d6Entries_avoid_anchor (b : Fin 24) :
    EntriesAvoidAnchor (d6Sheet b) (d6Entries b) := by
  revert b
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  exact ⟨sheet0_entries_avoid 0, sheet0_entries_avoid 1, sheet0_entries_avoid 2,
    sheet0_entries_avoid 3, sheet0_entries_avoid 4, sheet0_entries_avoid 5,
    sheet1_entries_avoid 0, sheet1_entries_avoid 1, sheet1_entries_avoid 2,
    sheet1_entries_avoid 3, sheet1_entries_avoid 4, sheet1_entries_avoid 5,
    sheet2_entries_avoid 0, sheet2_entries_avoid 1, sheet2_entries_avoid 2,
    sheet2_entries_avoid 3, sheet2_entries_avoid 4, sheet2_entries_avoid 5,
    sheet3_entries_avoid 0, sheet3_entries_avoid 1, sheet3_entries_avoid 2,
    sheet3_entries_avoid 3, sheet3_entries_avoid 4, sheet3_entries_avoid 5, trivial⟩

theorem d6Column_anchor_zero (b : Fin 24) (v : Fin 1053)
    (hv : AnchorCoordinate (d6Sheet b) v) : d6Column b v = 0 :=
  sparseValue_eq_zero_of_avoids (d6Sheet b) (d6Entries b) (d6Entries_avoid_anchor b) v hv

/-- The actual Book ordering uses only the six D6 columns of its chosen sheet. -/
theorem realCoordinates_single_of_sheet_ne (i : Fin 4) (u : Triple) (j : Fin 24)
    (h : d6Sheet (eigenIndex j) ≠ i) : realCoordinates (Pi.single i u) j = 0 := by
  revert h i j
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  simp [d6Sheet, eigenIndex, realCoordinates]

/-- Every native anchor coordinate vanishes on the corresponding actual Book axis. -/
theorem realV_axis_anchor_zero (i : Fin 4) (u : Triple) (v : Fin 1053)
    (hv : AnchorCoordinate i v) : realV (Pi.single i u) v = 0 := by
  have hc : (realV (Pi.single i u) v : ℂ) = 0 := by
    rw [realV_complex, V_apply]
    apply Finset.sum_eq_zero
    intro j _
    by_cases h : d6Sheet (eigenIndex j) = i
    · have hz : d6Column (eigenIndex j) v = 0 :=
        d6Column_anchor_zero (eigenIndex j) v (h.symm ▸ hv)
      change realCoordinates (Pi.single i u) j * d6Column (eigenIndex j) v = 0
      rw [hz, mul_zero]
    · rw [realCoordinates_single_of_sheet_ne i u j h, zero_mul]
  exact_mod_cast hc

/-- Exact affine anchor agreement at an arbitrary packed native real base. -/
theorem realV_axis_affine_anchor (p : Fin 1053 → ℝ) (i : Fin 4) (u : Triple)
    (v : Fin 1053) (hv : AnchorCoordinate i v) :
    (p + realV (Pi.single i u)) v = p v := by
  simp only [Pi.add_apply, realV_axis_anchor_zero i u v hv, add_zero]

/-- The same agreement for the continuous-linear map, with no replacement model. -/
theorem realVContinuousLinearMap_axis_anchor_zero (i : Fin 4) (u : Triple)
    (v : Fin 1053) (hv : AnchorCoordinate i v) :
    realVContinuousLinearMap (Pi.single i u) v = 0 :=
  realV_axis_anchor_zero i u v hv

/-- The whole affine line fixes the literal anchors. -/
theorem realV_axis_line_anchor (p : Fin 1053 → ℝ) (i : Fin 4) (u : Triple)
    (t : ℝ) (v : Fin 1053) (hv : AnchorCoordinate i v) :
    (p + t • realV (Pi.single i u)) v = p v := by
  simp only [Pi.add_apply, Pi.smul_apply, realV_axis_anchor_zero i u v hv,
    smul_zero, add_zero]

end Option2.NativeStress.BookHT.TangentCoordinates

open Option2.NativeStress.BookHT.TangentCoordinates

#check @d6Entries_avoid_anchor
#check @d6Column_anchor_zero
#check @realCoordinates_single_of_sheet_ne
#check @realV_axis_anchor_zero
#check @realV_axis_affine_anchor
#check @realVContinuousLinearMap_axis_anchor_zero
#check @realV_axis_line_anchor
#print axioms d6Entries_avoid_anchor
#print axioms d6Column_anchor_zero
#print axioms realCoordinates_single_of_sheet_ne
#print axioms realV_axis_anchor_zero
#print axioms realV_axis_affine_anchor
#print axioms realVContinuousLinearMap_axis_anchor_zero
#print axioms realV_axis_line_anchor

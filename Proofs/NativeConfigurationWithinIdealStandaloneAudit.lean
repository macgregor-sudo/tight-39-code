module

public import NativeConfigurationPolynomialResiduals

@[expose] public section

/-!
# All within-frame product rows in the original F ideal

The three ordered pairs in each frame use the same bilinear residual identity,
with the complementary point placed last. Two local additive equalities put
those frame sums into their canonical order. Frames and coordinates remain
symbolic; no configuration row, product or ideal is redefined.

This is classical bilinear/polynomial ideal arithmetic, with no novelty claim.
The first-party frame identity and coordinate maps are imported and applied.
Imported Mathlib APIs are pinned at065356127b1dc0016f66b7283ce0ce2c4055aa55;
no upstream proof body is copied. The native source remains imported from
https://github.com/macgregor-sudo/compact-albert-recognition, commit
40d3b344180d9ddb78aaa2876873377c1e631515. Existing Apache-2.0 notices and
extraction provenance remain at THIRD_PARTY_NOTICES.md#native-albert-code.
No full ideal equality, row clearing or certificate binding is asserted.
Thanks to the native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace NativePolynomial.ConfigurationResiduals

open scoped BigOperators
open CoordinateMaps MvPolynomial FrameResiduals ConfigurationResidualIndices

variable {R : Type*} [CommRing R]

private theorem within_id_mem (h t : R) (i : Fin 39) (k : Fin 27) :
    idempotencyResidual (coordinateProduct (C h)) (point i) k ∈ fIdeal h t := by
  have hRow : fRow h t (fNumber (fId i k)) ∈ fIdeal h t :=
    Ideal.subset_span ⟨fNumber (fId i k), rfl⟩
  rw [fRow_id] at hRow
  exact hRow

private theorem within_sum_mem (h t : R) (f : Fin 13) (k : Fin 27) :
    frameSumResidual coordinateUnit (point (framePointIndex f 0))
      (point (framePointIndex f 1)) (point (framePointIndex f 2)) k ∈ fIdeal h t := by
  have hRow : fRow h t (fNumber (fSum f k)) ∈ fIdeal h t :=
    Ideal.subset_span ⟨fNumber (fSum f k), rfl⟩
  rw [fRow_sum, Fin.sum_univ_three] at hRow
  change (point (framePointIndex f 0) k + point (framePointIndex f 1) k +
    point (framePointIndex f 2) k - coordinateUnit k) ∈ fIdeal h t
  exact hRow

/-- All three product rows in every frame follow from actual F generators. -/
theorem within_mem_fIdeal (h t : R) (hHalf : (2 : R) * h = 1)
    (f : Fin 13) (s : Fin 3) (k : Fin 27) :
    gRow h t (gNumber (gWithin f s k)) ∈ fIdeal h t := by
  have hHalfP : (2 : MvPolynomial (Fin 1053) R) * C h = 1 := by
    have hConstant : (C (2 : R) : MvPolynomial (Fin 1053) R) = 2 :=
      _root_.map_ofNat C 2
    have hMapped := congrArg (C : R →+* MvPolynomial (Fin 1053) R) hHalf
    rw [map_mul, hConstant, map_one] at hMapped
    exact hMapped
  have hSwap :
      frameSumResidual (coordinateUnit : Fin 27 → MvPolynomial (Fin 1053) R)
        (point (framePointIndex f 0)) (point (framePointIndex f 2))
        (point (framePointIndex f 1)) =
      frameSumResidual coordinateUnit (point (framePointIndex f 0))
        (point (framePointIndex f 1)) (point (framePointIndex f 2)) := by
    change (point (framePointIndex f 0) + point (framePointIndex f 2) +
        point (framePointIndex f 1)) - coordinateUnit =
      (point (framePointIndex f 0) + point (framePointIndex f 1) +
        point (framePointIndex f 2)) - coordinateUnit
    exact congrArg (fun v : Fin 27 → MvPolynomial (Fin 1053) R => v - coordinateUnit)
      (add_right_comm (point (framePointIndex f 0)) (point (framePointIndex f 2))
        (point (framePointIndex f 1)))
  have hCycle :
      frameSumResidual (coordinateUnit : Fin 27 → MvPolynomial (Fin 1053) R)
        (point (framePointIndex f 1)) (point (framePointIndex f 2))
        (point (framePointIndex f 0)) =
      frameSumResidual coordinateUnit (point (framePointIndex f 0))
        (point (framePointIndex f 1)) (point (framePointIndex f 2)) := by
    change (point (framePointIndex f 1) + point (framePointIndex f 2) +
        point (framePointIndex f 0)) - coordinateUnit =
      (point (framePointIndex f 0) + point (framePointIndex f 1) +
        point (framePointIndex f 2)) - coordinateUnit
    exact congrArg (fun v : Fin 27 → MvPolynomial (Fin 1053) R => v - coordinateUnit)
      ((add_comm (point (framePointIndex f 1) + point (framePointIndex f 2))
        (point (framePointIndex f 0))).trans
        (add_assoc (point (framePointIndex f 0)) (point (framePointIndex f 1))
          (point (framePointIndex f 2))).symm)
  have hSum021 (j : Fin 27) :
      frameSumResidual coordinateUnit (point (framePointIndex f 0))
        (point (framePointIndex f 2)) (point (framePointIndex f 1)) j ∈ fIdeal h t := by
    rw [hSwap]
    exact within_sum_mem h t f j
  have hSum120 (j : Fin 27) :
      frameSumResidual coordinateUnit (point (framePointIndex f 1))
        (point (framePointIndex f 2)) (point (framePointIndex f 0)) j ∈ fIdeal h t := by
    rw [hCycle]
    exact within_sum_mem h t f j
  have hProduct := product_mem_of_frame_residuals (fIdeal h t)
    (coordinateProduct (C h)) coordinateUnit
    (coordinateProduct_comm (C h)) (coordinateProduct_unit_left (C h) hHalfP)
    (coordinate_two_isUnit (C h) hHalfP)
  have h01 := hProduct (point (framePointIndex f 0)) (point (framePointIndex f 1))
    (point (framePointIndex f 2))
    (within_id_mem h t (framePointIndex f 0))
    (within_id_mem h t (framePointIndex f 1))
    (within_id_mem h t (framePointIndex f 2)) (within_sum_mem h t f)
  have h02 := hProduct (point (framePointIndex f 0)) (point (framePointIndex f 2))
    (point (framePointIndex f 1))
    (within_id_mem h t (framePointIndex f 0))
    (within_id_mem h t (framePointIndex f 2))
    (within_id_mem h t (framePointIndex f 1)) hSum021
  have h12 := hProduct (point (framePointIndex f 1)) (point (framePointIndex f 2))
    (point (framePointIndex f 0))
    (within_id_mem h t (framePointIndex f 1))
    (within_id_mem h t (framePointIndex f 2))
    (within_id_mem h t (framePointIndex f 0)) hSum120
  rw [gRow_within]
  have hCases : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  rcases hCases with rfl | rfl | rfl
  · simpa only [withinPair_zero] using h01 k
  · simpa only [withinPair_one] using h02 k
  · simpa only [withinPair_two] using h12 k

/-- The same family in its literal original G numbering. -/
theorem within_literal_mem_fIdeal (h t : R) (hHalf : (2 : R) * h = 1)
    (f : Fin 13) (s : Fin 3) (k : Fin 27) :
    gRow h t ⟨1053 + 81 * f.val + 27 * s.val + k.val, by omega⟩ ∈ fIdeal h t := by
  have hIndex : gNumber (gWithin f s k) =
      (⟨1053 + 81 * f.val + 27 * s.val + k.val, by omega⟩ : Fin 3159) := by
    apply Fin.ext
    exact gNumber_within_val f s k
  rw [← hIndex]
  exact within_mem_fIdeal h t hHalf f s k

end NativePolynomial.ConfigurationResiduals



#check @NativePolynomial.ConfigurationResiduals.within_mem_fIdeal
#check @NativePolynomial.ConfigurationResiduals.within_literal_mem_fIdeal
#print axioms NativePolynomial.ConfigurationResiduals.within_mem_fIdeal
#print axioms NativePolynomial.ConfigurationResiduals.within_literal_mem_fIdeal

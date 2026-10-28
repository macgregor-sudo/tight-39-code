module

public import NativeConfigurationPairIdealStandaloneAudit

@[expose] public section

/-!
# Every actual F trace row belongs to the G ideal

Each point uses the three cross overlaps and sum of a different frame.
Sorting point labels gives actual scalar G generators; reversed orientation
is justified by the coordinate product and trace identities. The public
frame trace-recovery lemma then supplies each of the 39 F trace residuals.
Both normalizations 2*h=1 and 3*t=1 remain explicit.

This is elementary finite-label and polynomial ideal arithmetic, with no
novelty claim. First-party scalar-map, coordinate and FrameResiduals APIs
are imported and applied, not copied. Mathlib remains pinned at
065356127b1dc0016f66b7283ce0ce2c4055aa55. The unchanged native dependency is
https://github.com/macgregor-sudo/compact-albert-recognition, commit
40d3b344180d9ddb78aaa2876873377c1e631515. Existing Apache-2.0 notices and
extraction provenance remain at THIRD_PARTY_NOTICES.md#native-albert-code.
No new point labels, residuals, ideal premises or certificate data are used.
Thanks to the native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

namespace NativePolynomial.ConfigurationResiduals

open CoordinateMaps MvPolynomial FrameResiduals ConfigurationResidualIndices

variable {R : Type*} [CommRing R]

/-- Sorting an actual cross pair preserves its scalar residual in the G ideal. -/
private theorem crossPairing_mem_gSpan (h t : R)
    (hHalfP : (2 : MvPolynomial (Fin 1053) R) * C h = 1) (i j : Fin 39)
    (hFramesNe : i.val / 3 ≠ j.val / 3) :
    coordinatePairing (point i) (point j) - C t ∈
      Ideal.span (Set.range (gRow h t)) := by
  have hDifferent : i.val ≠ j.val := by
    intro hEq
    exact hFramesNe (congrArg (fun n : ℕ => n / 3) hEq)
  by_cases hij : i < j
  · let ij : Pair 39 := ⟨(i, j), hij⟩
    have hRow := fCross_mem_gSpan h t ij hFramesNe
    rw [fRow_pair, ite_eq_right hFramesNe] at hRow
    exact hRow
  · have hji : j < i := by
      change j.val < i.val
      have hNot : ¬ i.val < j.val := hij
      omega
    let ji : Pair 39 := ⟨(j, i), hji⟩
    have hRow := fCross_mem_gSpan h t ji hFramesNe.symm
    rw [fRow_pair, ite_eq_right hFramesNe.symm] at hRow
    have hSymm : coordinatePairing (point j : Fin 27 → MvPolynomial (Fin 1053) R) (point i) =
        coordinatePairing (point i) (point j) := by
      calc
        _ = coordinateTrace (coordinateProduct (C h) (point j) (point i)) :=
          (coordinateTrace_product (C h) hHalfP _ _).symm
        _ = coordinateTrace (coordinateProduct (C h) (point i) (point j)) :=
          congrArg coordinateTrace
            (coordinateProduct_comm (C h) (point j) (point i))
        _ = _ := coordinateTrace_product (C h) hHalfP _ _
    rw [hSymm] at hRow
    exact hRow

/-- Every original F trace residual follows from actual G cross and sum rows. -/
theorem fTrace_mem_gSpan (h t : R) (hHalf : (2 : R) * h = 1)
    (hThird : (3 : R) * t = 1) (i : Fin 39) :
    fRow h t (fNumber (fTrace i)) ∈ Ideal.span (Set.range (gRow h t)) := by
  let I : Ideal (MvPolynomial (Fin 1053) R) := Ideal.span (Set.range (gRow h t))
  have hHalfP : (2 : MvPolynomial (Fin 1053) R) * C h = 1 := by
    have hConstant : (C (2 : R) : MvPolynomial (Fin 1053) R) = 2 :=
      _root_.map_ofNat C 2
    have hMapped := congrArg (C : R →+* MvPolynomial (Fin 1053) R) hHalf
    rw [map_mul, hConstant, map_one] at hMapped
    exact hMapped
  have hThirdP : (3 : MvPolynomial (Fin 1053) R) * C t = 1 := by
    have hConstant : (C (3 : R) : MvPolynomial (Fin 1053) R) = 3 :=
      _root_.map_ofNat C 3
    have hMapped := congrArg (C : R →+* MvPolynomial (Fin 1053) R) hThird
    rw [map_mul, hConstant, map_one] at hMapped
    exact hMapped
  obtain ⟨f, a, hi⟩ := exists_framePointIndex_eq i
  have hFrame : i.val / 3 = f.val := by
    rw [← hi, framePointIndex_div_three]
  have hOther : ∃ g : Fin 13, g ≠ f := by
    by_cases hfZero : f = 0
    · refine ⟨1, ?_⟩
      rw [hfZero]
      decide
    · exact ⟨0, Ne.symm hfZero⟩
  obtain ⟨g, hgf⟩ := hOther
  have hFrames (b : Fin 3) : i.val / 3 ≠ (framePointIndex g b).val / 3 := by
    rw [hFrame, framePointIndex_div_three]
    intro hEq
    exact hgf (Fin.ext hEq.symm)
  have hCross (b : Fin 3) :
      coordinateTrace (coordinateProduct (C h)
        (point i) (point (framePointIndex g b))) - C t ∈ I := by
    rw [coordinateTrace_product (C h) hHalfP]
    exact crossPairing_mem_gSpan h t hHalfP i (framePointIndex g b) (hFrames b)
  have hSum (k : Fin 27) :
      frameSumResidual coordinateUnit (point (framePointIndex g 0))
        (point (framePointIndex g 1)) (point (framePointIndex g 2)) k ∈ I := by
    have hRow : gRow h t (gNumber (gSum g k)) ∈ I :=
      Ideal.subset_span ⟨gNumber (gSum g k), rfl⟩
    rw [gRow_sum, Fin.sum_univ_three] at hRow
    change (point (framePointIndex g 0) k + point (framePointIndex g 1) k +
      point (framePointIndex g 2) k - coordinateUnit k) ∈ I
    exact hRow
  have hTrace := trace_mem_of_other_frame_residuals I
    coordinateTrace (coordinateProduct (C h)) coordinateUnit
    (coordinateProduct_unit_right (C h) hHalfP) (C t) hThirdP
    (point i) (point (framePointIndex g 0))
    (point (framePointIndex g 1)) (point (framePointIndex g 2))
    (hCross 0) (hCross 1) (hCross 2) hSum
  rw [fRow_trace]
  exact hTrace

end NativePolynomial.ConfigurationResiduals


#check @NativePolynomial.ConfigurationResiduals.fTrace_mem_gSpan
#print axioms NativePolynomial.ConfigurationResiduals.fTrace_mem_gSpan

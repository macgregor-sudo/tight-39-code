module

public import NativeConfigurationForwardIdealStandaloneAudit

@[expose] public section

/-!
# All scalar F pair rows belong to the actual G ideal

The existing finite product equivalence reconstructs a point's frame and
outcome labels. An ordered cross-frame pair is an actual G cross generator.
For a within-frame pair, the trace of the actual G vector product gives its
scalar overlap. These cover the 702 cross and 39 within scalar F rows.
Only the within branch needs 2*h=1; no third normalization is used here.

This is elementary finite-label and polynomial ideal arithmetic, with no
novelty claim. The first-party residual APIs and Mathlib finProdFinEquiv
(Mathlib/Logic/Equiv/Fin/Basic.lean:332) are imported and applied, not copied.
Mathlib remains pinned at065356127b1dc0016f66b7283ce0ce2c4055aa55. The
unchanged native dependency comes from
https://github.com/macgregor-sudo/compact-albert-recognition, commit
40d3b344180d9ddb78aaa2876873377c1e631515. Existing Apache-2.0 notices and
extraction provenance remain at THIRD_PARTY_NOTICES.md#native-albert-code.
No new label data, carrier, residual family or certificate binding is added.
Thanks to the native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

namespace NativePolynomial.ConfigurationResiduals

open CoordinateMaps MvPolynomial FrameResiduals ConfigurationResidualIndices

/-- Every actual point label is a frame label paired with one of its outcomes. -/
theorem exists_framePointIndex_eq (i : Fin 39) :
    ∃ f : Fin 13, ∃ a : Fin 3, framePointIndex f a = i := by
  obtain ⟨⟨f, a⟩, h⟩ := (finProdFinEquiv : Fin 13 × Fin 3 ≃ Fin 39).surjective i
  refine ⟨f, a, ?_⟩
  have hIndex : framePointIndex f a = finProdFinEquiv (f, a) := by
    apply Fin.ext
    change 3 * f.val + a.val = a.val + 3 * f.val
    omega
  exact hIndex.trans h

variable {R : Type*} [CommRing R]

/-- A canonical cross-frame F scalar row is an actual G cross generator. -/
theorem fCross_mem_gSpan (h t : R) (ij : Pair 39)
    (hFramesNe : ij.val.1.val / 3 ≠ ij.val.2.val / 3) :
    fRow h t (fNumber (fPair ij)) ∈ Ideal.span (Set.range (gRow h t)) := by
  obtain ⟨f, a, hi⟩ := exists_framePointIndex_eq ij.val.1
  obtain ⟨g, b, hj⟩ := exists_framePointIndex_eq ij.val.2
  have hf : ij.val.1.val / 3 = f.val := by
    rw [← hi, framePointIndex_div_three]
  have hg : ij.val.2.val / 3 = g.val := by
    rw [← hj, framePointIndex_div_three]
  have hiVal : 3 * f.val + a.val = ij.val.1.val := by
    simpa only [framePointIndex_val] using congrArg (fun q : Fin 39 => q.val) hi
  have hjVal : 3 * g.val + b.val = ij.val.2.val := by
    simpa only [framePointIndex_val] using congrArg (fun q : Fin 39 => q.val) hj
  have hfg : f < g := by
    change f.val < g.val
    have hij : ij.val.1.val < ij.val.2.val := ij.property
    have ha := a.isLt
    have hb := b.isLt
    omega
  let fg : Pair 13 := ⟨(f, g), hfg⟩
  have hPair : crossPointPair fg a b = ij := by
    apply Subtype.ext
    exact Prod.ext hi hj
  have hRow := gRow_cross_eq_fRow_pair h t fg a b
  rw [hPair] at hRow
  rw [← hRow]
  exact Ideal.subset_span ⟨gNumber (gCross fg a b), rfl⟩

/-- A scalar within overlap is the trace of its actual G vector product. -/
theorem fWithin_mem_gSpan (h t : R) (hHalf : (2 : R) * h = 1) (ij : Pair 39)
    (hSameFrame : ij.val.1.val / 3 = ij.val.2.val / 3) :
    fRow h t (fNumber (fPair ij)) ∈ Ideal.span (Set.range (gRow h t)) := by
  let I : Ideal (MvPolynomial (Fin 1053) R) := Ideal.span (Set.range (gRow h t))
  have hHalfP : (2 : MvPolynomial (Fin 1053) R) * C h = 1 := by
    have hConstant : (C (2 : R) : MvPolynomial (Fin 1053) R) = 2 :=
      _root_.map_ofNat C 2
    have hMapped := congrArg (C : R →+* MvPolynomial (Fin 1053) R) hHalf
    rw [map_mul, hConstant, map_one] at hMapped
    exact hMapped
  obtain ⟨f, a, hi⟩ := exists_framePointIndex_eq ij.val.1
  obtain ⟨g, b, hj⟩ := exists_framePointIndex_eq ij.val.2
  have hf : ij.val.1.val / 3 = f.val := by
    rw [← hi, framePointIndex_div_three]
  have hg : ij.val.2.val / 3 = g.val := by
    rw [← hj, framePointIndex_div_three]
  have hfg : f = g := by
    apply Fin.ext
    omega
  subst g
  have hab : a < b := by
    change a.val < b.val
    have hiVal : 3 * f.val + a.val = ij.val.1.val := by
      simpa only [framePointIndex_val] using congrArg (fun q : Fin 39 => q.val) hi
    have hjVal : 3 * f.val + b.val = ij.val.2.val := by
      simpa only [framePointIndex_val] using congrArg (fun q : Fin 39 => q.val) hj
    have hij : ij.val.1.val < ij.val.2.val := ij.property
    omega
  let s : Fin 3 := withinPair.symm ⟨(a, b), hab⟩
  have hPair : withinPair s = ⟨(a, b), hab⟩ :=
    withinPair.apply_symm_apply ⟨(a, b), hab⟩
  have hProduct (k : Fin 27) :
      coordinateProduct (C h) (point ij.val.1) (point ij.val.2) k ∈ I := by
    have hRow : gRow h t (gNumber (gWithin f s k)) ∈ I :=
      Ideal.subset_span ⟨gNumber (gWithin f s k), rfl⟩
    rw [gRow_within, hPair] at hRow
    simpa only [hi, hj] using hRow
  have hPairing := trace_product_mem_of_coordinates I coordinateTrace
    (coordinateProduct (C h)) (point ij.val.1) (point ij.val.2) hProduct
  rw [coordinateTrace_product (C h) hHalfP] at hPairing
  rw [fRow_pair, ite_eq_left hSameFrame, sub_zero]
  exact hPairing

/-- The same/different-frame cases cover every actual scalar F pair row. -/
theorem fPair_mem_gSpan (h t : R) (hHalf : (2 : R) * h = 1) (ij : Pair 39) :
    fRow h t (fNumber (fPair ij)) ∈ Ideal.span (Set.range (gRow h t)) := by
  by_cases hSameFrame : ij.val.1.val / 3 = ij.val.2.val / 3
  · exact fWithin_mem_gSpan h t hHalf ij hSameFrame
  · exact fCross_mem_gSpan h t ij hSameFrame

end NativePolynomial.ConfigurationResiduals



#check @NativePolynomial.ConfigurationResiduals.exists_framePointIndex_eq
#check @NativePolynomial.ConfigurationResiduals.fCross_mem_gSpan
#check @NativePolynomial.ConfigurationResiduals.fWithin_mem_gSpan
#check @NativePolynomial.ConfigurationResiduals.fPair_mem_gSpan
#print axioms NativePolynomial.ConfigurationResiduals.exists_framePointIndex_eq
#print axioms NativePolynomial.ConfigurationResiduals.fCross_mem_gSpan
#print axioms NativePolynomial.ConfigurationResiduals.fWithin_mem_gSpan
#print axioms NativePolynomial.ConfigurationResiduals.fPair_mem_gSpan

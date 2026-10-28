module

public import NativeConfigurationPolynomialResiduals

@[expose] public section

/-!
# Cross-frame G rows as canonical F generators

Ordered frame labels give ordered point labels. Division by three recovers
the frame, so each actual cross-frame G row is the corresponding F pair row.
The resulting ideal membership uses that literal F generator. The parameters
h and t remain arbitrary; no normalization or full ideal inclusion is asserted.

This is elementary finite-label and polynomial ideal arithmetic, with no
novelty claim. The earlier first-party index and residual definitions are
imported and applied; no upstream implementation is copied. Mathlib remains
pinned at065356127b1dc0016f66b7283ce0ce2c4055aa55. The native source is
imported through the existing chain from
https://github.com/macgregor-sudo/compact-albert-recognition, commit
40d3b344180d9ddb78aaa2876873377c1e631515. Existing Apache-2.0 notices and
extraction provenance remain at THIRD_PARTY_NOTICES.md#native-albert-code.
No new carrier, row clearing, native evaluation or certificate binding is added.
Thanks to the native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

namespace NativePolynomial.ConfigurationResiduals

open CoordinateMaps MvPolynomial ConfigurationResidualIndices

/-- Every point of an earlier frame precedes every point of a later frame. -/
theorem framePointIndex_lt_of_lt (f g : Fin 13) (hfg : f < g) (a b : Fin 3) :
    framePointIndex f a < framePointIndex g b := by
  change (framePointIndex f a).val < (framePointIndex g b).val
  rw [framePointIndex_val, framePointIndex_val]
  have hFrames : f.val < g.val := hfg
  have ha := a.isLt
  have hb := b.isLt
  omega

/-- The quotient in the actual F pair test is precisely the frame label. -/
theorem framePointIndex_div_three (f : Fin 13) (a : Fin 3) :
    (framePointIndex f a).val / 3 = f.val := by
  rw [framePointIndex_val]
  have ha := a.isLt
  omega

/-- The actual increasing point pair belonging to a cross-frame G label. -/
def crossPointPair (fg : Pair 13) (a b : Fin 3) : Pair 39 :=
  ⟨(framePointIndex fg.val.1 a, framePointIndex fg.val.2 b),
    framePointIndex_lt_of_lt fg.val.1 fg.val.2 fg.property a b⟩

theorem crossPointPair_fst (fg : Pair 13) (a b : Fin 3) :
    (crossPointPair fg a b).val.1 = framePointIndex fg.val.1 a := rfl

theorem crossPointPair_snd (fg : Pair 13) (a b : Fin 3) :
    (crossPointPair fg a b).val.2 = framePointIndex fg.val.2 b := rfl

variable {R : Type*} [CommRing R]

/-- Both numbered rows are the same weighted pairing minus the same C t. -/
theorem gRow_cross_eq_fRow_pair (h t : R) (fg : Pair 13) (a b : Fin 3) :
    gRow h t (gNumber (gCross fg a b)) =
      fRow h t (fNumber (fPair (crossPointPair fg a b))) := by
  have hFrames : fg.val.1.val ≠ fg.val.2.val :=
    ne_of_lt (show fg.val.1.val < fg.val.2.val from fg.property)
  rw [gRow_cross, fRow_pair]
  simp only [crossPointPair_fst, crossPointPair_snd, framePointIndex_div_three,
    if_neg hFrames]

/-- All cross-frame G polynomials belong to the ideal of actual F rows. -/
theorem cross_mem_fIdeal (h t : R) (fg : Pair 13) (a b : Fin 3) :
    gRow h t (gNumber (gCross fg a b)) ∈ fIdeal h t := by
  rw [gRow_cross_eq_fRow_pair]
  exact Ideal.subset_span ⟨fNumber (fPair (crossPointPair fg a b)), rfl⟩

end NativePolynomial.ConfigurationResiduals



#check @NativePolynomial.ConfigurationResiduals.framePointIndex_lt_of_lt
#check @NativePolynomial.ConfigurationResiduals.framePointIndex_div_three
#check @NativePolynomial.ConfigurationResiduals.crossPointPair
#check @NativePolynomial.ConfigurationResiduals.crossPointPair_fst
#check @NativePolynomial.ConfigurationResiduals.crossPointPair_snd
#check @NativePolynomial.ConfigurationResiduals.gRow_cross_eq_fRow_pair
#check @NativePolynomial.ConfigurationResiduals.cross_mem_fIdeal
#print axioms NativePolynomial.ConfigurationResiduals.framePointIndex_lt_of_lt
#print axioms NativePolynomial.ConfigurationResiduals.framePointIndex_div_three
#print axioms NativePolynomial.ConfigurationResiduals.crossPointPair
#print axioms NativePolynomial.ConfigurationResiduals.crossPointPair_fst
#print axioms NativePolynomial.ConfigurationResiduals.crossPointPair_snd
#print axioms NativePolynomial.ConfigurationResiduals.gRow_cross_eq_fRow_pair
#print axioms NativePolynomial.ConfigurationResiduals.cross_mem_fIdeal

/-
# Readouts against the original native complex quartet

The original coordinate and phase points are the independent native field
definitions in LiteralNativeQuartetBinder. Their actual point equalities
identify them with the included literal matrices, so the inherited finite
reconstruction theorem applies to the actual native Jordan trace readouts.
No purity, trace-one or MUB premise is needed for the visible-block result.

The second endpoint composes that result with the existing native square
and determinant normalization. Its explicit hypotheses are only the two
families of original readouts; its conclusion is idempotency iff the actual
scaled hidden matrix obeys U Uᴴ=I and det U=1. No bundled group, completion
classification or normalized arbitrary-ray definition is introduced.

These are locally authored compositions of the inherited compact Albert
coordinate dictionary and classical quartet reconstruction. No mathematical
novelty is claimed. Source attribution and full upstream notices remain
in the imported first-party modules. Thanks to the mathematical source
authors and to the Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/
module

public import LiteralNativeQuartetBinder

@[expose] public section
noncomputable section

namespace CompactAlbert

open UnitaryErrorBases.ComplexQuartet

/-- Equal actual readouts against the original twelve native anchors are
equivalent to visible block I/3, for arbitrary native x. -/
theorem native_literal_quartet_readouts_iff (x : Glennie.Albert) :
    ((∀ t : Fin 3,
        Glennie.trace (Glennie.jordan x (literalNativeCoordinatePoint t)) = (1 / 3 : ℝ)) ∧
      (∀ s t : PhaseIndex,
        Glennie.trace (Glennie.jordan x (literalNativePhasePoint s t)) = (1 / 3 : ℝ))) ↔
      hermitianMatrix (toTitsCoordinates x) =
        (1 / 3 : ℂ) • (1 : TitsComplexMatrix) := by
  simpa only [literalNativeCoordinatePoint_eq_included,
    literalNativePhasePoint_eq_included] using
      (native_included_quartet_readouts_iff x)

/-- Under the original twelve readout equations, actual native idempotency
is exactly the explicit special-unitary conditions on the scaled hidden block. -/
theorem native_idempotent_iff_scaled_specialUnitary_of_literal_quartet_readouts
    (x : Glennie.Albert)
    (hE : ∀ t : Fin 3,
      Glennie.trace (Glennie.jordan x (literalNativeCoordinatePoint t)) = (1 / 3 : ℝ))
    (hP : ∀ s t : PhaseIndex,
      Glennie.trace (Glennie.jordan x (literalNativePhasePoint s t)) = (1 / 3 : ℝ)) :
    Glennie.jordan x x = x ↔
      ((3 : ℂ) • (toTitsCoordinates x).2.2) *
          ((3 : ℂ) • (toTitsCoordinates x).2.2).conjTranspose =
            (1 : TitsComplexMatrix) ∧
        ((3 : ℂ) • (toTitsCoordinates x).2.2).det = 1 := by
  have ha : hermitianMatrix (toTitsCoordinates x) =
      (1 / 3 : ℂ) • (1 : TitsComplexMatrix) :=
    (native_literal_quartet_readouts_iff x).mp ⟨hE, hP⟩
  exact native_idempotent_iff_scaled_specialUnitary_conditions x ha

end CompactAlbert

#check CompactAlbert.native_literal_quartet_readouts_iff
#check CompactAlbert.native_idempotent_iff_scaled_specialUnitary_of_literal_quartet_readouts
#print axioms CompactAlbert.native_literal_quartet_readouts_iff
#print axioms CompactAlbert.native_idempotent_iff_scaled_specialUnitary_of_literal_quartet_readouts

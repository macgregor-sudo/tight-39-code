/-
# Native complementary triples and the ordered central alternatives

The actual native sum equal to the unit projects to zero hidden sum through
the existing real-linear coordinate equivalence. For three actual native
idempotents with the original twelve readouts, the checked point dictionary
then supplies special-unitary matrices U=3B. The existing ordered matrix
central-triple theorem gives the two possible orientations.

This first-party module only composes the native-coordinate results with
UnitaryErrorBases.specialUnitary_triple_sum_zero from CentralTriples. The
matrix argument is not copied or reproved. Its classical adjugate provenance
and complete mathlib attribution remain in that imported source; native
compact-Albert provenance and upstream notices remain in the other import.
No new mathematical result or novelty, converse frame theorem, gauge action
or completion classification is asserted.
Thanks to the mathematical source authors and the Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/
module

public import LiteralNativeQuartetReadouts
public import CentralTriples

@[expose] public section
noncomputable section

namespace CompactAlbert

open UnitaryErrorBases.ComplexQuartet UnitaryErrorBases.ThreeCycleFourier

/-- The actual native unit has zero hidden component, so a native triple
summing to that unit has zero sum of its scaled hidden matrices. -/
theorem native_scaled_hidden_sum_eq_zero_of_sum_eq_unit
    (x y z : Glennie.Albert) (hsum : x + y + z = 1) :
    ((3 : ℂ) • (toTitsCoordinates x).2.2) +
        ((3 : ℂ) • (toTitsCoordinates y).2.2) +
        ((3 : ℂ) • (toTitsCoordinates z).2.2) = 0 := by
  have hcoords := congrArg
    (fun a : Glennie.Albert => compactTitsCoordinateEquiv a) hsum
  rw [map_add, map_add, compactTitsCoordinateEquiv_unit] at hcoords
  have hhidden := congrArg (fun q : TitsCoordinates => q.2.2) hcoords
  change (toTitsCoordinates x).2.2 + (toTitsCoordinates y).2.2 +
    (toTitsCoordinates z).2.2 = 0 at hhidden
  simpa only [smul_add, smul_zero] using
    congrArg (fun B : TitsComplexMatrix => (3 : ℂ) • B) hhidden

/-- Three actual native idempotents with the original quartet readouts and
sum equal to the unit have exactly the two ordered central alternatives
for U=3B. No orthogonality or frame-classification premise is assumed. -/
theorem native_complementary_triple_hidden_central_alternatives
    (p : Fin 3 → Glennie.Albert)
    (hidem : ∀ i : Fin 3, Glennie.jordan (p i) (p i) = p i)
    (hE : ∀ i t : Fin 3,
      Glennie.trace (Glennie.jordan (p i) (literalNativeCoordinatePoint t)) = (1 / 3 : ℝ))
    (hP : ∀ (i : Fin 3) (s t : PhaseIndex),
      Glennie.trace (Glennie.jordan (p i) (literalNativePhasePoint s t)) = (1 / 3 : ℝ))
    (hsum : p 0 + p 1 + p 2 = 1) :
    let U : Fin 3 → TitsComplexMatrix :=
      fun i => (3 : ℂ) • (toTitsCoordinates (p i)).2.2
    (U 1 = omega • U 0 ∧ U 2 = omega ^ 2 • U 0) ∨
      (U 1 = omega ^ 2 • U 0 ∧ U 2 = omega • U 0) := by
  let U : Fin 3 → TitsComplexMatrix :=
    fun i => (3 : ℂ) • (toTitsCoordinates (p i)).2.2
  change (U 1 = omega • U 0 ∧ U 2 = omega ^ 2 • U 0) ∨
    (U 1 = omega ^ 2 • U 0 ∧ U 2 = omega • U 0)
  have hSU (i : Fin 3) : U i ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
    have hpair : U i * (U i).conjTranspose = (1 : TitsComplexMatrix) ∧
        (U i).det = 1 :=
      (native_idempotent_iff_scaled_specialUnitary_of_literal_quartet_readouts
        (p i) (hE i) (hP i)).mp (hidem i)
    apply Matrix.mem_specialUnitaryGroup_iff.mpr
    refine ⟨Matrix.mem_unitaryGroup_iff.mpr ?_, hpair.2⟩
    simpa only [Matrix.star_eq_conjTranspose] using hpair.1
  have hUzero : U 0 + U 1 + U 2 = 0 :=
    native_scaled_hidden_sum_eq_zero_of_sum_eq_unit (p 0) (p 1) (p 2) hsum
  have hroot : omega ^ 2 + omega + 1 = 0 := by
    rw [omega_sq]
    ring
  exact UnitaryErrorBases.specialUnitary_triple_sum_zero
    (U 0) (U 1) (U 2) omega hroot (hSU 0) (hSU 1) (hSU 2) hUzero

end CompactAlbert

#check CompactAlbert.native_scaled_hidden_sum_eq_zero_of_sum_eq_unit
#check CompactAlbert.native_complementary_triple_hidden_central_alternatives
#print axioms CompactAlbert.native_scaled_hidden_sum_eq_zero_of_sum_eq_unit
#print axioms CompactAlbert.native_complementary_triple_hidden_central_alternatives

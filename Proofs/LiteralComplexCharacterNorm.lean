/-
# Unit complex characters and the selected native-ray denominator

The checked character is a natural power of the checked cube root omega.
Multiplicativity and nonnegativity of Complex.normSq suffice to prove its
norm is one. The resulting native norm and denominator identities concern
only these characters. No arbitrary fixed-scale outer product is asserted
to be a normalized projector.

These locally authored elementary adapters connect the original packet2.2
unit-phase vv*/3 formula to the denominator in MASTER6.3. They use the
actual quaternion-pair octonion norm, without an inverse coordinate map,
phase case expansion, new abstract structure or novelty claim. Mathematical
and Lean/mathlib attribution remains in the imported first-party sources.
Thanks to the source authors and the Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/
module

public import LiteralNativeQuartetBinder

@[expose] public section
noncomputable section

namespace CompactAlbert

open UnitaryErrorBases.ComplexQuartet UnitaryErrorBases.ThreeCycleFourier

private theorem omega_normSq_eq_one : Complex.normSq omega = 1 := by
  have hcube : Complex.normSq omega ^ 3 = 1 := by
    simpa only [map_pow, map_one] using
      congrArg (fun z : ℂ => Complex.normSq z) omega_cube
  have hfactor :
      (Complex.normSq omega - 1) *
        (Complex.normSq omega ^ 2 + Complex.normSq omega + 1) = 0 := by
    nlinarith [hcube]
  rcases mul_eq_zero.mp hfactor with h | h
  · exact sub_eq_zero.mp h
  · have hn := Complex.normSq_nonneg omega
    have hs := sq_nonneg (Complex.normSq omega)
    nlinarith

/-- Every selected character has squared complex norm one. -/
theorem character_normSq_eq_one (t : PhaseIndex) :
    Complex.normSq (character t) = 1 := by
  unfold character
  rw [map_pow, omega_normSq_eq_one, one_pow]

/-- The selected character has squared norm one in the actual native
quaternion-pair octonions, using the fixed scalar/i embedding. -/
theorem complexOctonion_character_normSq_eq_one (t : PhaseIndex) :
    Glennie.octNormSq (complexOctonion (character t)) = 1 := by
  calc
    Glennie.octNormSq (complexOctonion (character t)) =
        Complex.normSq (character t) := by
      simp [complexOctonion, Glennie.octNormSq, Quaternion.normSq_def',
        Complex.normSq_apply, pow_two]
    _ = 1 := character_normSq_eq_one t

/-- On the selected original phase rays, the general squared-ray-norm
denominator is exactly the packet's fixed denominator three. -/
theorem literalNativePhasePoint_denominator_eq_three (s t : PhaseIndex) :
    1 + Glennie.octNormSq (complexOctonion (character t)) +
        Glennie.octNormSq (complexOctonion (character (s - t))) = (3 : ℝ) := by
  rw [complexOctonion_character_normSq_eq_one,
    complexOctonion_character_normSq_eq_one]
  norm_num

end CompactAlbert

#check CompactAlbert.character_normSq_eq_one
#check CompactAlbert.complexOctonion_character_normSq_eq_one
#check CompactAlbert.literalNativePhasePoint_denominator_eq_three
#print axioms CompactAlbert.character_normSq_eq_one
#print axioms CompactAlbert.complexOctonion_character_normSq_eq_one
#print axioms CompactAlbert.literalNativePhasePoint_denominator_eq_three

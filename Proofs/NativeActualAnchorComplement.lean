module

public import NativeActualStateEquivalence

@[expose] public section

/-!
The complement of the actual canonical native anchors 0–11.
This composes accepted actual/literal label identities, Hermitian trace reality
and the literal quartet reconstruction; no new native points or purity premises.
First-party proof composition; inherited source attribution remains in the
accepted owners and pinned Mathlib (065356127b1dc0016f66b7283ce0ce2c4055aa55).
Thanks to their contributors. “If I have seen further it is by standing on the
sholders of Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
namespace CompactAlbert.ActualQuartetStates

open NativePolynomial.ConfigurationResiduals
open QuadraticCertificate.ExactCKMConfiguration
open QuadraticCertificate.ExactCKMSharedFrames
open UnitaryErrorBases.ComplexQuartet
open scoped BigOperators

private theorem visible_zero_of_zero_readouts (A : TitsComplexMatrix)
    (hA : A.IsHermitian)
    (hE : ∀ t : Fin 3, (A * coordinateProjector t).trace.re = 0)
    (hP : ∀ s t : PhaseIndex, (A * phaseProjector s t).trace.re = 0) : A = 0 := by
  have hEc (t : Fin 3) : (A * coordinateProjector t).trace = 0 := by
    rw [← trace_mul_eq_real_of_isHermitian A _ hA (coordinateProjector_isHermitian t), hE t]
    rfl
  have hPc (s t : PhaseIndex) : (A * phaseProjector s t).trace = 0 := by
    rw [← trace_mul_eq_real_of_isHermitian A _ hA (phaseProjector_isHermitian s t), hP s t]
    rfl
  have htrace : A.trace = 0 := by
    calc
      A.trace = (A * (∑ t : Fin 3, coordinateProjector t)).trace := by
        rw [coordinateProjector_sum, Matrix.mul_one]
      _ = ∑ t : Fin 3, (A * coordinateProjector t).trace := by
        rw [Matrix.mul_sum, Matrix.trace_sum]
      _ = 0 := by simp [hEc]
  have hrec := literal_quartet_reconstruction A
  simpa only [hEc, hPc, zero_smul, Finset.sum_const_zero, zero_add,
    htrace, add_zero] using hrec.symm

/-- Orthogonality to precisely the original first twelve canonical labels is
equivalent to zero visible Hermitian component. No idempotency or trace premise. -/
theorem actual_anchor_orthogonal_iff_visible_zero (x : Glennie.Albert) :
    (∀ i : Fin 39, i.val < 12 →
      Glennie.trace (Glennie.jordan x (nativePoint i)) = 0) ↔
      hermitianMatrix (toTitsCoordinates x) = 0 := by
  constructor
  · intro hx
    apply visible_zero_of_zero_readouts _ (hermitianMatrix_isHermitian _)
    · intro t
      have ht := hx (framePointIndex 0 t)
        ((actual_anchor_labels _).mpr (Or.inl ⟨t, rfl⟩))
      rw [congrFun nativePoint_coordinate_eq_literal t,
        literalNativeCoordinatePoint_eq_included] at ht
      exact (native_trace_jordan_includeHermitianMatrix x
        ⟨coordinateProjector t, coordinateProjector_isHermitian t⟩).symm.trans ht
    · intro s t
      let sf : Fin 3 := ⟨s.val, ZMod.val_lt s⟩
      let tf : Fin 3 := ⟨t.val, ZMod.val_lt t⟩
      have hs : (sf.val : PhaseIndex) = s := ZMod.natCast_zmod_val s
      have ht : (tf.val : PhaseIndex) = t := ZMod.natCast_zmod_val t
      have hst := hx (framePointIndex (sharedPhaseFrameLabel sf) tf)
        ((actual_anchor_labels _).mpr (Or.inr ⟨sf, tf, rfl⟩))
      rw [congrFun (nativePoint_phase_eq_literal sf) tf, hs, ht,
        literalNativePhasePoint_eq_included] at hst
      exact (native_trace_jordan_includeHermitianMatrix x
        ⟨phaseProjector s t, phaseProjector_isHermitian s t⟩).symm.trans hst
  · intro hzero i hi
    rcases (actual_anchor_labels i).mp hi with ⟨t, rfl⟩ | ⟨s, t, rfl⟩
    · rw [congrFun nativePoint_coordinate_eq_literal t,
        literalNativeCoordinatePoint_eq_included]
      change Glennie.trace (Glennie.jordan x (includeHermitianMatrix _)) = 0
      rw [native_trace_jordan_includeHermitianMatrix, hzero]
      simp
    · rw [congrFun (nativePoint_phase_eq_literal s) t,
        literalNativePhasePoint_eq_included]
      change Glennie.trace (Glennie.jordan x (includeHermitianMatrix _)) = 0
      rw [native_trace_jordan_includeHermitianMatrix, hzero]
      simp

/-- A real-linear map preserving the displayed native trace pairing and fixing
the actual twelve anchors preserves their hidden complement. Pairing preservation
is an explicit premise, not a consequence asserted for arbitrary automorphisms. -/
theorem visible_zero_preserved_of_trace_pairing_and_actual_anchor_fixing
    (f : Glennie.Albert →ₗ[ℝ] Glennie.Albert)
    (hpair : ∀ x y : Glennie.Albert,
      Glennie.trace (Glennie.jordan (f x) (f y)) = Glennie.trace (Glennie.jordan x y))
    (hfix : ∀ i : Fin 39, i.val < 12 → f (nativePoint i) = nativePoint i)
    (x : Glennie.Albert) (hx : hermitianMatrix (toTitsCoordinates x) = 0) :
    hermitianMatrix (toTitsCoordinates (f x)) = 0 := by
  apply (actual_anchor_orthogonal_iff_visible_zero (f x)).mp
  intro i hi
  rw [← hfix i hi, hpair]
  exact (actual_anchor_orthogonal_iff_visible_zero x).mpr hx i hi

end CompactAlbert.ActualQuartetStates

/-
# Actual canonical-quartet native states and special-unitary matrices

The domain uses the twelve actual original labels, native idempotency and
native Jordan trace readouts. Trace one is derived. The accepted native point
dictionary supplies the scaled hidden coordinate, constructor and both inverse
identities; this module packages them after proving exact label coverage.

These are first-party compositions of accepted classical compact Albert and
second-Tits results, not a new classification or copied proof implementation.
Inherited native source attribution and complete license notices remain in the
imported declaration owners. Thanks to those authors and the Lean and mathlib
contributors. “If I have seen further it is by standing on the sholders of
Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/
module

public import NativeComplementaryDictionary
public import NativeExactCKMSharedFramesProbe

@[expose] public section
noncomputable section

namespace CompactAlbert.ActualQuartetStates

open NativePolynomial.ConfigurationResiduals
open QuadraticCertificate.ExactCKMConfiguration
open QuadraticCertificate.ExactCKMSharedFrames
open UnitaryErrorBases.ComplexQuartet

/-- Readouts against precisely the first twelve actual native seed labels. -/
def ActualQuartetReadouts (x : Glennie.Albert) : Prop :=
  ∀ i : Fin 39, i.val < 12 →
    Glennie.trace (Glennie.jordan x (nativePoint i)) = (1 / 3 : ℝ)

/-- Native idempotency and actual quartet readouts; trace one is a consequence. -/
def ActualQuartetState (x : Glennie.Albert) : Prop :=
  Glennie.jordan x x = x ∧ ActualQuartetReadouts x

abbrev State := {x : Glennie.Albert // ActualQuartetState x}

/-- The explicit matrix equations, with the accepted adjoint convention. -/
abbrev SpecialUnitaryMatrix :=
  {U : TitsComplexMatrix // U * U.conjTranspose = 1 ∧ U.det = 1}

/-- The grouped coordinate and phase indices cover exactly actual labels 0–11. -/
theorem actual_anchor_labels (i : Fin 39) :
    i.val < 12 ↔
      (∃ t : Fin 3, i = framePointIndex 0 t) ∨
      ∃ s t : Fin 3, i = framePointIndex (sharedPhaseFrameLabel s) t := by
  constructor
  · intro hi
    by_cases hi3 : i.val < 3
    · let t : Fin 3 := ⟨i.val, hi3⟩
      have hIndex : framePointIndex 0 t = i := by
        apply Fin.ext
        dsimp only [framePointIndex, t]
        omega
      exact Or.inl ⟨t, hIndex.symm⟩
    · let s : Fin 3 := ⟨(i.val - 3) / 3, by omega⟩
      let t : Fin 3 := ⟨(i.val - 3) % 3, Nat.mod_lt _ (by decide)⟩
      have hIndex : framePointIndex (sharedPhaseFrameLabel s) t = i := by
        apply Fin.ext
        dsimp only [framePointIndex, sharedPhaseFrameLabel, s, t]
        omega
      exact Or.inr ⟨s, t, hIndex.symm⟩
  · rintro (⟨t, rfl⟩ | ⟨s, t, rfl⟩)
    · dsimp only [framePointIndex]
      omega
    · dsimp only [framePointIndex, sharedPhaseFrameLabel]
      omega

private theorem phase_fin_representative (s : PhaseIndex) :
    ∃ t : Fin 3, (t.val : PhaseIndex) = s := by
  have hCases : s = 0 ∨ s = 1 ∨ s = 2 :=
    (by decide : ∀ z : PhaseIndex, z = 0 ∨ z = 1 ∨ z = 2) s
  rcases hCases with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

/-- Actual first-twelve readouts are exactly the accepted literal quartet
readouts, including every phase and the original grouped outcome order. -/
theorem actualQuartetReadouts_iff_literal (x : Glennie.Albert) :
    ActualQuartetReadouts x ↔
      ((∀ t : Fin 3, Glennie.trace
          (Glennie.jordan x (literalNativeCoordinatePoint t)) = (1 / 3 : ℝ)) ∧
       (∀ s t : PhaseIndex, Glennie.trace
          (Glennie.jordan x (literalNativePhasePoint s t)) = (1 / 3 : ℝ))) := by
  constructor
  · intro hx
    constructor
    · intro t
      have hLabel := congrFun nativePoint_coordinate_eq_literal t
      rw [← hLabel]
      exact hx _ ((actual_anchor_labels _).mpr (Or.inl ⟨t, rfl⟩))
    · intro s t
      obtain ⟨sf, hsf⟩ := phase_fin_representative s
      obtain ⟨tf, htf⟩ := phase_fin_representative t
      have hLabel := congrFun (nativePoint_phase_eq_literal sf) tf
      rw [← hsf, ← htf, ← hLabel]
      exact hx _ ((actual_anchor_labels _).mpr (Or.inr ⟨sf, tf, rfl⟩))
  · rintro ⟨hE, hP⟩ i hi
    rcases (actual_anchor_labels i).mp hi with ⟨t, rfl⟩ | ⟨s, t, rfl⟩
    · rw [congrFun nativePoint_coordinate_eq_literal t]
      exact hE t
    · rw [congrFun (nativePoint_phase_eq_literal s) t]
      exact hP (s.val : PhaseIndex) (t.val : PhaseIndex)

/-- Visible component I/3 follows from the actual twelve readouts alone. -/
theorem visible_third_of_actualQuartetReadouts (x : Glennie.Albert)
    (hx : ActualQuartetReadouts x) :
    hermitianMatrix (toTitsCoordinates x) =
      (1 / 3 : ℂ) • (1 : TitsComplexMatrix) :=
  (native_literal_quartet_readouts_iff x).mp
    ((actualQuartetReadouts_iff_literal x).mp hx)

theorem trace_one_of_actualQuartetReadouts (x : Glennie.Albert)
    (hx : ActualQuartetReadouts x) : Glennie.trace x = 1 :=
  native_trace_eq_one_of_visible_third x (visible_third_of_actualQuartetReadouts x hx)

/-- The accepted native constructor satisfies the actual domain predicate. -/
theorem nativeComplementaryPoint_actualQuartetState (U : TitsComplexMatrix)
    (hU : U * U.conjTranspose = 1 ∧ U.det = 1) :
    ActualQuartetState (nativeComplementaryPoint U) :=
  ⟨(nativeComplementaryPoint_idempotent_iff U).mpr hU,
    (actualQuartetReadouts_iff_literal _).mpr (nativeComplementaryPoint_literal_readouts U)⟩

def stateToSpecialUnitary (x : State) : SpecialUnitaryMatrix :=
  ⟨(3 : ℂ) • (toTitsCoordinates x.val).2.2,
    (native_idempotent_iff_scaled_specialUnitary_of_literal_quartet_readouts x.val
      ((actualQuartetReadouts_iff_literal x.val).mp x.property.2).1
      ((actualQuartetReadouts_iff_literal x.val).mp x.property.2).2).mp x.property.1⟩

def specialUnitaryToState (U : SpecialUnitaryMatrix) : State :=
  ⟨nativeComplementaryPoint U.val, nativeComplementaryPoint_actualQuartetState U.val U.property⟩

/-- The inverse laws are the accepted native coordinate identities. -/
def stateEquivSpecialUnitary : State ≃ SpecialUnitaryMatrix where
  toFun := stateToSpecialUnitary
  invFun := specialUnitaryToState
  left_inv x := by
    apply Subtype.ext
    exact nativeComplementaryPoint_scaled_hidden_inverse x.val
      (visible_third_of_actualQuartetReadouts x.val x.property.2)
  right_inv U := by
    apply Subtype.ext
    exact nativeComplementaryPoint_scaled_hidden U.val

theorem stateEquivSpecialUnitary_apply (x : State) :
    (stateEquivSpecialUnitary x).val =
      (3 : ℂ) • (toTitsCoordinates x.val).2.2 := rfl

theorem stateEquivSpecialUnitary_symm_apply (U : SpecialUnitaryMatrix) :
    (stateEquivSpecialUnitary.symm U).val = nativeComplementaryPoint U.val := rfl

theorem stateEquivSpecialUnitary_left_inverse (x : State) :
    stateEquivSpecialUnitary.symm (stateEquivSpecialUnitary x) = x :=
  stateEquivSpecialUnitary.symm_apply_apply x

theorem stateEquivSpecialUnitary_right_inverse (U : SpecialUnitaryMatrix) :
    stateEquivSpecialUnitary (stateEquivSpecialUnitary.symm U) = U :=
  stateEquivSpecialUnitary.apply_symm_apply U

end CompactAlbert.ActualQuartetStates

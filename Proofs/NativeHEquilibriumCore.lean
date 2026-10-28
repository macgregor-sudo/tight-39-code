module

public import NativeHLiteralQ12Bridge
public import PointQ12Bridge
public import RowJacobian

@[expose] public section

namespace Option2.NativeStress.NativeH.Equilibrium

open ConfigurationResidualIndices QuarticCertificate.RowBridge

/-- The identical retained point expression used by Column3Pilot.baseQ12. -/
def baseQ12 (v : Fin 1053) : Q12 :=
  FourSheets.PointQ12.pointQ12
    (Fin.divNat (m := 39) (n := 27) v) (Fin.modNat (m := 39) (n := 27) v)

section Fast

variable {R : Type*} [CommRing R]

/-- Filter term indices before ring arithmetic; this changes only evaluation order. -/
def fastShapeEntry (h : R) (s : RowShape) (P : Fin 1053 → R) (a : Fin 1053) : R :=
  ((s.quadratic.filter fun e => e.1 == a).map fun e =>
    quadraticScale h s * (e.2.2 : R) * P e.2.1).sum +
  ((s.quadratic.filter fun e => e.2.1 == a).map fun e =>
    quadraticScale h s * (e.2.2 : R) * P e.1).sum +
  ((s.linear.filter fun e => e.1 == a).map fun e => (e.2 : R)).sum

theorem fastShapeEntry_eq (h : R) (s : RowShape) (P : Fin 1053 → R) (a : Fin 1053) :
    fastShapeEntry h s P a = shapeJacobianEntry h s P a := by
  unfold fastShapeEntry shapeJacobianEntry
  congr 1
  · generalize s.quadratic = q
    induction q with
    | nil => simp
    | cons e q ih =>
      by_cases hx : e.1 = a <;> by_cases hy : e.2.1 = a <;>
        simp [hx, hy, mul_add] at * <;> linear_combination ih
  · generalize s.linear = q
    induction q with
    | nil => simp
    | cons e q ih =>
      by_cases hx : e.1 = a <;> simp [hx, ih]

private theorem filtered_map_sum {α : Type*} (p : α → Bool) (f : α → R) (l : List α)
    (h : ∀ x ∈ l, p x = false → f x = 0) :
    ((l.filter p).map f).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hi := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    cases hp : p x with
    | false => simp [hp, hi, h x (by simp) hp]
    | true => simp [hp, hi]

/-- Typed residual labels avoid repeatedly evaluating fNumber's inverse. -/
def fastContraction (entries : List Entry) (spec : HSpec)
    (h : Q12) (P : Fin 1053 → Q12) (c : Fin 1053) : Q12 :=
  (((entries.filter fun e => (labelSlots e.label).contains (variableSlot c)).map fun e =>
    orientedQ12 spec e.coefficient * fastShapeEntry h (labelShape e.label) P c)).sum

theorem fastContraction_eq (entries : List Entry) (spec : HSpec)
    (h t : Q12) (P : Fin 1053 → Q12) (c : Fin 1053) :
    fastContraction entries spec h P c =
      (entries.map fun e => orientedQ12 spec e.coefficient *
        jacobianEntry h t (fNumber e.label) P c).sum := by
  unfold fastContraction
  simp only [fastShapeEntry_eq]
  rw [filtered_map_sum]
  · simp only [jacobianEntry, rowShape, fNumber.symm_apply_apply]
  · intro e _ he
    have hn : variableSlot c ∉ rowSlots (fNumber e.label) := by
      simpa [rowSlots] using he
    have hz := jacobianEntry_eq_zero_of_not_mem h t (fNumber e.label) P hn
    simpa only [jacobianEntry, rowShape, fNumber.symm_apply_apply, hz, mul_zero] using
      congrArg (fun z => orientedQ12 spec e.coefficient * z) hz

end Fast

theorem actual_fastContraction_eq (i : Fin 4) (a : Fin 3) (c : Fin 1053) :
    fastContraction (rawEntries i a) (hSpec i a) (Q12.lit 1 0 0 0 2) baseQ12 c =
      ((hEntriesQ12 i a).map fun e => e.2 *
        jacobianEntry (Q12.lit 1 0 0 0 2) (Q12.lit 1 0 0 0 3) e.1 baseQ12 c).sum := by
  rw [fastContraction_eq _ _ _ (Q12.lit 1 0 0 0 3)]
  simp only [hEntriesQ12, List.map_map, Function.comp_def]

end Option2.NativeStress.NativeH.Equilibrium

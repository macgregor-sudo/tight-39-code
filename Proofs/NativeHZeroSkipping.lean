module

public import NativeHEquilibriumCore

@[expose] public section

namespace Option2.NativeStress.NativeH.Equilibrium

open ConfigurationResidualIndices QuarticCertificate.RowBridge

private theorem drop_zero_terms {α R : Type*} [CommRing R]
    (p : α → Bool) (f : α → R) (l : List α)
    (h : ∀ x ∈ l, p x = false → f x = 0) :
    ((l.filter p).map f).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hi := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    cases hp : p x with
    | false => simp [hp, hi, h x (by simp) hp]
    | true => simp [hp, hi]

/-- Discard monomials whose differentiated point value is zero before multiplying. -/
def sparseShapeEntry (h : Q12) (s : RowShape) (P : Fin 1053 → Q12) (a : Fin 1053) : Q12 :=
  ((((s.quadratic.filter fun e => e.1 == a).filter fun e => P e.2.1 != 0)).map fun e =>
    quadraticScale h s * (e.2.2 : Q12) * P e.2.1).sum +
  ((((s.quadratic.filter fun e => e.2.1 == a).filter fun e => P e.1 != 0)).map fun e =>
    quadraticScale h s * (e.2.2 : Q12) * P e.1).sum +
  ((s.linear.filter fun e => e.1 == a).map fun e => (e.2 : Q12)).sum

theorem sparseShapeEntry_eq (h : Q12) (s : RowShape) (P : Fin 1053 → Q12) (a : Fin 1053) :
    sparseShapeEntry h s P a = fastShapeEntry h s P a := by
  have h1 := drop_zero_terms (fun e : Fin 1053 × Fin 1053 × ℤ => P e.2.1 != 0)
    (fun e => quadraticScale h s * (e.2.2 : Q12) * P e.2.1)
    (s.quadratic.filter fun e => e.1 == a) (by
      intro e _ he
      have hz : P e.2.1 = 0 := by simpa using he
      simp only [hz, mul_zero])
  have h2 := drop_zero_terms (fun e : Fin 1053 × Fin 1053 × ℤ => P e.1 != 0)
    (fun e => quadraticScale h s * (e.2.2 : Q12) * P e.1)
    (s.quadratic.filter fun e => e.2.1 == a) (by
      intro e _ he
      have hz : P e.1 = 0 := by simpa using he
      simp only [hz, mul_zero])
  unfold sparseShapeEntry fastShapeEntry
  rw [h1, h2]

/-- Skip zero row values before multiplying by their exact frozen H weights. -/
def sparseContraction (entries : List Entry) (spec : HSpec)
    (h : Q12) (P : Fin 1053 → Q12) (c : Fin 1053) : Q12 :=
  (((entries.filter fun e => (labelSlots e.label).contains (variableSlot c)).map fun e =>
    let z := sparseShapeEntry h (labelShape e.label) P c
    if z = 0 then 0 else orientedQ12 spec e.coefficient * z)).sum

theorem sparseContraction_eq (entries : List Entry) (spec : HSpec)
    (h : Q12) (P : Fin 1053 → Q12) (c : Fin 1053) :
    sparseContraction entries spec h P c = fastContraction entries spec h P c := by
  unfold sparseContraction fastContraction
  apply congrArg List.sum
  apply List.map_congr_left
  intro e _
  simp only [sparseShapeEntry_eq]
  split_ifs with hz
  · simp only [hz, mul_zero]
  · rfl

end Option2.NativeStress.NativeH.Equilibrium

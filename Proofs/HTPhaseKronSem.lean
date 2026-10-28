module

public import HTPhaseKronCore

@[expose] public section

/-! # Semantics of the phased column checks (generic, data-free; first-party)

For any commutative ring `R`, ring map `ι : Q12 →+* R` and units `U : Fin 4 → Rˣ` (the phase
variables), `PhiR ι U` is the phased configuration and `mono U m` the Laurent monomial `U^m`.
`colOK L c = true` implies `Σ_{pe ∈ L} ι(ℓ_pe) U^{x_pe} · shapeJacobianEntry(ι ½, rowShape, Φ, c) = 0`
identically in `U`. -/

set_option autoImplicit false
namespace Option2.NativeStress.HTPhaseKron
open NativeH NativeH.Equilibrium ConfigurationResidualIndices QuarticCertificate.RowBridge

section Sem
variable {R : Type*} [CommRing R] (ι : Q12 →+* R) (U : Fin 4 → Rˣ)

/-- The Laurent monomial `U^m`. -/
def mono (m : Ex) : R := ((U 0 ^ m.1 * U 1 ^ m.2.1 * U 2 ^ m.2.2.1 * U 3 ^ m.2.2.2 : Rˣ) : R)

theorem mono_add (x y : Ex) : mono U (Ex.add x y) = mono U x * mono U y := by
  simp only [mono, Ex.add, zpow_add, Units.val_mul]
  ring

/-- Value of one `(coefficient, exponent)` term. -/
def ev (t : Q12 × Ex) : R := ι t.1 * mono U t.2

/-- The phased configuration `Φ(U)`. -/
noncomputable def PhiR (v : Fin 1053) : R := ((phiTerms v).map (ev ι U)).sum

theorem sum_map_flatMap {α β : Type*} (l : List α) (f : α → List β) (g : β → R) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem map_quadraticScale (h : Q12) (s : RowShape) :
    ι (quadraticScale h s) = quadraticScale (ι h) s := by
  unfold quadraticScale; split <;> simp

theorem piece (j : Fin 1053) (k : Q12) (x : Ex) :
    (((phiTerms j).map fun t => (k * t.1, Ex.add x t.2)).map (ev ι U)).sum =
      ι k * mono U x * PhiR ι U j := by
  unfold PhiR
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp, ev, map_mul, mono_add]
  ring

theorem entryTerms_sum (pe : PEntry) (c : Fin 1053) :
    ((entryTerms pe c).map (ev ι U)).sum =
      ι pe.e.coefficient.toQ12 * mono U pe.x *
        shapeJacobianEntry (ι half) (labelShape pe.e.label) (PhiR ι U) c := by
  simp only [entryTerms, shapeJacobianEntry, List.map_append, List.sum_append, sum_map_flatMap]
  rw [mul_add, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro q _
    by_cases h1 : q.1 = c <;> by_cases h2 : q.2.1 = c <;>
      simp only [h1, h2, ↓reduceIte, List.map_append, List.sum_append, List.map_nil,
        List.sum_nil, piece, add_zero, zero_add, mul_zero, map_mul, map_quadraticScale,
        map_intCast] <;> ring
  · congr 1
    apply List.map_congr_left
    intro l _
    by_cases h : l.1 = c <;>
      simp only [h, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, mul_zero, ev, map_mul, map_intCast] <;> ring

theorem colTerms_sum (L : List PEntry) (c : Fin 1053) :
    ((colTerms L c).map (ev ι U)).sum =
      (L.map fun pe => ι pe.e.coefficient.toQ12 * mono U pe.x *
        shapeJacobianEntry (ι half) (labelShape pe.e.label) (PhiR ι U) c).sum := by
  unfold colTerms
  rw [sum_map_flatMap]
  congr 1
  apply List.map_congr_left
  intro pe _
  exact entryTerms_sum ι U pe c

theorem insertT_sum (t : Q12 × Ex) (L : List (Ex × Q12)) :
    ((insertT t L).map fun p => ι p.2 * mono U p.1).sum =
      ev ι U t + (L.map fun p => ι p.2 * mono U p.1).sum := by
  induction L with
  | nil => simp [insertT, ev]
  | cons hd rest ih =>
    obtain ⟨m, s⟩ := hd
    simp only [insertT]
    split_ifs with h
    · subst h; simp only [List.map_cons, List.sum_cons, map_add, ev]; ring
    · simp only [List.map_cons, List.sum_cons, ih]; ring

theorem collect_sum (l : List (Q12 × Ex)) :
    ((collect l).map fun p => ι p.2 * mono U p.1).sum = (l.map (ev ι U)).sum := by
  induction l with
  | nil => simp [collect]
  | cons t l ih =>
    have : collect (t :: l) = insertT t (collect l) := rfl
    rw [this, insertT_sum, ih]
    simp

theorem colOK_sum (L : List PEntry) (c : Fin 1053) (h : colOK L c = true) :
    (L.map fun pe => ι pe.e.coefficient.toQ12 * mono U pe.x *
        shapeJacobianEntry (ι half) (labelShape pe.e.label) (PhiR ι U) c).sum = 0 := by
  rw [← colTerms_sum, ← collect_sum]
  unfold colOK at h
  rw [List.all_eq_true] at h
  generalize collect (colTerms L c) = K at h ⊢
  induction K with
  | nil => simp
  | cons p K ih =>
    have hp : p.2 = 0 := by simpa using h p (by simp)
    simp only [List.map_cons, List.sum_cons, hp, map_zero, zero_mul, zero_add]
    exact ih fun q hq => h q (by simp [hq])

/-- Entries not reading the column's state contribute nothing. -/
theorem sum_filter_touches (L : List PEntry) (c : Fin 1053) (h t : R) (P : Fin 1053 → R) :
    (L.map fun pe => ι pe.e.coefficient.toQ12 * mono U pe.x *
        jacobianEntry h t (fNumber pe.e.label) P c).sum =
    ((L.filter (touches (variableSlot c))).map fun pe => ι pe.e.coefficient.toQ12 * mono U pe.x *
        jacobianEntry h t (fNumber pe.e.label) P c).sum := by
  induction L with
  | nil => simp
  | cons pe L ih =>
    by_cases ht : touches (variableSlot c) pe = true
    · simp [List.filter_cons, ht, ih]
    · have hz : jacobianEntry h t (fNumber pe.e.label) P c = 0 := by
        apply jacobianEntry_eq_zero_of_not_mem
        simp only [rowSlots, Equiv.symm_apply_apply]
        intro hm
        apply ht
        simpa [touches] using hm
      simp [List.filter_cons, ht, ih, hz]

end Sem

end Option2.NativeStress.HTPhaseKron

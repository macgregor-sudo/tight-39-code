module

public import HTPhaseKronT00Endpoint

@[expose] public section

/-! Non-vacuity of the all-phase T00 endpoint: the phased covector has a row of weight `1/2` at
every unit phase. First-party. -/

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Option2.NativeStress.HTPhaseKron
open CKM.NativeFirstOrder NativeH ConfigurationResidualIndices QuarticCertificate.RowBridge

theorem ellT00_ne_zero (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : ∃ r, ellT00 ξ hξ r = 1 / 2 := by
  obtain ⟨pe, rest, hL⟩ : ∃ pe rest, covT00 = pe :: rest := ⟨_, _, rfl⟩
  have hU := firstRowUnique_eq
  unfold firstRowUnique at hU
  rw [hL] at hU
  simp only [List.all_eq_true, decide_eq_true_eq] at hU
  refine ⟨fNumber pe.e.label, ?_⟩
  unfold ellT00
  rw [hL, List.map_cons, List.sum_cons, if_pos rfl]
  have hz : (rest.map fun q => if fNumber q.e.label = fNumber pe.e.label then
      Q12.toComplex q.e.coefficient.toQ12 * mono (Uph ξ hξ) q.x else 0).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    rw [if_neg (hU q hq)]
  have hpe : pe = ⟨idEntry 12 11 ⟨1, 0, 0, 0, 2, by decide⟩, (0, 0, 0, 0)⟩ :=
    (List.cons.inj hL).1.symm ▸ rfl
  rw [hz, add_zero, hpe]
  simp [mono, Literal.toQ12, Q12.toComplex_lit, idEntry]

end Option2.NativeStress.HTPhaseKron
#print axioms Option2.NativeStress.HTPhaseKron.ellT00_ne_zero

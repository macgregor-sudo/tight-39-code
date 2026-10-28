module

public import HTPhaseKronT00Endpoint

@[expose] public section

/-! # Row formula for a sparse phased covector (first-party, generic)

If the original row numbers of the entries of `L` are distinct, the row weight
`Σ_{q ∈ L} [fNumber q = r] f q` equals `f pe` at the row of an entry `pe ∈ L`, and `0` off the support. -/

set_option autoImplicit false
namespace Option2.NativeStress.HTPhaseComplete
open HTPhaseKron NativeH ConfigurationResidualIndices

theorem sum_ite_of_nodup (L : List PEntry) (f : PEntry → ℂ)
    (hnd : (L.map fun q => (fNumber q.e.label).val).Nodup) (pe : PEntry) (h : pe ∈ L) :
    (L.map fun q => if fNumber q.e.label = fNumber pe.e.label then f q else 0).sum = f pe := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨ha, hL⟩ := hnd
    have tail0 : ∀ b ∈ L, (fNumber b.e.label).val ≠ (fNumber a.e.label).val := by
      intro b hb e; exact ha (List.mem_map.mpr ⟨b, hb, e⟩)
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | hp
    · rw [if_pos rfl]
      have : (L.map fun q => if fNumber q.e.label = fNumber pe.e.label then f q else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        rw [if_neg (fun e => tail0 q hq (congrArg Fin.val e))]
      rw [this, add_zero]
    · have hne : fNumber a.e.label ≠ fNumber pe.e.label :=
        fun e => tail0 pe hp (congrArg Fin.val e).symm
      rw [if_neg hne, zero_add]
      exact ih hL hp

theorem sum_ite_of_not_mem (L : List PEntry) (f : PEntry → ℂ) (r : Fin 2184)
    (h : ∀ q ∈ L, fNumber q.e.label ≠ r) :
    (L.map fun q => if fNumber q.e.label = r then f q else 0).sum = 0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  rw [if_neg (h q hq)]

end Option2.NativeStress.HTPhaseComplete

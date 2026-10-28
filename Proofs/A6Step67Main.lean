module

public import A6SpecStep67
public import A6Step67Count
public import A6Step67Data00
public import A6Step67Data01

@[expose] public section

/-!
# STEP67: the 24-variable Hilbert-function bound (D7) for MONO's trinomials — lane STEP67 top module

`A6Compact.step67_bound : A6Compact.StmtD7`, i.e. for every `m`,
`finrank F (F[Fin 24]_m ⧸ ChainMid.quadricRelations MonoSound.t m) ≤ 4·C(m+5,5) + 1540·C(m+4,4)`.

* MONO side (`LeadingMonomialBound`, `MonoSound`, base): every record in `subData` (MONO's leading-monomial certificates for
  exactly the 765 generators of COUNT's `CertL2g`) passes the kernel checker `MonoKV.checkV` (`A6Step67DataKK`), so its key
  decodes to the leading exponent of an element of the relation span (`MonoSound.leadCert_of_checkV`), and
  `Mono.finrank_le_card_of_leadCerts` bounds the finrank by the number of degree-`m` exponents divisible by none of them.
* COUNT side (`StdCount`, `StdCert`, base; `A6Step67Count`): COUNT's split tree, relabelled into MONO's coordinates and
  re-checked by the kernel, bounds that number for every `m` (`Step67.std_count_bound`).
* Bridge (here): the count's generator list is literally the digit list of the certified keys (`gens_keys`, kernel-checked),
  and `Finsupp.equivFunOnFinite` identifies the two exponent types.
Provenance: project-internal reuse of lanes MONO and COUNT (base imports; certificate data selected by STEP67 py/gen.py).
-/

open MvPolynomial Module

namespace A6Compact.Step67
open MonoSound MonoKV StdCount

/-- MONO's records for the 765 generators, in COUNT's generator order. -/
def subData : List (Nat × Nat × Nat × Nat) := d00 ++ d01

theorem subData_ok : subData.all (fun x => Nat.ble x.1 7 && checkV x.1 x.2.1 x.2.2.1 x.2.2.2) = true := by
  simp only [subData, List.all_append, Bool.and_eq_true, d00_ok, d01_ok, and_self]

/-- the certified leading exponents used by step 7 -/
def Gsub : Set (Fin 24 →₀ ℕ) := {μ | ∃ x ∈ subData, μ = dec x.2.1}

theorem leadCert_of_mem_Gsub {μ : Fin 24 →₀ ℕ} (h : μ ∈ Gsub) : Mono.LeadCert MonoSound.t rK μ := by
  obtain ⟨x, hx, rfl⟩ := h
  have := List.all_eq_true.mp subData_ok x hx
  rw [Bool.and_eq_true] at this
  exact leadCert_of_checkV (Nat.le_of_ble_eq_true this.1) this.2

/-- the count's generators are the digit lists of the certified keys -/
theorem gens_keys : rootGens.map Kl = subData.map (fun x => x.2.1) := by decide +kernel

theorem gens_lt : rootGens.all (fun l => l.all (fun a => Nat.blt a 8)) = true := by decide +kernel

theorem dec_Kl (l : List ℕ) (hl : ∀ a ∈ l, a < 8) : (⇑(dec (Kl l)) : Fin 24 → ℕ) = den l := by
  funext i
  simp only [dec, Finsupp.coe_equivFunOnFinite_symm, den]
  exact Kl_digit l hl i

theorem dec_mem_Gsub {l : List ℕ} (hl : l ∈ rootGens) : dec (Kl l) ∈ Gsub := by
  have : Kl l ∈ subData.map (fun x => x.2.1) := gens_keys ▸ List.mem_map_of_mem hl
  obtain ⟨x, hx, hxk⟩ := List.mem_map.mp this
  exact ⟨x, hx, by rw [hxk]⟩

theorem lt8_of_mem {l : List ℕ} (hl : l ∈ rootGens) : ∀ a ∈ l, a < 8 := by
  intro a ha
  have h1 := List.all_eq_true.mp gens_lt l hl
  exact lt_of_blt_true (List.all_eq_true.mp h1 a ha)

end A6Compact.Step67

namespace A6Compact
open MonoSound StdCount Step67

/-- **D7** for MONO's trinomials `MonoSound.t` (lane STEP67 deliverable). -/
theorem step67_bound : StmtD7 := by
  intro m
  classical
  let A : Finset (Fin 24 → ℕ) :=
    (Finset.Nat.antidiagonalTuple 24 m).filter (Std (rootGens.map den) (Finset.univ : Finset (Fin 24)))
  let Sf : Finset (Fin 24 →₀ ℕ) := A.map Finsupp.equivFunOnFinite.symm.toEmbedding
  have hcard : Sf.card = cnt (rootGens.map den) (Finset.univ : Finset (Fin 24)) m := by
    simp only [Sf, A, Finset.card_map, cnt]
  refine le_trans (Mono.finrank_le_card_of_leadCerts MonoSound.t (fun s => tpoly_isHomogeneous s.2) rK rK_add Gsub
    (fun _ h => leadCert_of_mem_Gsub h) m Sf ?_) (hcard ▸ std_count_bound m)
  intro s hs hstd
  refine Finset.mem_map.mpr ⟨⇑s, Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩, by simp⟩
  · rw [Finset.Nat.mem_antidiagonalTuple, ← hs, Finsupp.degree_eq_sum]
  · intro i hi; exact absurd (Finset.mem_univ i) hi
  · intro g hg hle
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
    apply hstd _ (dec_mem_Gsub hl)
    intro i
    have := hle i
    rw [← dec_Kl l (lt8_of_mem hl)] at this
    exact this

end A6Compact

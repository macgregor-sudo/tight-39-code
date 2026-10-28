module

/-
# Generic Artin–Rees jet-length comparison

Original source: `claude-artin-rees-pilot-2026-10-23`, 2026-10-23.
AI-assisted authorship: Claude (Fable 5.1 and Opus). No project license has been
chosen; this file is first-party and copies no upstream proof body.

Pin: Lean v4.35.0-rc2, mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Mathematics (classical; Stacks 00IN, 00IV)

Let `R` be a commutative Noetherian ring, `E` a finite `R`-module, `S ≤ N`
submodules of `E`, `a` an ideal, and `M = N/S`.  Artin–Rees (Stacks 00IN,
mathlib `Ideal.exists_pow_inf_eq_pow_smul`) gives `c` with
`N ⊓ a^(n+c+1) E ≤ a^(n+1) N` for all `n`.  Write `l = n + c + 1`.

* Second isomorphism theorem / additivity (Stacks 00IV, mathlib
  `Module.length_eq_add_of_exact`): the exact sequence
  `N/(N ∩ (S + a^l E)) → E/(S + a^l E) → E/(N + a^l E)` gives
  `length E/(S + a^l E) = length N/(N ∩ (S + a^l E)) + length E/(N + a^l E)`.
* Artin–Rees plus the modular law `N ∩ (S + a^l E) = S + N ∩ a^l E`
  (`S ≤ N`) gives `N ∩ (S + a^l E) ≤ S + a^(n+1) N`, so `N/(N ∩ (S + a^l E))`
  surjects onto `N/(S + a^(n+1) N) ≅ M/a^(n+1) M`; length does not increase
  under a surjection (`Module.length_le_of_surjective`).

Hence `length M/a^(n+1)M + length E/(N + a^l E) ≤ length E/(S + a^l E)` in
`ℕ∞`, with `c` uniform in `n`.  The ideal case is `E = R`, `S = I`, `N = J`.
No finite-length, locality, or growth hypothesis is used or concluded.

## Interface

Public declarations:
* `ShiftedJetLength.QuotientSubmodule S N` — the module `N/S` as
  `N ⧸ Submodule.comap N.subtype S`.
* `ShiftedJetLength.exists_shifted_jet_length_comparison_submodule` — module form.
* `ShiftedJetLength.QuotientIdealModule I J` — `J/I` for ideals `I ≤ J`.
* `ShiftedJetLength.exists_shifted_jet_length_comparison` — the ideal-quotient form.
* `ShiftedJetLength.exists_length_quotient_smul_le` — the submodule inequality
  `length N/a^(n+1)N ≤ length E/a^(n+c+1)E`, derived from the module form.
-/
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Length
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

namespace ShiftedJetLength

open Submodule

section General

variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

/-- Length of a quotient depends only on the quotienting submodule. -/
theorem length_quotient_congr {p p' : Submodule R E} (h : p = p') :
    Module.length R (E ⧸ p) = Module.length R (E ⧸ p') :=
  (Submodule.quotEquivOfEq p p' h).length_eq

/-- Quotienting by a larger submodule gives a smaller (or equal) length:
`E ⧸ p → E ⧸ p'` is surjective when `p ≤ p'`. -/
theorem length_quotient_le_of_le {p p' : Submodule R E} (h : p ≤ p') :
    Module.length R (E ⧸ p') ≤ Module.length R (E ⧸ p) :=
  Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)

/-- Additivity along `N/(N ∩ A) → E/A → E/(N + A)` (second isomorphism theorem
composed with `Module.length_eq_add_of_exact`).  The kernel of the inclusion-induced
map `N → E/A` is `comap N.subtype A`, and its image is the kernel of
`E/A → E/(N ⊔ A)`. -/
theorem length_quotient_eq_add (N A : Submodule R E) :
    Module.length R (E ⧸ A) =
      Module.length R (N ⧸ Submodule.comap N.subtype A) +
        Module.length R (E ⧸ (N ⊔ A)) := by
  have hker : Submodule.comap N.subtype A = LinearMap.ker (A.mkQ ∘ₗ N.subtype) := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  let f : (N ⧸ Submodule.comap N.subtype A) →ₗ[R] E ⧸ A :=
    (Submodule.comap N.subtype A).liftQ (A.mkQ ∘ₗ N.subtype) (le_of_eq hker)
  let g : (E ⧸ A) →ₗ[R] E ⧸ (N ⊔ A) := Submodule.factor (le_sup_right : A ≤ N ⊔ A)
  refine Module.length_eq_add_of_exact f g ?_ (Submodule.factor_surjective _) ?_
  · exact LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ _ hker)
  · rw [LinearMap.exact_iff]
    simp only [f, g, Submodule.range_liftQ, LinearMap.range_comp, Submodule.range_subtype,
      Submodule.ker_mapQ, Submodule.comap_id, Submodule.map_sup, Submodule.mkQ_map_self,
      sup_bot_eq]

/-- Iterated quotient by an ideal multiple: `((E/S)/(a·(E/S)))` has the length of
`E/(S + a·E)` (third isomorphism theorem `Submodule.quotientQuotientEquivQuotientSup`
after rewriting `a • ⊤ = (a • ⊤).map S.mkQ`). -/
theorem length_quotient_quotient_smul_top (S : Submodule R E) (a : Ideal R) :
    Module.length R ((E ⧸ S) ⧸ (a • (⊤ : Submodule R (E ⧸ S)))) =
      Module.length R (E ⧸ (S ⊔ a • (⊤ : Submodule R E))) := by
  have h : (a • ⊤ : Submodule R (E ⧸ S)) = (a • (⊤ : Submodule R E)).map S.mkQ := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  rw [length_quotient_congr h]
  exact (Submodule.quotientQuotientEquivQuotientSup S _).length_eq

/-- **Artin–Rees**, shifted form: there is `c` with
`N ⊓ a^(n+c+1) E ≤ a^(n+1) N` for every `n`.  Derived from mathlib's
`Ideal.exists_pow_inf_eq_pow_smul` (`a^l • ⊤ ⊓ N = a^(l-c) • (a^c • ⊤ ⊓ N)` for `l ≥ c`)
at `l = n + c + 1`, using `a^c • ⊤ ⊓ N ≤ N`. -/
theorem exists_inf_pow_smul_top_le [IsNoetherianRing R] [Module.Finite R E]
    (a : Ideal R) (N : Submodule R E) :
    ∃ c : ℕ, ∀ n : ℕ, N ⊓ a ^ (n + c + 1) • (⊤ : Submodule R E) ≤ a ^ (n + 1) • N := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul a N
  refine ⟨k, fun n => ?_⟩
  rw [inf_comm, hk (n + k + 1) (by omega), show n + k + 1 - k = n + 1 by omega]
  exact smul_mono_right _ inf_le_right

/-- The key inclusion inside `N`: if `S ≤ N` and `N ⊓ a^l E ≤ a^k N`, then the
pullback of `S + a^l E` to `N` lies in `(pullback of S) + a^k N`.
Elementwise: `x ∈ N`, `x = s + y` with `s ∈ S ≤ N`, `y ∈ a^l E`; then
`y = x - s ∈ N ⊓ a^l E ≤ a^k N`, and `a^k N = (a^k • ⊤).map N.subtype`
(`Submodule.map_smul''`, `Submodule.map_subtype_top`). -/
theorem comap_subtype_sup_le {N S : Submodule R E} (hSN : S ≤ N) {a : Ideal R} {k l : ℕ}
    (hAR : N ⊓ a ^ l • (⊤ : Submodule R E) ≤ a ^ k • N) :
    Submodule.comap N.subtype (S ⊔ a ^ l • (⊤ : Submodule R E)) ≤
      Submodule.comap N.subtype S ⊔ a ^ k • (⊤ : Submodule R N) := by
  intro x hx
  rw [Submodule.mem_comap, Submodule.mem_sup] at hx
  obtain ⟨s, hs, y, hy, hsy⟩ := hx
  have hyN : y ∈ N := by
    have := N.sub_mem x.2 (hSN hs)
    rwa [show (x : E) = N.subtype x from rfl, ← hsy, add_sub_cancel_left] at this
  have hy' : y ∈ a ^ k • N := hAR ⟨hyN, hy⟩
  rw [← Submodule.map_subtype_top N, ← Submodule.map_smul''] at hy'
  obtain ⟨y', hy'', rfl⟩ := hy'
  rw [Submodule.mem_sup]
  refine ⟨⟨s, hSN hs⟩, hs, y', hy'', ?_⟩
  apply Subtype.ext
  simpa using hsy

/-- The `R`-module `N/S` for submodules `S ≤ N` of `E`: the quotient of `N` by the
pullback of `S` along the inclusion `N → E`. -/
abbrev QuotientSubmodule (S N : Submodule R E) : Type _ :=
  N ⧸ Submodule.comap N.subtype S

/-- **Generic shifted jet-length comparison, module form.**  For a Noetherian ring `R`,
a finite module `E`, submodules `S ≤ N`, and an ideal `a`, there is `c` such that for all
`n`, in `ℕ∞`,
`length (N/S)/(a^(n+1)·(N/S)) + length E/(N + a^(n+c+1) E) ≤ length E/(S + a^(n+c+1) E)`. -/
theorem exists_shifted_jet_length_comparison_submodule [IsNoetherianRing R] [Module.Finite R E]
    (a : Ideal R) (S N : Submodule R E) (hSN : S ≤ N) :
    ∃ c : ℕ, ∀ n : ℕ,
      Module.length R
          (QuotientSubmodule S N ⧸
            (a ^ (n + 1) • (⊤ : Submodule R (QuotientSubmodule S N)))) +
        Module.length R (E ⧸ (N ⊔ a ^ (n + c + 1) • (⊤ : Submodule R E))) ≤
      Module.length R (E ⧸ (S ⊔ a ^ (n + c + 1) • (⊤ : Submodule R E))) := by
  obtain ⟨c, hc⟩ := exists_inf_pow_smul_top_le a N
  refine ⟨c, fun n => ?_⟩
  rw [length_quotient_quotient_smul_top, length_quotient_eq_add N (S ⊔ _),
    length_quotient_congr (show N ⊔ (S ⊔ a ^ (n + c + 1) • (⊤ : Submodule R E)) =
      N ⊔ a ^ (n + c + 1) • ⊤ by rw [← sup_assoc, sup_eq_left.mpr hSN])]
  exact add_le_add (length_quotient_le_of_le (comap_subtype_sup_le hSN (hc n))) le_rfl

/-- Milestone corollary (`S = ⊥`): `length N/a^(n+1)N ≤ length E/a^(n+c+1)E` uniformly in `n`.
Not a substitute for the three-term comparison. -/
theorem exists_length_quotient_smul_le [IsNoetherianRing R] [Module.Finite R E]
    (a : Ideal R) (N : Submodule R E) :
    ∃ c : ℕ, ∀ n : ℕ,
      Module.length R (N ⧸ (a ^ (n + 1) • (⊤ : Submodule R N))) ≤
        Module.length R (E ⧸ (a ^ (n + c + 1) • (⊤ : Submodule R E))) := by
  -- From the module form at `S = ⊥`: `N ⧸ comap N.subtype ⊥ ≃ₗ N` (`quotEquivOfEqBot`),
  -- transported through `Submodule.Quotient.equiv` with `map e (a • ⊤) = a • ⊤`;
  -- then `⊥ ⊔ p = p` and `le_self_add`/`le_add_right`.
  obtain ⟨c, hc⟩ := exists_shifted_jet_length_comparison_submodule a ⊥ N bot_le
  refine ⟨c, fun n => ?_⟩
  have hbot : Submodule.comap N.subtype (⊥ : Submodule R E) = ⊥ := by
    rw [Submodule.comap_bot, Submodule.ker_subtype]
  let e : QuotientSubmodule (⊥ : Submodule R E) N ≃ₗ[R] N :=
    Submodule.quotEquivOfEqBot _ hbot
  have hmap : (a ^ (n + 1) • (⊤ : Submodule R (QuotientSubmodule (⊥ : Submodule R E) N))).map
      (e : QuotientSubmodule (⊥ : Submodule R E) N →ₗ[R] N) = a ^ (n + 1) • ⊤ := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  have h1 := (Submodule.Quotient.equiv _ _ e hmap).length_eq
  have h2 := hc n
  rw [bot_sup_eq] at h2
  rw [← h1]
  exact le_trans le_self_add h2

end General

section Ideals

variable {R : Type*} [CommRing R]

/-- `J/I` as an `R`-module for ideals `I ≤ J`: the quotient of `J` by the pullback of `I`
along the inclusion `J → R`.  Written with explicit `Submodule.comap` so that it does not
resolve to the ring-hom `Ideal.comap`. -/
abbrev QuotientIdealModule (I J : Ideal R) : Type _ :=
  J ⧸ Submodule.comap (Submodule.subtype (J : Submodule R R)) (I : Submodule R R)

/-- **Ideal-quotient comparison**: for a Noetherian
ring `R`, ideals `I ≤ J` and any ideal `m`, there is `c` such that for every `N`, in `ℕ∞`,
`length (J/I)/m^(N+1)(J/I) + length R/(J + m^(N+c+1)) ≤ length R/(I + m^(N+c+1))`.
Specialization of the module form at `E = R`, with `m^k • ⊤ = m^k`
(`Ideal.smul_eq_mul`/`Ideal.mul_top` or equivalent) transported by `length_quotient_congr`. -/
theorem exists_shifted_jet_length_comparison [IsNoetherianRing R]
    (m I J : Ideal R) (hIJ : I ≤ J) :
    ∃ c : ℕ, ∀ N : ℕ,
      Module.length R
          (QuotientIdealModule I J ⧸
            ((m ^ (N + 1)) • (⊤ : Submodule R (QuotientIdealModule I J)))) +
        Module.length R (R ⧸ (J ⊔ m ^ (N + c + 1))) ≤
      Module.length R (R ⧸ (I ⊔ m ^ (N + c + 1))) := by
  obtain ⟨c, hc⟩ := exists_shifted_jet_length_comparison_submodule (E := R) m I J hIJ
  refine ⟨c, fun n => ?_⟩
  have e : ∀ k : ℕ, (m ^ k • (⊤ : Submodule R R)) = m ^ k := fun k => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have h := hc n
  rw [e] at h
  exact h

end Ideals

end ShiftedJetLength

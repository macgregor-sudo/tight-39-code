module

/-
Adoption attribution: source https://github.com/ImperialCollegeLondon/FLT,
commit 923d45174c500aa1d994ba973bac38ea39eacbf7,
original FLT/Slop/DimensionTheorem/DimLeGrowth.lean, Akhil Mathew,
Apache-2.0. Original copyright/license and the detailed adaptation notices below
are retained. This staging adds attribution only; proof modifications are those
identified in the incoming port's provenance ledger. Thank you to Akhil Mathew
and the FLT and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/
/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew (upstream lemmas); chain-argument inductive step adapted for this port.
-/
/- PROVENANCE (file level)
  Upstream: ImperialCollegeLondon/FLT, commit 923d45174c500aa1d994ba973bac38ea39eacbf7
  File: FLT/Slop/DimensionTheorem/DimLeGrowth.lean (lines 1-390)
  Author: Akhil Mathew
  SPDX-License-Identifier: Apache-2.0  (upstream LICENSE copied verbatim to LICENSE-FLT)
  Modification notice: ported to Lean v4.35.0-rc2 / mathlib 065356127b1d; module-system
  syntax dropped; namespace `DimensionTheorem` -> `GrowthDimension`.
  STRUCTURAL ADAPTATION: the imports
  `Mathlib.RingTheory.KrullDimension.Field` and `Mathlib.RingTheory.KrullDimension.Regular`
  are removed, together with upstream `ringKrullDim_le_of_forall_minimalPrimes`
  (lines 314-350) and the uses of `ringKrullDim_eq_zero_of_isField`,
  `Ideal.exists_minimalPrimes_le` and
  `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`.
  The inductive step of `ringKrullDim_le_of_growthLE` is replaced by an elementary
  chain argument (new lemma `length_le_ringKrullDim_of_ker_le`, adapted from the
  chain-transport construction of upstream lines 314-350). Upstream lines 69-313 are
  verbatim except that `hilbertSamuel_zero` / `hilbertSamuel_coe` are made public.
  Upstream lines 1-68 (header, imports, module docstring) are rewritten to describe
  the port; plain `import`s replace upstream's `public import`s.
-/
public import GrowthDimension.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

/-!
# `dim R ≤ d(R)`

The Krull dimension of a Noetherian local ring is at most the growth degree
of its Hilbert–Samuel function (Stacks Project, tag 00KQ; Atiyah–Macdonald, Ch. 11),
in the growth-order formulation of `d(R)`.

## Strategy: induction on `d` (`ringKrullDim_le_of_growthLE`)

* **Base case `d = 0`** (`ringKrullDim_le_zero_of_growthLE_zero`, upstream verbatim):
  bounded `ℓ(R/𝔪ⁿ)` stabilizes, Nakayama gives `𝔪ⁿ = ⊥`, so `dim R ≤ 0`.
* **Inductive step** (port-local chain argument, replacing upstream's reduction to
  minimal primes and Mathlib's `KrullDimension.Regular`): given a chain
  `q₀ < q₁ < ⋯ < q_ℓ` of primes of `R` with `ℓ > 0`, pass to the local domain
  `R' = R ⧸ q₀`, whose Hilbert–Samuel function is dominated by that of `R`.
  Pick `x ∈ q₁ \ q₀`; its image `x'` is a nonzero element of `𝔪_{R'}`.
  Artin–Rees (`exists_hilbertSamuel_quotient_span_singleton_add_le`, upstream
  verbatim) and the telescoping lemma drop the growth degree of `R' ⧸ (x')` by one,
  so by induction `dim (R' ⧸ (x')) ≤ d`. The kernel of `R → R' ⧸ (x')` lies in `q₁`,
  so the tail `q₁ < ⋯ < q_ℓ` maps to a chain of length `ℓ - 1` in `R' ⧸ (x')`
  (`length_le_ringKrullDim_of_ker_le`), giving `ℓ ≤ d + 1`.

## Main result

* `GrowthDimension.ringKrullDim_le_of_growthLE` :
  `GrowthLE (hilbertSamuel R) d → ringKrullDim R ≤ d`.
-/

/- Some lemmas below do not use all the section variables; keep the statements
exactly as in the interface rather than `omit`-ting hypotheses. -/
set_option linter.unusedSectionVars false

namespace GrowthDimension

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-! ### Auxiliary lemmas -/

-- PROVENANCE: upstream lines 71-78, adapted: `private` removed (used by Consumer.lean).
omit [IsNoetherianRing R] in
lemma hilbertSamuel_zero : hilbertSamuel R 0 = 0 := by
  have : Subsingleton (R ⧸ (maximalIdeal R ^ 0)) := by
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.Quotient.subsingleton_iff.mpr rfl
  unfold hilbertSamuel colength
  rw [Module.length_eq_zero]
  rfl

-- PROVENANCE: upstream lines 80-88, adapted: `private` removed (used by Consumer.lean).
lemma hilbertSamuel_coe (n : ℕ) :
    (hilbertSamuel R n : ℕ∞) = Module.length R (R ⧸ maximalIdeal R ^ n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (R ⧸ (maximalIdeal R ^ 0)) := by
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.Quotient.subsingleton_iff.mpr rfl
    rw [hilbertSamuel_zero, Module.length_eq_zero, Nat.cast_zero]
  · exact colength_coe (radical_pow_eq_of_radical_eq
      (maximalIdeal.isMaximal R).isPrime.radical hn.ne')

omit [IsNoetherianRing R] in
/-- The image of the maximal ideal in a proper quotient is the maximal ideal. -/
private lemma map_mk_maximalIdeal (I : Ideal R) [Nontrivial (R ⧸ I)] :
    (maximalIdeal R).map (Ideal.Quotient.mk I) = maximalIdeal (R ⧸ I) := by
  have hI : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp ‹_›
  have := IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr (le_maximalIdeal hI)]

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- The length of a double quotient over `R ⧸ I` equals the length of the
corresponding single quotient over `R`. -/
private lemma length_quotient_map_quotient (I J : Ideal R) :
    Module.length (R ⧸ I) ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) =
      Module.length R (R ⧸ (I ⊔ J)) := by
  rw [← Module.length_eq_of_surjective (S := R) (R := R ⧸ I)
      (M := (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I))
      (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ R I J).toLinearEquiv.length_eq

omit [IsNoetherianRing R] in
/-- The Hilbert–Samuel function of `R ⧸ I` as a colength in `R`. -/
private lemma hilbertSamuel_quotient_eq (I : Ideal R) [Nontrivial (R ⧸ I)] (n : ℕ) :
    hilbertSamuel (R ⧸ I) n = colength R (I ⊔ maximalIdeal R ^ n) := by
  have hI : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp ‹_›
  have hmax : maximalIdeal (R ⧸ I) ^ n = (maximalIdeal R ^ n).map (Ideal.Quotient.mk I) := by
    rw [← map_mk_maximalIdeal I, Ideal.map_pow]
  unfold hilbertSamuel colength
  rw [hmax, length_quotient_map_quotient]

/-! ### The five main lemmas -/

/-- The Hilbert–Samuel function decreases when passing to a proper quotient ring. -/
lemma hilbertSamuel_quotient_le (I : Ideal R) [Nontrivial (R ⧸ I)] (n : ℕ) :
    hilbertSamuel (R ⧸ I) n ≤ hilbertSamuel R n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [hilbertSamuel_zero]
    exact Nat.zero_le _
  · have hrad : (maximalIdeal R ^ n).radical = maximalIdeal R :=
      radical_pow_eq_of_radical_eq (maximalIdeal.isMaximal R).isPrime.radical hn.ne'
    rw [hilbertSamuel_quotient_eq I n]
    exact colength_le_colength le_sup_right hrad

/-- **Artin–Rees difference bound.** In a Noetherian local domain, quotienting by
`0 ≠ x ∈ 𝔪` drops the Hilbert–Samuel function by at least a shifted copy of
itself: there is `c > 0` with
`hs_{R/(x)}(n) + hs_R(n - c) ≤ hs_R(n)` for all `n ≥ c`. -/
lemma exists_hilbertSamuel_quotient_span_singleton_add_le [IsDomain R] {x : R}
    (hx : x ∈ maximalIdeal R) (hx0 : x ≠ 0)
    [Nontrivial (R ⧸ Ideal.span {x})] :
    ∃ c, 0 < c ∧ ∀ n, c ≤ n →
      hilbertSamuel (R ⧸ Ideal.span {x}) n + hilbertSamuel R (n - c) ≤
        hilbertSamuel R n := by
  -- Artin–Rees, applied to `N = (x)` inside `M = R`.
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal R)
    ((Ideal.span {x} : Ideal R) : Submodule R R)
  have htop : ∀ J : Ideal R, J • (⊤ : Submodule R R) = J := fun J => by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  refine ⟨k + 1, Nat.succ_pos k, fun n hn => ?_⟩
  -- Step 1: the colon ideal `(𝔪ⁿ : x)` is contained in `𝔪^(n - (k+1))`.
  have hcolon : ∀ r : R, r * x ∈ maximalIdeal R ^ n →
      r ∈ maximalIdeal R ^ (n - (k + 1)) := by
    intro r hr
    have h1 : r * x ∈ (maximalIdeal R ^ n • (⊤ : Submodule R R)) ⊓
        ((Ideal.span {x} : Ideal R) : Submodule R R) := by
      rw [htop]
      exact Submodule.mem_inf.mpr ⟨hr, Ideal.mem_span_singleton.mpr (dvd_mul_left x r)⟩
    rw [hk n (le_trans (Nat.le_succ k) hn)] at h1
    have h2 : r * x ∈ (maximalIdeal R ^ (n - k)) •
        ((Ideal.span {x} : Ideal R) : Submodule R R) :=
      Submodule.smul_mono le_rfl inf_le_right h1
    obtain ⟨t, ht, hteq⟩ := Submodule.mem_smul_span_singleton.mp h2
    have htr : t = r := mul_right_cancel₀ hx0 (by rwa [smul_eq_mul] at hteq)
    exact Ideal.pow_le_pow_right (Nat.sub_le_sub_left (Nat.le_succ k) n) (htr ▸ ht)
  have hn1 : 1 ≤ n := le_trans (Nat.le_add_left 1 k) hn
  -- Step 2: length bookkeeping over `R`.
  -- The map `r ↦ r x mod 𝔪ⁿ`.
  set φ : R →ₗ[R] R ⧸ ((maximalIdeal R ^ n : Ideal R) : Submodule R R) :=
    (Submodule.mkQ ((maximalIdeal R ^ n : Ideal R) : Submodule R R)) ∘ₗ
      LinearMap.toSpanSingleton R R x with hφ
  have hφapply : ∀ r : R, φ r = Submodule.Quotient.mk (r * x) := fun r => by
    simp [hφ, LinearMap.toSpanSingleton_apply, smul_eq_mul]
  have hkerle : LinearMap.ker φ ≤ ((maximalIdeal R ^ (n - (k + 1)) : Ideal R) : Submodule R R) := by
    intro r hr
    rw [LinearMap.mem_ker, hφapply, Submodule.Quotient.mk_eq_zero] at hr
    exact hcolon r hr
  have hrange : LinearMap.range φ =
      Submodule.map (Submodule.mkQ ((maximalIdeal R ^ n : Ideal R) : Submodule R R))
        ((Ideal.span {x} : Ideal R) : Submodule R R) := by
    rw [hφ, LinearMap.range_comp, LinearMap.range_toSpanSingleton]
  -- The middle term of the additivity formula equals `ℓ(R ⧸ ker φ)`.
  have hmapJ : Submodule.map (Submodule.mkQ ((maximalIdeal R ^ n : Ideal R) : Submodule R R))
        (((Ideal.span {x} ⊔ maximalIdeal R ^ n : Ideal R)) : Submodule R R) =
      Submodule.map (Submodule.mkQ ((maximalIdeal R ^ n : Ideal R) : Submodule R R))
        ((Ideal.span {x} : Ideal R) : Submodule R R) := by
    rw [Submodule.map_sup]
    have hbot : Submodule.map (Submodule.mkQ ((maximalIdeal R ^ n : Ideal R) : Submodule R R))
        ((maximalIdeal R ^ n : Ideal R) : Submodule R R) = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨z, hz, rfl⟩
      simp only [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hz
    rw [hbot, sup_bot_eq]
  have hquot : Module.length R
      (Submodule.map (Submodule.mkQ ((maximalIdeal R ^ n : Ideal R) : Submodule R R))
        ((Ideal.span {x} : Ideal R) : Submodule R R)) =
      Module.length R (R ⧸ LinearMap.ker φ) :=
    ((φ.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange)).length_eq).symm
  -- Surjection `R ⧸ ker φ ↠ R ⧸ 𝔪^(n-(k+1))`.
  have hsurj : Module.length R (R ⧸ maximalIdeal R ^ (n - (k + 1))) ≤
      Module.length R (R ⧸ LinearMap.ker φ) := by
    have hle : LinearMap.ker φ ≤
        Submodule.comap LinearMap.id
          ((maximalIdeal R ^ (n - (k + 1)) : Ideal R) : Submodule R R) := by
      simpa using hkerle
    refine Module.length_le_of_surjective
      (Submodule.mapQ (LinearMap.ker φ) _ LinearMap.id hle) ?_
    intro y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk z, rfl⟩
  -- Additivity of length: `ℓ(R/𝔪ⁿ) = ℓ(R ⧸ ker φ) + ℓ(R/((x) ⊔ 𝔪ⁿ))`.
  have hadd := length_quotient_eq_add (maximalIdeal R ^ n)
    (Ideal.span {x} ⊔ maximalIdeal R ^ n) le_sup_right
  rw [hmapJ, hquot] at hadd
  -- Assemble the `ℕ∞` inequality.
  have hmain : Module.length R (R ⧸ (Ideal.span {x} ⊔ maximalIdeal R ^ n)) +
      Module.length R (R ⧸ maximalIdeal R ^ (n - (k + 1))) ≤
      Module.length R (R ⧸ maximalIdeal R ^ n) := by
    calc Module.length R (R ⧸ (Ideal.span {x} ⊔ maximalIdeal R ^ n)) +
        Module.length R (R ⧸ maximalIdeal R ^ (n - (k + 1)))
        ≤ Module.length R (R ⧸ (Ideal.span {x} ⊔ maximalIdeal R ^ n)) +
          Module.length R (R ⧸ LinearMap.ker φ) := add_le_add le_rfl hsurj
      _ = Module.length R (R ⧸ LinearMap.ker φ) +
          Module.length R (R ⧸ (Ideal.span {x} ⊔ maximalIdeal R ^ n)) := add_comm _ _
      _ = Module.length R (R ⧸ maximalIdeal R ^ n) := hadd.symm
  -- Convert to `ℕ`.
  have hradJ : (Ideal.span {x} ⊔ maximalIdeal R ^ n).radical = maximalIdeal R := by
    refine le_antisymm ?_ ?_
    · have hJm : Ideal.span {x} ⊔ maximalIdeal R ^ n ≤ maximalIdeal R :=
        sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hx)
          (Ideal.pow_le_self (by omega : n ≠ 0))
      exact (Ideal.radical_mono hJm).trans_eq (maximalIdeal.isMaximal R).isPrime.radical
    · calc maximalIdeal R
          = (maximalIdeal R ^ n).radical :=
            (radical_pow_eq_of_radical_eq (maximalIdeal.isMaximal R).isPrime.radical
              (by omega : n ≠ 0)).symm
        _ ≤ (Ideal.span {x} ⊔ maximalIdeal R ^ n).radical := Ideal.radical_mono le_sup_right
  have hcoeq : (hilbertSamuel (R ⧸ Ideal.span {x}) n : ℕ∞) =
      Module.length R (R ⧸ (Ideal.span {x} ⊔ maximalIdeal R ^ n)) := by
    rw [hilbertSamuel_quotient_eq (Ideal.span {x}) n, colength_coe hradJ]
  have hfinal : ((hilbertSamuel (R ⧸ Ideal.span {x}) n +
      hilbertSamuel R (n - (k + 1)) : ℕ) : ℕ∞) ≤ ((hilbertSamuel R n : ℕ) : ℕ∞) := by
    push_cast
    rw [hcoeq, hilbertSamuel_coe, hilbertSamuel_coe]
    exact hmain
  exact_mod_cast hfinal

/-- **Base case**: bounded Hilbert–Samuel function forces dimension `≤ 0`. -/
lemma ringKrullDim_le_zero_of_growthLE_zero
    (h : GrowthLE (hilbertSamuel R) 0) : ringKrullDim R ≤ 0 := by
  obtain ⟨C, hC⟩ := h
  simp only [pow_zero, mul_one] at hC
  -- Step 1: the Hilbert–Samuel function stabilizes.
  obtain ⟨n, hn1, heq⟩ : ∃ n, 1 ≤ n ∧ hilbertSamuel R (n + 1) = hilbertSamuel R n := by
    by_contra hcon
    have hlt : ∀ m, 1 ≤ m → hilbertSamuel R m < hilbertSamuel R (m + 1) := by
      intro m hm
      rcases lt_or_eq_of_le (hilbertSamuel_monotone (R := R) (Nat.le_succ m)) with hlt | heq
      · exact hlt
      · exact absurd ⟨m, hm, heq.symm⟩ hcon
    have key : ∀ m : ℕ, m + hilbertSamuel R 1 ≤ hilbertSamuel R (m + 1) := by
      intro m
      induction m with
      | zero => simp
      | succ j ih =>
        have h2 := hlt (j + 1) (by omega)
        omega
    have h3 := key (C + 1)
    have h4 := hC (C + 1 + 1)
    omega
  -- Step 2: hence `𝔪ⁿ ≤ 𝔪ⁿ⁺¹`.
  have hfin : Module.length R (R ⧸ maximalIdeal R ^ n) ≠ ⊤ :=
    length_quotient_ne_top_of_radical_eq
      (radical_pow_eq_of_radical_eq (maximalIdeal.isMaximal R).isPrime.radical (by omega : n ≠ 0))
  have hlen : Module.length R (R ⧸ maximalIdeal R ^ (n + 1)) =
      Module.length R (R ⧸ maximalIdeal R ^ n) := by
    rw [← hilbertSamuel_coe, ← hilbertSamuel_coe, heq]
  have hbot : maximalIdeal R ^ n ≤ maximalIdeal R ^ (n + 1) := by
    have hadd := length_quotient_eq_add (maximalIdeal R ^ (n + 1)) (maximalIdeal R ^ n)
      (Ideal.pow_le_pow_right (Nat.le_succ n))
    rw [hlen] at hadd
    have hmid0 : Module.length R
        (Submodule.map (Submodule.mkQ ((maximalIdeal R ^ (n + 1) : Ideal R) : Submodule R R))
          ((maximalIdeal R ^ n : Ideal R) : Submodule R R)) = 0 :=
      WithTop.add_right_cancel hfin (hadd.symm.trans (zero_add _).symm)
    have := Module.length_eq_zero_iff.mp hmid0
    have hbot' :
        Submodule.map
          (Submodule.mkQ ((maximalIdeal R ^ (n + 1) : Ideal R) : Submodule R R))
          ((maximalIdeal R ^ n : Ideal R) : Submodule R R) = ⊥ :=
      Submodule.eq_bot_of_subsingleton
    intro y hy
    have hmem := hbot' ▸ Submodule.mem_map_of_mem (f := Submodule.mkQ _) hy
    rw [Submodule.mem_bot] at hmem
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
  -- Step 3: Nakayama gives `𝔪ⁿ = ⊥`.
  have hpow : maximalIdeal R ^ n = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) _
      (IsNoetherian.noetherian _) ?_ (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    rw [Ideal.smul_eq_mul, mul_comm, ← pow_succ]
    exact hbot
  -- Step 4: every prime is the maximal ideal, so the dimension is `0`.
  have hprime : ∀ p : PrimeSpectrum R, p.asIdeal = maximalIdeal R := by
    intro p
    have := p.2
    refine le_antisymm (le_maximalIdeal p.2.ne_top) ?_
    have hle : maximalIdeal R ^ n ≤ p.asIdeal := hpow ▸ bot_le
    exact (Ideal.IsPrime.pow_le_iff (by omega : n ≠ 0)).mp hle
  rw [ringKrullDim, Order.krullDim_nonpos_iff_forall_isMax]
  intro q r _
  have : q = r := PrimeSpectrum.ext ((hprime q).trans (hprime r).symm)
  exact this ▸ le_rfl


/- PROVENANCE: new for this port (replaces upstream lines 314-350,
  `ringKrullDim_le_of_forall_minimalPrimes`). The chain-transport construction
  (`hcomap`, `hprime'`, the `step` proof and the final `calc`) is adapted from
  upstream FLT/Slop/DimensionTheorem/DimLeGrowth.lean lines 320-349
  (commit 923d45174c500aa1d994ba973bac38ea39eacbf7, author Akhil Mathew,
  SPDX-License-Identifier: Apache-2.0); changed: the quotient map `R → R ⧸ p` is
  generalised to any surjective ring hom `π` whose kernel lies under the head of the
  chain, and no minimal prime is chosen. -/
omit [IsLocalRing R] [IsNoetherianRing R] in
/-- A chain of primes whose head contains the kernel of a surjection `π : R →+* S`
maps to a chain of the same length in `S`. -/
lemma length_le_ringKrullDim_of_ker_le {S : Type*} [CommRing S] (π : R →+* S)
    (hπ : Function.Surjective π) (c : LTSeries (PrimeSpectrum R))
    (hker : RingHom.ker π ≤ c.head.asIdeal) :
    ((c.length : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim S := by
  have hmono : ∀ i : Fin (c.length + 1), RingHom.ker π ≤ (c i).asIdeal := fun i =>
    le_trans hker (c.monotone (Fin.zero_le i) : c.head.asIdeal ≤ (c i).asIdeal)
  have hcomap : ∀ I : Ideal R, RingHom.ker π ≤ I → (I.map π).comap π = I := by
    intro I hI
    rw [Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hI]
  have hprime' : ∀ i : Fin (c.length + 1), (((c i).asIdeal).map π).IsPrime := by
    intro i
    have := (c i).2
    exact Ideal.map_isPrime_of_surjective hπ (hmono i)
  let c' : LTSeries (PrimeSpectrum S) :=
    { length := c.length
      toFun := fun i => ⟨((c i).asIdeal).map π, hprime' i⟩
      step := fun i => by
        change (((c i.castSucc).asIdeal).map π) < (((c i.succ).asIdeal).map π)
        have hlt : (c i.castSucc).asIdeal < (c i.succ).asIdeal := c.step i
        refine lt_of_le_of_ne (Ideal.map_mono hlt.le) fun he => hlt.ne ?_
        rw [← hcomap _ (hmono i.castSucc), he, hcomap _ (hmono i.succ)] }
  calc ((c.length : ℕ∞) : WithBot ℕ∞) = ((c'.length : ℕ∞) : WithBot ℕ∞) := rfl
    _ ≤ Order.krullDim (PrimeSpectrum S) := Order.LTSeries.length_le_krullDim c'
    _ = ringKrullDim S := by rw [ringKrullDim]

/- PROVENANCE: upstream lines 352-388, adapted. Statement verbatim (namespace aside);
  base case verbatim; the `succ` case is new (elementary chain argument, see the file
  header): it reuses upstream `hilbertSamuel_quotient_le`,
  `exists_hilbertSamuel_quotient_span_singleton_add_le`, `GrowthLE.of_le_sub`,
  `map_mk_maximalIdeal` and the `Nontrivial` argument of upstream lines 376-380. -/
/-- **`dim R ≤ d(R)`, inductive form**: any bound on the growth of the
Hilbert–Samuel function bounds the Krull dimension. -/
theorem ringKrullDim_le_of_growthLE :
    ∀ (d : ℕ) (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      GrowthLE (hilbertSamuel R) d → ringKrullDim R ≤ (d : WithBot ℕ∞) := by
  intro d
  induction d with
  | zero =>
    intro R _ _ _ h
    simpa using ringKrullDim_le_zero_of_growthLE_zero h
  | succ d ih =>
    intro R _ _ _ h
    rw [ringKrullDim, Order.krullDim, iSup_le_iff]
    intro c
    by_cases hlen : c.length = 0
    · rw [hlen]
      exact_mod_cast Nat.zero_le (d + 1)
    -- The first two primes of the chain.
    set q₀ := c.head with hq₀
    set q₁ := (c.tail hlen).head with hq₁
    have hq01 : q₀.asIdeal < q₁.asIdeal := by
      rw [hq₀, hq₁, RelSeries.head_tail]
      exact c.strictMono (show (0 : Fin (c.length + 1)) < 1 from by
        rw [Fin.lt_def, Fin.val_one', Nat.mod_eq_of_lt (by omega)]; exact Nat.zero_lt_one)
    -- The local domain `R' = R ⧸ q₀`.
    have : Nontrivial (R ⧸ q₀.asIdeal) :=
      Ideal.Quotient.nontrivial_iff.mpr q₀.2.ne_top
    have : IsDomain (R ⧸ q₀.asIdeal) := Ideal.Quotient.isDomain q₀.asIdeal
    have hS : GrowthLE (hilbertSamuel (R ⧸ q₀.asIdeal)) (d + 1) :=
      h.of_le fun m => hilbertSamuel_quotient_le q₀.asIdeal m
    -- An element `x ∈ q₁ \ q₀`.
    obtain ⟨x, hxq₁, hxq₀⟩ := IsConcreteLE.exists_of_lt hq01
    set x' := Ideal.Quotient.mk q₀.asIdeal x with hx'
    have hx0 : x' ≠ 0 := fun h0 => hxq₀ (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    have hxmem : x' ∈ maximalIdeal (R ⧸ q₀.asIdeal) := by
      rw [← map_mk_maximalIdeal q₀.asIdeal]
      exact Ideal.mem_map_of_mem _ (le_maximalIdeal q₁.2.ne_top hxq₁)
    have hxle : Ideal.span {x'} ≤ maximalIdeal (R ⧸ q₀.asIdeal) :=
      (Ideal.span_singleton_le_iff_mem _).mpr hxmem
    have : Nontrivial ((R ⧸ q₀.asIdeal) ⧸ Ideal.span {x'}) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hxle)
    -- Artin–Rees plus telescoping, then the induction hypothesis.
    obtain ⟨k, hk, hAR⟩ := exists_hilbertSamuel_quotient_span_singleton_add_le hxmem hx0
    have hdrop : GrowthLE (hilbertSamuel ((R ⧸ q₀.asIdeal) ⧸ Ideal.span {x'})) d :=
      GrowthLE.of_le_sub hk hS hilbertSamuel_monotone hAR
    have hdim := ih _ hdrop
    -- Chain transport along `π : R → R' ⧸ (x')`.
    let π : R →+* (R ⧸ q₀.asIdeal) ⧸ Ideal.span {x'} :=
      (Ideal.Quotient.mk (Ideal.span {x'})).comp (Ideal.Quotient.mk q₀.asIdeal)
    have hπ : Function.Surjective π :=
      Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
    have hker : RingHom.ker π ≤ q₁.asIdeal := by
      have hspan : Ideal.span {x'} ≤ q₁.asIdeal.map (Ideal.Quotient.mk q₀.asIdeal) :=
        (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ hxq₁)
      intro a ha
      have ha' : Ideal.Quotient.mk q₀.asIdeal a ∈ Ideal.span {x'} := by
        rw [RingHom.mem_ker] at ha
        exact Ideal.Quotient.eq_zero_iff_mem.mp ha
      have := hspan ha'
      rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hq01.le] at this
      exact this
    have htail := length_le_ringKrullDim_of_ker_le π hπ (c.tail hlen) hker
    have hle := htail.trans hdim
    simp only [RelSeries.tail_length] at hle
    have hle' : c.length - 1 ≤ d := by exact_mod_cast hle
    have hfin : c.length ≤ d + 1 := by omega
    exact_mod_cast hfin

end GrowthDimension

module

/-
PROVENANCE: new, first-party file for this port (not from upstream FLT).
It only composes the ported upstream results; no upstream code is copied here.
-/
public import GrowthDimension.DimLeGrowth

@[expose] public section

/-!
# Index-shifted consumer interface

The consuming project indexes jet quotients as `R ⧸ 𝔪^(N+1)`, while the upstream
Hilbert–Samuel function is `n ↦ ℓ(R ⧸ 𝔪ⁿ)`. This file converts a polynomial bound
on the shifted lengths (for all `N`, or eventually in `N`) into
`GrowthLE (hilbertSamuel R) e`, and composes with
`GrowthDimension.ringKrullDim_le_of_growthLE`.

Nothing about analytic rings, irreducible components, or any particular growth
bound is claimed here.
-/

namespace GrowthDimension

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A bound `ℓ(R ⧸ 𝔪^(N+1)) ≤ C (N+1)^e` for all `N` gives growth degree `≤ e`. -/
theorem growthLE_of_shifted_bound {e C : ℕ}
    (h : ∀ N, Module.length R (R ⧸ maximalIdeal R ^ (N + 1)) ≤ ((C * (N + 1) ^ e : ℕ) : ℕ∞)) :
    GrowthLE (hilbertSamuel R) e := by
  refine ⟨C, fun n => ?_⟩
  rcases n with _ | N
  · rw [hilbertSamuel_zero]
    exact Nat.zero_le _
  · have h1 : (hilbertSamuel R (N + 1) : ℕ∞) ≤ ((C * (N + 1) ^ e : ℕ) : ℕ∞) := by
      rw [hilbertSamuel_coe]
      exact h N
    have h2 : hilbertSamuel R (N + 1) ≤ C * (N + 1) ^ e := by exact_mod_cast h1
    exact h2.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.le_succ _) e))

/-- An eventual bound `ℓ(R ⧸ 𝔪^(N+1)) ≤ C (N+1)^e` gives growth degree `≤ e`; the finitely
many small indices are absorbed by monotonicity, with explicit constant
`C + hilbertSamuel R (N₀ + 1)`. -/
theorem growthLE_of_eventually_shifted_bound {e C : ℕ}
    (h : ∀ᶠ N in Filter.atTop,
      Module.length R (R ⧸ maximalIdeal R ^ (N + 1)) ≤ ((C * (N + 1) ^ e : ℕ) : ℕ∞)) :
    GrowthLE (hilbertSamuel R) e := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨C + hilbertSamuel R (N₀ + 1), fun n => ?_⟩
  have hpos : 1 ≤ (n + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos n)
  by_cases hn : n ≤ N₀ + 1
  · calc hilbertSamuel R n ≤ hilbertSamuel R (N₀ + 1) := hilbertSamuel_monotone hn
      _ ≤ C + hilbertSamuel R (N₀ + 1) := Nat.le_add_left _ _
      _ = (C + hilbertSamuel R (N₀ + 1)) * 1 := (mul_one _).symm
      _ ≤ (C + hilbertSamuel R (N₀ + 1)) * (n + 1) ^ e := Nat.mul_le_mul_left _ hpos
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    have h1 : (hilbertSamuel R (N + 1) : ℕ∞) ≤ ((C * (N + 1) ^ e : ℕ) : ℕ∞) := by
      rw [hilbertSamuel_coe]
      exact hN₀ N (by omega)
    have h2 : hilbertSamuel R (N + 1) ≤ C * (N + 1) ^ e := by exact_mod_cast h1
    calc hilbertSamuel R (N + 1) ≤ C * (N + 1) ^ e := h2
      _ ≤ C * (N + 1 + 1) ^ e :=
          Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.le_succ _) e)
      _ ≤ (C + hilbertSamuel R (N₀ + 1)) * (N + 1 + 1) ^ e :=
          Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

/-- `dim R ≤ e` from a uniform shifted bound. -/
theorem ringKrullDim_le_of_shifted_bound {e C : ℕ}
    (h : ∀ N, Module.length R (R ⧸ maximalIdeal R ^ (N + 1)) ≤ ((C * (N + 1) ^ e : ℕ) : ℕ∞)) :
    ringKrullDim R ≤ (e : WithBot ℕ∞) :=
  ringKrullDim_le_of_growthLE e R (growthLE_of_shifted_bound h)

/-- `dim R ≤ e` from an eventual shifted bound. -/
theorem ringKrullDim_le_of_eventually_shifted_bound {e C : ℕ}
    (h : ∀ᶠ N in Filter.atTop,
      Module.length R (R ⧸ maximalIdeal R ^ (N + 1)) ≤ ((C * (N + 1) ^ e : ℕ) : ℕ∞)) :
    ringKrullDim R ≤ (e : WithBot ℕ∞) :=
  ringKrullDim_le_of_growthLE e R (growthLE_of_eventually_shifted_bound h)

end GrowthDimension

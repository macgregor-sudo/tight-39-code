module

public import HTPhaseKronCheck00_0
public import HTPhaseKronCheck00_1
public import HTPhaseKronCheck00_2
public import HTPhaseKronCheck00_3
public import HTPhaseKronCheck00_4
public import HTPhaseKronCheck00_5
public import HTPhaseKronCheck00_6
public import HTPhaseKronCheck00_7
public import HTPhaseKronCheck00_8
public import HTPhaseKronSem

@[expose] public section

/-! # L2 for T00: the pure T00 covector is an equilibrium covector at EVERY phase

`t00_phased_equilibrium`: for every commutative ring `R`, ring map `ι : Q12 →+* R` and units
`U : Fin 4 → Rˣ`, the phased covector `ℓ(U)_pe = ι(ℓ_pe) U^(x_pe)` annihilates every original
Jacobian column at the phased configuration `PhiR ι U` (all 2184 original rows through their
typed labels, all 1053 columns). Specialising `R = ℂ`, `ι = Q12.toComplex`, `U = ξ/ξ_base` gives
the statement at every literal phase, resonant or not; the identification of `PhiR` with
`literalCfg ξ` is a separate bridge. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option Elab.async false
namespace Option2.NativeStress.HTPhaseKron
open NativeH NativeH.Equilibrium ConfigurationResidualIndices QuarticCertificate.RowBridge

instance instDecEqLiteral : DecidableEq Literal := fun a b =>
  decidable_of_iff (a.A = b.A ∧ a.B = b.B ∧ a.C = b.C ∧ a.D = b.D ∧ a.denominator = b.denominator)
    (by
      cases a; cases b
      constructor
      · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

instance instDecEqEntry : DecidableEq Entry := fun a b =>
  decidable_of_iff (a.label = b.label ∧ a.coefficient = b.coefficient)
    (by
      cases a; cases b
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl⟩)

instance instDecEqPEntry : DecidableEq PEntry := fun a b =>
  decidable_of_iff (a.e = b.e ∧ a.x = b.x)
    (by
      cases a; cases b
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl⟩)

/-- The per-state lists are exactly the state filters of `covT00`. -/
theorem covAt00_spec : ∀ s : Fin 39, covT00.filter (touches s) = covAt00 s.val := by
  intro s; fin_cases s <;> decide +kernel

theorem state_of_chunks (L : List PEntry) (p : ℕ) (h0 : okRange L (27 * p + 0) 9 = true)
    (h1 : okRange L (27 * p + 9) 9 = true) (h2 : okRange L (27 * p + 18) 9 = true)
    (k : ℕ) (hk : k < 27) (hc : 27 * p + k < 1053) : colOK L ⟨27 * p + k, hc⟩ = true := by
  have key : ∀ lo, okRange L lo 9 = true → lo ≤ 27 * p + k → 27 * p + k < lo + 9 →
      colOK L ⟨27 * p + k, hc⟩ = true := by
    intro lo h hl hu
    have := okRange_spec L lo 9 h (27 * p + k - lo) (by omega) (by omega)
    have e : lo + (27 * p + k - lo) = 27 * p + k := by omega
    simpa only [e] using this
  rcases (by omega : k < 9 ∨ (9 ≤ k ∧ k < 18) ∨ 18 ≤ k) with h | h | h
  · exact key _ h0 (by omega) (by omega)
  · exact key _ h1 (by omega) (by omega)
  · exact key _ h2 (by omega) (by omega)

theorem state00_0 (k : ℕ) (_hk : k < 27) (hc : 27 * 0 + k < 1053) :
    colOK (covAt00 0) ⟨27 * 0 + k, hc⟩ = true := rfl
theorem state00_1 (k : ℕ) (_hk : k < 27) (hc : 27 * 1 + k < 1053) :
    colOK (covAt00 1) ⟨27 * 1 + k, hc⟩ = true := rfl
theorem state00_2 (k : ℕ) (_hk : k < 27) (hc : 27 * 2 + k < 1053) :
    colOK (covAt00 2) ⟨27 * 2 + k, hc⟩ = true := rfl
theorem state00_3 (k : ℕ) (_hk : k < 27) (hc : 27 * 3 + k < 1053) :
    colOK (covAt00 3) ⟨27 * 3 + k, hc⟩ = true := rfl
theorem state00_4 (k : ℕ) (_hk : k < 27) (hc : 27 * 4 + k < 1053) :
    colOK (covAt00 4) ⟨27 * 4 + k, hc⟩ = true := rfl
theorem state00_5 (k : ℕ) (_hk : k < 27) (hc : 27 * 5 + k < 1053) :
    colOK (covAt00 5) ⟨27 * 5 + k, hc⟩ = true := rfl
theorem state00_6 (k : ℕ) (_hk : k < 27) (hc : 27 * 6 + k < 1053) :
    colOK (covAt00 6) ⟨27 * 6 + k, hc⟩ = true := rfl
theorem state00_7 (k : ℕ) (_hk : k < 27) (hc : 27 * 7 + k < 1053) :
    colOK (covAt00 7) ⟨27 * 7 + k, hc⟩ = true := rfl
theorem state00_8 (k : ℕ) (_hk : k < 27) (hc : 27 * 8 + k < 1053) :
    colOK (covAt00 8) ⟨27 * 8 + k, hc⟩ = true := rfl
theorem state00_9 (k : ℕ) (_hk : k < 27) (hc : 27 * 9 + k < 1053) :
    colOK (covAt00 9) ⟨27 * 9 + k, hc⟩ = true := rfl
theorem state00_10 (k : ℕ) (_hk : k < 27) (hc : 27 * 10 + k < 1053) :
    colOK (covAt00 10) ⟨27 * 10 + k, hc⟩ = true := rfl
theorem state00_11 (k : ℕ) (_hk : k < 27) (hc : 27 * 11 + k < 1053) :
    colOK (covAt00 11) ⟨27 * 11 + k, hc⟩ = true := rfl
theorem state00_12 (k : ℕ) (hk : k < 27) (hc : 27 * 12 + k < 1053) :
    colOK (covAt00 12) ⟨27 * 12 + k, hc⟩ = true :=
  state_of_chunks _ 12 c00_12_0 c00_12_1 c00_12_2 k hk hc
theorem state00_13 (k : ℕ) (hk : k < 27) (hc : 27 * 13 + k < 1053) :
    colOK (covAt00 13) ⟨27 * 13 + k, hc⟩ = true :=
  state_of_chunks _ 13 c00_13_0 c00_13_1 c00_13_2 k hk hc
theorem state00_14 (k : ℕ) (hk : k < 27) (hc : 27 * 14 + k < 1053) :
    colOK (covAt00 14) ⟨27 * 14 + k, hc⟩ = true :=
  state_of_chunks _ 14 c00_14_0 c00_14_1 c00_14_2 k hk hc
theorem state00_15 (k : ℕ) (hk : k < 27) (hc : 27 * 15 + k < 1053) :
    colOK (covAt00 15) ⟨27 * 15 + k, hc⟩ = true :=
  state_of_chunks _ 15 c00_15_0 c00_15_1 c00_15_2 k hk hc
theorem state00_16 (k : ℕ) (hk : k < 27) (hc : 27 * 16 + k < 1053) :
    colOK (covAt00 16) ⟨27 * 16 + k, hc⟩ = true :=
  state_of_chunks _ 16 c00_16_0 c00_16_1 c00_16_2 k hk hc
theorem state00_17 (k : ℕ) (hk : k < 27) (hc : 27 * 17 + k < 1053) :
    colOK (covAt00 17) ⟨27 * 17 + k, hc⟩ = true :=
  state_of_chunks _ 17 c00_17_0 c00_17_1 c00_17_2 k hk hc
theorem state00_18 (k : ℕ) (hk : k < 27) (hc : 27 * 18 + k < 1053) :
    colOK (covAt00 18) ⟨27 * 18 + k, hc⟩ = true :=
  state_of_chunks _ 18 c00_18_0 c00_18_1 c00_18_2 k hk hc
theorem state00_19 (k : ℕ) (hk : k < 27) (hc : 27 * 19 + k < 1053) :
    colOK (covAt00 19) ⟨27 * 19 + k, hc⟩ = true :=
  state_of_chunks _ 19 c00_19_0 c00_19_1 c00_19_2 k hk hc
theorem state00_20 (k : ℕ) (hk : k < 27) (hc : 27 * 20 + k < 1053) :
    colOK (covAt00 20) ⟨27 * 20 + k, hc⟩ = true :=
  state_of_chunks _ 20 c00_20_0 c00_20_1 c00_20_2 k hk hc
theorem state00_21 (k : ℕ) (hk : k < 27) (hc : 27 * 21 + k < 1053) :
    colOK (covAt00 21) ⟨27 * 21 + k, hc⟩ = true :=
  state_of_chunks _ 21 c00_21_0 c00_21_1 c00_21_2 k hk hc
theorem state00_22 (k : ℕ) (hk : k < 27) (hc : 27 * 22 + k < 1053) :
    colOK (covAt00 22) ⟨27 * 22 + k, hc⟩ = true :=
  state_of_chunks _ 22 c00_22_0 c00_22_1 c00_22_2 k hk hc
theorem state00_23 (k : ℕ) (hk : k < 27) (hc : 27 * 23 + k < 1053) :
    colOK (covAt00 23) ⟨27 * 23 + k, hc⟩ = true :=
  state_of_chunks _ 23 c00_23_0 c00_23_1 c00_23_2 k hk hc
theorem state00_24 (k : ℕ) (hk : k < 27) (hc : 27 * 24 + k < 1053) :
    colOK (covAt00 24) ⟨27 * 24 + k, hc⟩ = true :=
  state_of_chunks _ 24 c00_24_0 c00_24_1 c00_24_2 k hk hc
theorem state00_25 (k : ℕ) (hk : k < 27) (hc : 27 * 25 + k < 1053) :
    colOK (covAt00 25) ⟨27 * 25 + k, hc⟩ = true :=
  state_of_chunks _ 25 c00_25_0 c00_25_1 c00_25_2 k hk hc
theorem state00_26 (k : ℕ) (hk : k < 27) (hc : 27 * 26 + k < 1053) :
    colOK (covAt00 26) ⟨27 * 26 + k, hc⟩ = true :=
  state_of_chunks _ 26 c00_26_0 c00_26_1 c00_26_2 k hk hc
theorem state00_27 (k : ℕ) (hk : k < 27) (hc : 27 * 27 + k < 1053) :
    colOK (covAt00 27) ⟨27 * 27 + k, hc⟩ = true :=
  state_of_chunks _ 27 c00_27_0 c00_27_1 c00_27_2 k hk hc
theorem state00_28 (k : ℕ) (hk : k < 27) (hc : 27 * 28 + k < 1053) :
    colOK (covAt00 28) ⟨27 * 28 + k, hc⟩ = true :=
  state_of_chunks _ 28 c00_28_0 c00_28_1 c00_28_2 k hk hc
theorem state00_29 (k : ℕ) (hk : k < 27) (hc : 27 * 29 + k < 1053) :
    colOK (covAt00 29) ⟨27 * 29 + k, hc⟩ = true :=
  state_of_chunks _ 29 c00_29_0 c00_29_1 c00_29_2 k hk hc
theorem state00_30 (k : ℕ) (hk : k < 27) (hc : 27 * 30 + k < 1053) :
    colOK (covAt00 30) ⟨27 * 30 + k, hc⟩ = true :=
  state_of_chunks _ 30 c00_30_0 c00_30_1 c00_30_2 k hk hc
theorem state00_31 (k : ℕ) (hk : k < 27) (hc : 27 * 31 + k < 1053) :
    colOK (covAt00 31) ⟨27 * 31 + k, hc⟩ = true :=
  state_of_chunks _ 31 c00_31_0 c00_31_1 c00_31_2 k hk hc
theorem state00_32 (k : ℕ) (hk : k < 27) (hc : 27 * 32 + k < 1053) :
    colOK (covAt00 32) ⟨27 * 32 + k, hc⟩ = true :=
  state_of_chunks _ 32 c00_32_0 c00_32_1 c00_32_2 k hk hc
theorem state00_33 (k : ℕ) (hk : k < 27) (hc : 27 * 33 + k < 1053) :
    colOK (covAt00 33) ⟨27 * 33 + k, hc⟩ = true :=
  state_of_chunks _ 33 c00_33_0 c00_33_1 c00_33_2 k hk hc
theorem state00_34 (k : ℕ) (hk : k < 27) (hc : 27 * 34 + k < 1053) :
    colOK (covAt00 34) ⟨27 * 34 + k, hc⟩ = true :=
  state_of_chunks _ 34 c00_34_0 c00_34_1 c00_34_2 k hk hc
theorem state00_35 (k : ℕ) (hk : k < 27) (hc : 27 * 35 + k < 1053) :
    colOK (covAt00 35) ⟨27 * 35 + k, hc⟩ = true :=
  state_of_chunks _ 35 c00_35_0 c00_35_1 c00_35_2 k hk hc
theorem state00_36 (k : ℕ) (hk : k < 27) (hc : 27 * 36 + k < 1053) :
    colOK (covAt00 36) ⟨27 * 36 + k, hc⟩ = true :=
  state_of_chunks _ 36 c00_36_0 c00_36_1 c00_36_2 k hk hc
theorem state00_37 (k : ℕ) (hk : k < 27) (hc : 27 * 37 + k < 1053) :
    colOK (covAt00 37) ⟨27 * 37 + k, hc⟩ = true :=
  state_of_chunks _ 37 c00_37_0 c00_37_1 c00_37_2 k hk hc
theorem state00_38 (k : ℕ) (hk : k < 27) (hc : 27 * 38 + k < 1053) :
    colOK (covAt00 38) ⟨27 * 38 + k, hc⟩ = true :=
  state_of_chunks _ 38 c00_38_0 c00_38_1 c00_38_2 k hk hc

theorem t00_colOK (c : Fin 1053) : colOK (covAt00 (c.val / 27)) c = true := by
  obtain ⟨n, hn⟩ := c
  have key : ∀ p, p < 39 → ∀ k (hk : k < 27) (hc : 27 * p + k < 1053),
      colOK (covAt00 p) ⟨27 * p + k, hc⟩ = true := by
    intro p hp
    match p, hp with
    | 0, _ => exact state00_0
    | 1, _ => exact state00_1
    | 2, _ => exact state00_2
    | 3, _ => exact state00_3
    | 4, _ => exact state00_4
    | 5, _ => exact state00_5
    | 6, _ => exact state00_6
    | 7, _ => exact state00_7
    | 8, _ => exact state00_8
    | 9, _ => exact state00_9
    | 10, _ => exact state00_10
    | 11, _ => exact state00_11
    | 12, _ => exact state00_12
    | 13, _ => exact state00_13
    | 14, _ => exact state00_14
    | 15, _ => exact state00_15
    | 16, _ => exact state00_16
    | 17, _ => exact state00_17
    | 18, _ => exact state00_18
    | 19, _ => exact state00_19
    | 20, _ => exact state00_20
    | 21, _ => exact state00_21
    | 22, _ => exact state00_22
    | 23, _ => exact state00_23
    | 24, _ => exact state00_24
    | 25, _ => exact state00_25
    | 26, _ => exact state00_26
    | 27, _ => exact state00_27
    | 28, _ => exact state00_28
    | 29, _ => exact state00_29
    | 30, _ => exact state00_30
    | 31, _ => exact state00_31
    | 32, _ => exact state00_32
    | 33, _ => exact state00_33
    | 34, _ => exact state00_34
    | 35, _ => exact state00_35
    | 36, _ => exact state00_36
    | 37, _ => exact state00_37
    | 38, _ => exact state00_38
    | p + 39, h => exact absurd h (by omega)
  have e : 27 * (n / 27) + n % 27 = n := by omega
  have := key (n / 27) (by omega) (n % 27) (by omega) (by omega)
  simpa only [e] using this

/-- **L2 (T00), every phase.** -/
theorem t00_phased_equilibrium {R : Type*} [CommRing R] (ι : Q12 →+* R) (U : Fin 4 → Rˣ) (t : R)
    (c : Fin 1053) :
    (covT00.map fun pe => ι pe.e.coefficient.toQ12 * mono U pe.x *
        jacobianEntry (ι half) t (fNumber pe.e.label) (PhiR ι U) c).sum = 0 := by
  rw [sum_filter_touches, covAt00_spec]
  simp only [jacobianEntry, rowShape, Equiv.symm_apply_apply]
  exact colOK_sum ι U _ c (t00_colOK c)

end Option2.NativeStress.HTPhaseKron
#print axioms Option2.NativeStress.HTPhaseKron.t00_phased_equilibrium

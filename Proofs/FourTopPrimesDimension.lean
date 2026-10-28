module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Order.KrullDimension
public import MinimalPrimeExhaustion

@[expose] public section

/-!
# Four top-dimensional minimal primes and their localized ideals (part C)

Dimension-hypothesis form of the contract `FOUR-TOP-PRIMES-LOCALIZATION-CONTRACT.md`.
The general theorem is stated for any finite index type; the contract-named theorem
specialises to `Fin 4`, dimension `62`, drop `61`, with the contract's `[IsNoetherianRing R]`
(unused by the proof).
-/

namespace FourTopPrimes

open MinimalPrimeExhaustion

/-- (C1) If `dim R/K < dim R/p` then `K ⊄ p`. -/
theorem not_le_of_ringKrullDim_lt {R : Type*} [CommRing R] {K p : Ideal R}
    (h : ringKrullDim (R ⧸ K) < ringKrullDim (R ⧸ p)) : ¬ K ≤ p := by
  intro hle
  exact absurd (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle)) (not_le.mpr h)

/-- (C2) Quotient dimension equals coheight in `PrimeSpectrum R`. -/
theorem ringKrullDim_quotient_eq_coheight {R : Type*} [CommRing R] (P : PrimeSpectrum R) :
    ringKrullDim (R ⧸ P.asIdeal) = (Order.coheight P : WithBot ℕ∞) := by
  have hZ : PrimeSpectrum.zeroLocus (R := R) (P.asIdeal : Set R) = Set.Ici P := by
    ext q
    simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici, SetLike.coe_subset_coe,
      PrimeSpectrum.asIdeal_le_asIdeal]
  rw [Order.coheight_eq_krullDim_Ici, ringKrullDim,
    Order.krullDim_eq_of_orderIso (Ideal.primeSpectrumQuotientOrderIsoZeroLocus P.asIdeal),
    Order.krullDim_eq_of_orderIso (Set.orderIsoOfEq _ _ hZ)]

/-- (C3) Distinct primes of the same finite coheight are incomparable. -/
theorem not_le_of_coheight_eq {α : Type*} [PartialOrder α] {x y : α} (hxy : x ≠ y)
    (hc : Order.coheight x = Order.coheight y) (hfin : Order.coheight y < ⊤) : ¬ x ≤ y := by
  intro hle
  have hlt : x < y := lt_of_le_of_ne hle hxy
  exact absurd (Order.coheight_strictAnti hlt hfin) (by rw [hc]; exact lt_irrefl _)

def sheetIntersection {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (P : ι → PrimeSpectrum R) : Ideal R :=
  Finset.univ.inf (fun i => (P i).asIdeal)

def residualColon {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (I : Ideal R) (P : ι → PrimeSpectrum R) : Ideal R :=
  I.colon (sheetIntersection P : Set R)

/-- General form: finite family, common finite quotient dimension `d`, colon drop `< d`. -/
theorem top_minimalPrimes_and_localized_ideal_eq_general {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] (I : Ideal R) (P : ι → PrimeSpectrum R) (d : ℕ)
    (hDistinct : Function.Injective P)
    (hContain : I ≤ sheetIntersection P)
    (hDim : ∀ i, ringKrullDim (R ⧸ (P i).asIdeal) = (d : WithBot ℕ∞))
    (hDrop : ringKrullDim (R ⧸ residualColon I P) < (d : WithBot ℕ∞)) :
    ({p : Ideal R | I.IsMinimalPrime p ∧ ringKrullDim (R ⧸ p) = (d : WithBot ℕ∞)} =
      Set.range (fun i => (P i).asIdeal)) ∧
    ∀ i, Ideal.map (algebraMap R (Localization.AtPrime (P i).asIdeal)) I =
      Ideal.map (algebraMap R (Localization.AtPrime (P i).asIdeal)) (P i).asIdeal := by
  classical
  set K := residualColon I P with hKdef
  have hKJ : K * Finset.univ.inf (fun i => (P i).asIdeal) ≤ I :=
    colon_mul_le I (Finset.univ.inf (fun i => (P i).asIdeal))
  -- (C1) `K ⊄ p` for every ideal `p` of quotient dimension `d`
  have hC1 : ∀ p : Ideal R, ringKrullDim (R ⧸ p) = (d : WithBot ℕ∞) → ¬ K ≤ p := by
    intro p hp
    exact not_le_of_ringKrullDim_lt (by rw [hp]; exact hDrop)
  -- coheights
  have hcoh : ∀ i, Order.coheight (P i) = (d : ℕ∞) := by
    intro i
    have h := hDim i
    rw [ringKrullDim_quotient_eq_coheight] at h
    exact_mod_cast h
  -- (C3) incomparability
  have hInc : ∀ i j, j ≠ i → ¬ (P j).asIdeal ≤ (P i).asIdeal := by
    intro i j hji hle
    refine not_le_of_coheight_eq (fun h => hji (hDistinct h)) (by rw [hcoh, hcoh])
      (by rw [hcoh]; exact WithTop.coe_lt_top d) ?_
    exact hle
  -- (C4) each `P i` is minimal over `I`
  have hMin : ∀ i, I.IsMinimalPrime (P i).asIdeal := by
    intro i
    refine ⟨⟨(P i).isPrime, hContain.trans (Finset.inf_le (Finset.mem_univ i))⟩, ?_⟩
    intro q hq hqle
    have hKq : ¬ K ≤ q := fun hKq => hC1 _ (hDim i) (hKq.trans hqle)
    obtain ⟨j, -, hjq⟩ := exists_le_of_isPrime_of_not_le Finset.univ (fun j => (P j).asIdeal)
      I K hKJ hq.1 hq.2 hKq
    by_cases hji : j = i
    · rw [hji] at hjq; exact hjq
    · exact absurd (hjq.trans hqle) (hInc i j hji)
  refine ⟨?_, ?_⟩
  · ext p
    constructor
    · rintro ⟨hp, hpd⟩
      obtain ⟨i, -, rfl⟩ := eq_of_isMinimalPrime_of_not_le Finset.univ (fun j => (P j).asIdeal)
        (fun j _ => (P j).isPrime) I K hContain hKJ hp (hC1 p hpd)
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨hMin i, hDim i⟩
  · intro i
    exact map_localization_eq_primeSpectrum Finset.univ P I K hContain hKJ i
      (Finset.mem_univ i) (hC1 _ (hDim i)) (fun j _ hji => hInc i j hji)

/-- The contract's exact boundary (`Fin 4`, dimension 62, drop ≤ 61). -/
theorem top_minimalPrimes_and_localized_ideal_eq {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (P : Fin 4 → PrimeSpectrum R)
    (hDistinct : Function.Injective P)
    (hContain : I ≤ sheetIntersection P)
    (hDim : ∀ i, ringKrullDim (R ⧸ (P i).asIdeal) = (62 : WithBot ℕ∞))
    (hDrop : ringKrullDim (R ⧸ residualColon I P) ≤ (61 : WithBot ℕ∞)) :
    ({p : Ideal R | I.IsMinimalPrime p ∧
        ringKrullDim (R ⧸ p) = (62 : WithBot ℕ∞)} =
      Set.range (fun i => (P i).asIdeal)) ∧
    ∀ i, Ideal.map (algebraMap R (Localization.AtPrime (P i).asIdeal)) I =
      Ideal.map (algebraMap R (Localization.AtPrime (P i).asIdeal)) (P i).asIdeal := by
  have h6162 : (61 : WithBot ℕ∞) < ((62 : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast (show (61 : ℕ) < 62 by norm_num)
  have hDim' : ∀ i, ringKrullDim (R ⧸ (P i).asIdeal) = ((62 : ℕ) : WithBot ℕ∞) := by
    intro i; rw [hDim i]; rfl
  have h := top_minimalPrimes_and_localized_ideal_eq_general I P 62 hDistinct hContain hDim'
    (hDrop.trans_lt h6162)
  exact h

end FourTopPrimes

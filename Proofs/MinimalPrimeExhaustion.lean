module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import IdealExtensionComparison

@[expose] public section

/-!
# Minimal-prime exhaustion and localized equality for a finite family of primes

Part A: if `I ≤ J := ⋂_{i ∈ F} P i` with every `P i` prime and `K * J ≤ I`, then every
minimal prime `p` of `I` with `K ⊄ p` equals some `P i`.

Part B: under the same hypotheses, if `K ⊄ P i` and no other `P j` (`j ∈ F`, `j ≠ i`) is
contained in `P i`, then the extensions of `I` and of `P i` to `R_(P i)` are equal.

No dimension, radical, or reducedness hypothesis appears here.
-/

namespace MinimalPrimeExhaustion

/-- Containment helper (arbitrary prime, containment only — not an equality claim):
a prime `p ⊇ I` with `K ⊄ p` contains some `P i`. -/
theorem exists_le_of_isPrime_of_not_le {R : Type*} [CommRing R] {ι : Type*} (F : Finset ι)
    (P : ι → Ideal R) (I K : Ideal R) (hKJ : K * F.inf P ≤ I)
    {p : Ideal R} (hp : p.IsPrime) (hIp : I ≤ p) (hKp : ¬ K ≤ p) :
    ∃ i ∈ F, P i ≤ p := by
  rcases (hp.mul_le).mp (hKJ.trans hIp) with h | h
  · exact absurd h hKp
  · exact (hp.inf_le').mp h

/-- Part A. A minimal prime of `I` not containing `K` is one of the `P i`. -/
theorem eq_of_isMinimalPrime_of_not_le {R : Type*} [CommRing R] {ι : Type*} (F : Finset ι)
    (P : ι → Ideal R) (hP : ∀ i ∈ F, (P i).IsPrime) (I K : Ideal R)
    (hIJ : I ≤ F.inf P) (hKJ : K * F.inf P ≤ I)
    {p : Ideal R} (hp : I.IsMinimalPrime p) (hKp : ¬ K ≤ p) :
    ∃ i ∈ F, p = P i := by
  obtain ⟨i, hi, hle⟩ := exists_le_of_isPrime_of_not_le F P I K hKJ hp.isPrime hp.le hKp
  exact ⟨i, hi, (Minimal.eq_of_le hp ⟨hP i hi, hIJ.trans (Finset.inf_le hi)⟩ hle).symm⟩

/-- The correctly oriented colon `(I : J) = {r | r • J ⊆ I}` satisfies `(I : J) * J ≤ I`. -/
theorem colon_mul_le {R : Type*} [CommRing R] (I J : Ideal R) :
    I.colon (J : Set R) * J ≤ I := by
  rw [Ideal.mul_le]
  intro r hr s hs
  exact (Submodule.mem_colon.mp hr) s hs

/-- Part A, colon form: `K := (I : J)` with `J = ⋂_{i ∈ F} P i`. -/
theorem eq_of_isMinimalPrime_of_not_colon_le {R : Type*} [CommRing R] {ι : Type*}
    (F : Finset ι) (P : ι → Ideal R) (hP : ∀ i ∈ F, (P i).IsPrime) (I : Ideal R)
    (hIJ : I ≤ F.inf P) {p : Ideal R} (hp : I.IsMinimalPrime p)
    (hKp : ¬ I.colon ((F.inf P : Ideal R) : Set R) ≤ p) :
    ∃ i ∈ F, p = P i :=
  eq_of_isMinimalPrime_of_not_le F P hP I _ hIJ (colon_mul_le I (F.inf P)) hp hKp

/-- Localization commutes with finite intersections of ideals. -/
theorem map_finset_inf {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] {ι : Type*} (F : Finset ι) (P : ι → Ideal R) :
    Ideal.map (algebraMap R S) (F.inf P) = F.inf (fun j => Ideal.map (algebraMap R S) (P j)) := by
  classical
  refine Finset.induction_on F ?_ ?_
  · exact Ideal.map_top _
  · intro a s _ ih
    rw [Finset.inf_insert, Finset.inf_insert, IsLocalization.map_inf M S, ih]

/-- Part B. Localized equality `I_(P i) = (P i)_(P i)` of the actual extended ideals. -/
theorem map_localization_eq {R : Type*} [CommRing R] {ι : Type*} (F : Finset ι)
    (P : ι → Ideal R) (hP : ∀ i ∈ F, (P i).IsPrime) (I K : Ideal R)
    (hIJ : I ≤ F.inf P) (hKJ : K * F.inf P ≤ I)
    (i : ι) (hi : i ∈ F) (hKi : ¬ K ≤ P i)
    (hInc : ∀ j ∈ F, j ≠ i → ¬ P j ≤ P i) :
    haveI := hP i hi
    Ideal.map (algebraMap R (Localization.AtPrime (P i))) I =
      Ideal.map (algebraMap R (Localization.AtPrime (P i))) (P i) := by
  have := hP i hi
  set S := Localization.AtPrime (P i)
  set f := algebraMap R S
  obtain ⟨s, hsK, hsP⟩ := IsConcreteLE.not_le_iff_exists.mp hKi
  have hs_unit : IsUnit (f s) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff S (P i) s).mpr (Ideal.mem_primeCompl_iff.mpr hsP)
  have step1 : Ideal.map f I = Ideal.map f (F.inf P) :=
    IdealExtensionComparison.map_eq_of_unit_multiplier f I (F.inf P) hIJ s hs_unit
      (fun x hx => Ideal.mul_le.mp hKJ s hsK x hx)
  have htop : ∀ j ∈ F, j ≠ i → Ideal.map f (P j) = ⊤ := by
    intro j hj hji
    obtain ⟨y, hyj, hyi⟩ := IsConcreteLE.not_le_iff_exists.mp (hInc j hj hji)
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem f hyj)
      ((IsLocalization.AtPrime.isUnit_to_map_iff S (P i) y).mpr (Ideal.mem_primeCompl_iff.mpr hyi))
  rw [step1, map_finset_inf (P i).primeCompl F P]
  apply le_antisymm (Finset.inf_le (f := fun j => Ideal.map f (P j)) hi)
  refine Finset.le_inf fun j hj => ?_
  by_cases hji : j = i
  · rw [hji]
  · rw [htop j hj hji]
    exact le_top

/-- Part B, `PrimeSpectrum` form (primality instances come from `PrimeSpectrum`). -/
theorem map_localization_eq_primeSpectrum {R : Type*} [CommRing R] {ι : Type*} (F : Finset ι)
    (P : ι → PrimeSpectrum R) (I K : Ideal R)
    (hIJ : I ≤ F.inf (fun j => (P j).asIdeal)) (hKJ : K * F.inf (fun j => (P j).asIdeal) ≤ I)
    (i : ι) (hi : i ∈ F) (hKi : ¬ K ≤ (P i).asIdeal)
    (hInc : ∀ j ∈ F, j ≠ i → ¬ (P j).asIdeal ≤ (P i).asIdeal) :
    Ideal.map (algebraMap R (Localization.AtPrime (P i).asIdeal)) I =
      Ideal.map (algebraMap R (Localization.AtPrime (P i).asIdeal)) (P i).asIdeal :=
  map_localization_eq F (fun j => (P j).asIdeal) (fun j _ => (P j).isPrime) I K hIJ hKJ i hi hKi
    hInc

end MinimalPrimeExhaustion

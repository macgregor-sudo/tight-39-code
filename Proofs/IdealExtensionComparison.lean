module

public import Mathlib.RingTheory.Ideal.Maps

@[expose] public section

namespace IdealExtensionComparison

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Inverting a multiplier that sends `J` into `I` makes the two ideals equal.

This is the standard localization argument, stated for any ring homomorphism
that makes the multiplier a unit. It is independent of analytic germs and
does not supply the multiplier or prove the hypotheses for a certificate.
-/
theorem map_eq_of_unit_multiplier (f : R →+* S) (I J : Ideal R)
    (hIJ : I ≤ J) (k : R) (hk : IsUnit (f k))
    (hmul : ∀ x ∈ J, k * x ∈ I) :
    Ideal.map f I = Ideal.map f J := by
  apply le_antisymm (Ideal.map_mono hIJ)
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change f x ∈ Ideal.map f I
  have hprod : f k * f x ∈ Ideal.map f I := by
    rw [← map_mul]
    exact Ideal.mem_map_of_mem f (hmul x hx)
  obtain ⟨u, hu⟩ := hk
  rw [← hu] at hprod
  have hcancel := (Ideal.map f I).mul_mem_left (↑(u⁻¹) : S) hprod
  simpa [← mul_assoc] using hcancel

end IdealExtensionComparison

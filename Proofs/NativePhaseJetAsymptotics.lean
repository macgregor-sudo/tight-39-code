module

public import NativePhaseHilbertSamuelBounds
public import Mathlib.Analysis.SpecialFunctions.Choose

@[expose] public section

/-! Asymptotic growth of the actual intrinsic jet lengths. Mathlib's generic
binomial asymptotic and finite-shift limit theorem give the squeeze; no
62-factor coefficient expansion or new asymptotic invariant is introduced.
Ordinary multiplicity requires its separate Hilbert--Samuel identification. -/

noncomputable section
namespace Option2.NativeStress.PhaseJetAsymptoticsA6
open Filter Asymptotics
open PhasePivotLocusA6 PhaseHilbertSamuelBoundsA6
open CKM.NativeFourFamily
open scoped Topology

private theorem shifted_nat_ratio (a b : ℕ) :
    Tendsto (fun n : ℕ => ((n+a : ℕ) : ℝ) / ((n+b : ℕ) : ℝ)) atTop (𝓝 1) := by
  simpa only [one_mul, div_one, Nat.cast_add, add_comm] using
    (tendsto_add_mul_div_add_mul_atTop_nhds (a : ℝ) (b : ℝ) (1 : ℝ)
      (d := (1 : ℝ)) one_ne_zero)

private theorem shifted_choose_ratio (k a b : ℕ) :
    Tendsto (fun n : ℕ => ((n+a).choose k : ℝ) / (((n+b : ℕ) : ℝ) ^ k))
      atTop (𝓝 (1 / (k.factorial : ℝ))) := by
  have heq : (fun n : ℕ => ((n+a).choose k : ℝ) / (((n+b : ℕ) : ℝ) ^ k)) ~[atTop]
      (fun n : ℕ => ((((n+a : ℕ) : ℝ) ^ k) / (k.factorial : ℝ)) /
        (((n+b : ℕ) : ℝ) ^ k)) := by
    exact ((isEquivalent_choose k).comp_tendsto (tendsto_add_atTop_nat a)).div IsEquivalent.refl
  apply heq.tendsto_nhds_iff.mpr
  convert ((shifted_nat_ratio a b).pow k).div_const (k.factorial : ℝ) using 1
  · funext n
    simp only [div_pow, div_eq_mul_inv]
    ring
  · simp only [one_pow]

private theorem shifted_choose_ratio_succ (k a b : ℕ) :
    Tendsto (fun n : ℕ => ((n+a).choose k : ℝ) / (((n+b : ℕ) : ℝ) ^ (k+1)))
      atTop (𝓝 0) := by
  have hz := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ) |>.comp (tendsto_add_atTop_nat b)
  have h := (shifted_choose_ratio k a b).mul hz
  convert h using 1
  · funext n
    simp only [Function.comp_apply, Nat.cast_add, pow_succ, div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  · simp only [mul_zero]

private theorem length_ratio_of_shifted_choose_bounds (L : ℕ → ℕ) (a b d c : ℕ)
    (hupper : ∀ N, L N ≤ a * (N+(d+1)).choose (d+1) + b * (N+d).choose d)
    (hlower : ∀ N, a * (N+(d+1)).choose (d+1) ≤ L (N+c)) :
    Tendsto (fun N : ℕ => (L N : ℝ) / ((N : ℝ) ^ (d+1)))
      atTop (𝓝 ((a : ℝ) / ((d+1).factorial : ℝ))) := by
  apply (tendsto_add_atTop_iff_nat c).mp
  have hlow : Tendsto
      (fun N : ℕ => (a : ℝ) * ((N+(d+1)).choose (d+1) : ℝ) /
        (((N+c : ℕ) : ℝ) ^ (d+1)))
      atTop (𝓝 ((a : ℝ) / ((d+1).factorial : ℝ))) := by
    simpa only [mul_div_assoc, mul_one_div] using
      (shifted_choose_ratio (d+1) (d+1) c).const_mul (a : ℝ)
  have hupp : Tendsto
      (fun N : ℕ => (a : ℝ) * ((N+(c+(d+1))).choose (d+1) : ℝ) /
          (((N+c : ℕ) : ℝ) ^ (d+1)) +
        (b : ℝ) * ((N+(c+d)).choose d : ℝ) / (((N+c : ℕ) : ℝ) ^ (d+1)))
      atTop (𝓝 ((a : ℝ) / ((d+1).factorial : ℝ))) := by
    simpa only [mul_div_assoc, mul_one_div, mul_zero, add_zero] using
      ((shifted_choose_ratio (d+1) (c+(d+1)) c).const_mul (a : ℝ)).add
        ((shifted_choose_ratio_succ d (c+d) c).const_mul (b : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp
  · intro N
    have h : (a : ℝ) * ((N+(d+1)).choose (d+1) : ℝ) ≤ (L (N+c) : ℝ) := by
      exact_mod_cast hlower N
    exact div_le_div_of_nonneg_right h (pow_nonneg (Nat.cast_nonneg _) _)
  · intro N
    have h : (L (N+c) : ℝ) ≤
        (a : ℝ) * ((N+c+(d+1)).choose (d+1) : ℝ) +
        (b : ℝ) * ((N+c+d).choose d : ℝ) := by
      exact_mod_cast hupper (N+c)
    have hd := div_le_div_of_nonneg_right h
      (pow_nonneg (Nat.cast_nonneg (N+c) : (0 : ℝ) ≤ ((N+c : ℕ) : ℝ)) (d+1))
    simpa only [Nat.add_assoc, add_div] using hd

/-- The actual natural length, normalized by 62!/N^62, tends to four.
Conversion from extended naturals uses the already proved finite lengths.
The fixed shift in the lower bound may depend on u, never on N. -/
theorem native_phase_normalized_intrinsic_jet_tendsto (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) :
    Tendsto (fun N : ℕ => (Nat.factorial 62 : ℝ) *
      ((nativePhaseIntrinsicJetLength u N).toNat : ℝ) / ((N : ℝ) ^ 62))
      atTop (𝓝 4) := by
  let L : ℕ → ℕ := fun N => (nativePhaseIntrinsicJetLength u N).toNat
  have hfinite (N : ℕ) : nativePhaseIntrinsicJetLength u N ≠ ⊤ :=
    ne_of_lt (native_phase_intrinsic_jet_length_lt_top u hgood hpivot N)
  have hupper (N : ℕ) : L N ≤ 4 * (N+62).choose 62 + 1540 * (N+61).choose 61 := by
    have h := native_phase_intrinsic_jet_upper_bound u hgood hpivot N
    rw [← ENat.natCast_toNat (hfinite N)] at h
    exact ENat.natCast_le_natCast.mp h
  obtain ⟨c,hc⟩ := native_phase_intrinsic_jet_shifted_lower_bound u hgood
  have hlower (N : ℕ) : 4 * (N+62).choose 62 ≤ L (N+c) := by
    have h := hc N
    rw [← ENat.natCast_toNat (hfinite (N+c))] at h
    exact ENat.natCast_le_natCast.mp h
  have hbase : Tendsto (fun N : ℕ => (L N : ℝ) / ((N : ℝ) ^ 62))
      atTop (𝓝 ((4 : ℝ) / (Nat.factorial 62 : ℝ))) :=
    length_ratio_of_shifted_choose_bounds L 4 1540 61 c hupper hlower
  have hfac : (Nat.factorial 62 : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero 62
  convert hbase.const_mul (Nat.factorial 62 : ℝ) using 1
  · funext N
    change (Nat.factorial 62 : ℝ) * (L N : ℝ) / (N : ℝ)^62 = _
    ring
  · field_simp

#print axioms Option2.NativeStress.PhaseJetAsymptoticsA6.native_phase_normalized_intrinsic_jet_tendsto
end Option2.NativeStress.PhaseJetAsymptoticsA6

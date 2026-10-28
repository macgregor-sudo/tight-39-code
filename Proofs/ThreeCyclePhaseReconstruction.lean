module

public import UEBResidualDefinitions
public import FourierTransport
import all UEBResidualDefinitions
import all FourierTransport

/-!
# Phase-specific reconstruction of the three-cycle Fourier recurrence

This continuation uses the original Challenge's PhaseTriple and the existing
FourierTransport recurrence. It proves the cycle obstruction and reconstructs
every scalar solution from its b=0 row. It does not identify these scalar
equations with the complete original matrix tangent space or count its dimension.

Mathematical source: MASTER.md §6.4, following equations (6.6)–(6.7).
New proof code; no third-party implementation is copied. Imports retain the
mathlib pin and attribution recorded in the two imported first-party modules.
No first-party release license is assigned by this isolated prototype.
-/

@[expose] public section
noncomputable section

namespace UnitaryErrorBases.ThreeCycleFourier

private lemma cycleIndexCases (i : Index) : i = 0 ∨ i = 1 ∨ i = 2 := by
  exact (by decide : ∀ j : Index, j = 0 ∨ j = 1 ∨ j = 2) i

@[simp] private lemma cycle_one_add_one : (1 : Index) + 1 = 2 := by decide
@[simp] private lemma cycle_one_add_two : (1 : Index) + 2 = 0 := by decide
@[simp] private lemma cycle_two_add_one : (2 : Index) + 1 = 0 := by decide
@[simp] private lemma cycle_two_add_two : (2 : Index) + 2 = 1 := by decide
@[simp] private lemma cycle_zero_ne_two : (0 : Index) ≠ 2 := by decide
@[simp] private lemma cycle_one_ne_two : (1 : Index) ≠ 2 := by decide
@[simp] private lemma cycle_two_ne_zero : (2 : Index) ≠ 0 := by decide
@[simp] private lemma cycle_two_ne_one : (2 : Index) ≠ 1 := by decide

private lemma shift_three (k mu : Index) :
    k + mu + 1 + mu + 1 + mu + 1 = k := by
  exact (by decide : ∀ k mu : Index,
    k + mu + 1 + mu + 1 + mu + 1 = k) k mu

lemma phaseTriple_ne_zero (d : PhaseTriple) (k : Index) : d.val k ≠ 0 := by
  intro hk
  have h := d.property.1 k
  simp [hk] at h

private lemma phaseTriple_star (d : PhaseTriple) (k : Index) :
    star (d.val k) = (d.val k)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  calc
    star (d.val k) * d.val k = (Complex.normSq (d.val k) : ℂ) := by
      exact Complex.normSq_eq_conj_mul_self.symm
    _ = 1 := by rw [d.property.1 k]; rfl

lemma phaseTriple_cyclic_product (d : PhaseTriple) (k : Index) :
    d.val k * d.val (k + 1) * d.val (k + 2) = 1 := by
  have hp : d.val 0 * d.val 1 * d.val 2 = 1 := by
    calc
      _ = ∏ j : Index, d.val j := (Fin.prod_univ_three (fun j : Index => d.val j)).symm
      _ = 1 := d.property.2
  rcases cycleIndexCases k with rfl | rfl | rfl
  · simpa using hp
  · simp only [cycle_one_add_one, cycle_one_add_two]
    calc
      d.val 1 * d.val 2 * d.val 0 = d.val 0 * d.val 1 * d.val 2 := by ring
      _ = 1 := hp
  · simp only [cycle_two_add_one, cycle_two_add_two]
    calc
      d.val 2 * d.val 0 * d.val 1 = d.val 0 * d.val 1 * d.val 2 := by ring
      _ = 1 := hp

@[simp] lemma phase_transport_zero (d : PhaseTriple) (k mu : Index) :
    transportFactor (phaseWeight d.val) 0 k mu = 1 := by
  simp [transportFactor, phaseWeight, phaseEntry]

@[simp] lemma phase_transport_one (d : PhaseTriple) (k mu : Index) :
    transportFactor (phaseWeight d.val) 1 k mu =
      d.val (k + mu + 1) / d.val k := by
  have h : k + mu + 2 - 1 = k + mu + 1 := by ring
  simp [transportFactor, phaseWeight, phaseEntry, h]

@[simp] lemma phase_transport_two (d : PhaseTriple) (k mu : Index) :
    transportFactor (phaseWeight d.val) 2 k mu =
      d.val (k + 1) / d.val (k + mu + 2) := by
  simp [transportFactor, phaseWeight, phaseEntry, phaseTriple_star, div_eq_mul_inv,
    mul_comm]

/-- The multiplier after the b=2 step closes the three-step cycle. -/
def cycleMultiplier (d : PhaseTriple) (k mu : Index) : ℂ :=
  transportFactor (phaseWeight d.val) 2 k mu *
    (d.val (k + mu + 1 + mu + 1) / d.val (k + mu + 1))

lemma cycleMultiplier_eq (d : PhaseTriple) (k mu : Index) :
    cycleMultiplier d k mu = if mu = 1 then d.val (k + 1) ^ 3 else 1 := by
  have hn := phaseTriple_ne_zero d
  rcases cycleIndexCases mu with rfl | rfl | rfl
  · have h : k + 1 + 1 = k + 2 := by ring
    simp [cycleMultiplier, h, hn, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  · have h₁ : k + 1 + 1 + 1 + 1 = k + 1 := by
      exact (by decide : ∀ k : Index, k + 1 + 1 + 1 + 1 = k + 1) k
    have h₂ : k + 1 + 2 = k := by
      exact (by decide : ∀ k : Index, k + 1 + 2 = k) k
    have h₃ : k + 1 + 1 = k + 2 := by ring
    have hp : d.val k * d.val (k + 2) = (d.val (k + 1))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      calc
        (d.val k * d.val (k + 2)) * d.val (k + 1) =
            d.val k * d.val (k + 1) * d.val (k + 2) := by ring
        _ = 1 := phaseTriple_cyclic_product d k
    rw [cycleMultiplier, phase_transport_two, h₁, h₂, h₃]
    simp only [ite_true]
    calc
      d.val (k + 1) / d.val k * (d.val (k + 1) / d.val (k + 2)) =
          d.val (k + 1) ^ 2 / (d.val k * d.val (k + 2)) := by rw [div_mul_div_comm, pow_two]
      _ = d.val (k + 1) ^ 3 := by rw [hp]; simp [div_eq_mul_inv]; ring
  · have h₂ : k + 2 + 2 = k + 1 := by
      exact (by decide : ∀ k : Index, k + 2 + 2 = k + 1) k
    have h₃ : k + 2 + 1 = k := by
      exact (by decide : ∀ k : Index, k + 2 + 1 = k) k
    simp [cycleMultiplier, h₂, h₃, hn]

/-- Only the middle Fourier mode has a resonance obstruction. Its phase index
is k+1, so the coordinate belonging to a resonant j is a (j-1) 1. -/
def ResonanceSupported (d : PhaseTriple) (a : Index → Index → ℂ) : Prop :=
  ∀ k, (d.val (k + 1) ^ 3 - 1) * a k 1 = 0

theorem resonanceSupported_iff (d : PhaseTriple) (a : Index → Index → ℂ) :
    ResonanceSupported d a ↔
      ∀ k, d.val (k + 1) ^ 3 ≠ 1 → a k 1 = 0 := by
  constructor
  · intro h k hk
    exact (mul_eq_zero.mp (h k)).resolve_left (sub_ne_zero.mpr hk)
  · intro h k
    by_cases hk : d.val (k + 1) ^ 3 = 1
    · simp [hk]
    · simp [h k hk]

/-- The explicit first two recurrence steps, with no restriction on base data. -/
def reconstruct (d : PhaseTriple) (a : Index → Index → ℂ) : Coordinates :=
  fun b k mu =>
    if b = 0 then a k mu
    else if b = 1 then a (k + mu + 1) mu
    else d.val (k + mu + 1) / d.val k * a (k + mu + 1 + mu + 1) mu

@[simp] lemma reconstruct_zero (d : PhaseTriple) (a : Index → Index → ℂ)
    (k mu : Index) : reconstruct d a 0 k mu = a k mu := by
  simp [reconstruct]

@[simp] lemma reconstruct_one (d : PhaseTriple) (a : Index → Index → ℂ)
    (k mu : Index) : reconstruct d a 1 k mu = a (k + mu + 1) mu := by
  simp [reconstruct]

@[simp] lemma reconstruct_two (d : PhaseTriple) (a : Index → Index → ℂ)
    (k mu : Index) : reconstruct d a 2 k mu =
      d.val (k + mu + 1) / d.val k * a (k + mu + 1 + mu + 1) mu := by
  simp [reconstruct]

/-- No additional choices remain once the b=0 row is specified. -/
theorem eq_reconstruct_of_recurrence (d : PhaseTriple) (z : Coordinates)
    (hz : SatisfiesRecurrence (phaseWeight d.val) z) :
    z = reconstruct d (z 0) := by
  have h₁ (k mu : Index) : z 1 k mu = z 0 (k + mu + 1) mu := by
    simpa using hz 0 k mu
  have h₂ (k mu : Index) : z 2 k mu =
      d.val (k + mu + 1) / d.val k * z 0 (k + mu + 1 + mu + 1) mu := by
    simpa only [cycle_one_add_one, phase_transport_one, h₁] using hz 1 k mu
  funext b k mu
  rcases cycleIndexCases b with rfl | rfl | rfl
  · exact (reconstruct_zero d (z 0) k mu).symm
  · exact (h₁ k mu).trans (reconstruct_one d (z 0) k mu).symm
  · exact (h₂ k mu).trans (reconstruct_two d (z 0) k mu).symm

/-- The final recurrence step is equivalent to the computed resonance support;
the first two steps already hold for arbitrary base data. -/
theorem reconstruct_satisfies_iff (d : PhaseTriple) (a : Index → Index → ℂ) :
    SatisfiesRecurrence (phaseWeight d.val) (reconstruct d a) ↔
      ResonanceSupported d a := by
  have closure (k mu : Index) :
      transportFactor (phaseWeight d.val) 2 k mu *
          reconstruct d a 2 (k + mu + 1) mu =
        cycleMultiplier d k mu * a k mu := by
    simp only [reconstruct_two, shift_three, cycleMultiplier, mul_assoc]
  constructor
  · intro h k
    have hc := h 2 k 1
    rw [cycle_two_add_one, reconstruct_zero, closure, cycleMultiplier_eq] at hc
    simp only [ite_true] at hc
    calc
      (d.val (k + 1) ^ 3 - 1) * a k 1 =
          d.val (k + 1) ^ 3 * a k 1 - a k 1 := by ring
      _ = 0 := sub_eq_zero.mpr hc.symm
  · intro h b k mu
    rcases cycleIndexCases b with rfl | rfl | rfl
    · simp
    · simp
    · rw [cycle_two_add_one, reconstruct_zero, closure, cycleMultiplier_eq]
      by_cases hm : mu = 1
      · subst mu
        simp only [ite_true]
        have hc := h k
        have he : d.val (k + 1) ^ 3 * a k 1 - a k 1 = 0 := by
          calc
            _ = (d.val (k + 1) ^ 3 - 1) * a k 1 := by ring
            _ = 0 := hc
        exact (sub_eq_zero.mp he).symm
      · simp [hm]

/-- Existence and uniqueness for every base row, with the exact obstruction. -/
theorem existsUnique_recurrence_iff (d : PhaseTriple) (a : Index → Index → ℂ) :
    (∃! z : Coordinates, SatisfiesRecurrence (phaseWeight d.val) z ∧ z 0 = a) ↔
      ResonanceSupported d a := by
  constructor
  · rintro ⟨z, ⟨hz, ha⟩, _⟩
    have he : z = reconstruct d a := by
      simpa only [ha] using eq_reconstruct_of_recurrence d z hz
    apply (reconstruct_satisfies_iff d a).mp
    rw [← he]
    exact hz
  · intro ha
    refine ⟨reconstruct d a, ⟨(reconstruct_satisfies_iff d a).mpr ha, ?_⟩, ?_⟩
    · funext k mu
      exact reconstruct_zero d a k mu
    · intro z hz
      simpa only [hz.2] using eq_reconstruct_of_recurrence d z hz.1

/-- A concrete consumer through the existing inverse Fourier transform. -/
theorem inverse_reconstruct_pairEquations_iff (d : PhaseTriple)
    (a : Index → Index → ℂ) :
    (∀ b r s, pairEquation (phaseWeight d.val) (inverse (reconstruct d a)) b r s = 0) ↔
      ResonanceSupported d a :=
  (inverse_pairEquations_iff_recurrence _ (phaseWeight_ne_zero d.val
    (phaseTriple_ne_zero d)) (reconstruct d a)).trans (reconstruct_satisfies_iff d a)

/-- Every solution of the original scalar pair equations is this explicit
inverse transform of its extracted base row, with exactly the resonance support. -/
theorem pairEquations_iff_reconstruction (d : PhaseTriple) (y : Coordinates) :
    (∀ b r s, pairEquation (phaseWeight d.val) y b r s = 0) ↔
      ResonanceSupported d (forward y 0) ∧
        y = inverse (reconstruct d (forward y 0)) := by
  constructor
  · intro h
    have hr := (phasePairEquations_iff_recurrence d.val d.property.1 y).mp h
    have he := eq_reconstruct_of_recurrence d (forward y) hr
    constructor
    · apply (reconstruct_satisfies_iff d (forward y 0)).mp
      rw [← he]
      exact hr
    · calc
        y = inverse (forward y) := (inverse_forward y).symm
        _ = inverse (reconstruct d (forward y 0)) := congrArg inverse he
  · rintro ⟨hs, he⟩
    have hr := (inverse_reconstruct_pairEquations_iff d (forward y 0)).mpr hs
    simpa only [← he] using hr

end UnitaryErrorBases.ThreeCycleFourier

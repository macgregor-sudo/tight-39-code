module

public import ThreeCycleUnitaryErrorBasis
public import FourierTransport

@[expose] public section

/-!
# Global parameter recovery for the actual normalized monomial family

This is the normalized monomial family, using
the accepted monomialFamily, PhaseTriple, Index, Label and IsSpecialUnitary.
The construction uses the original nine-matrix array. No quotient topology, native
gauge classification, immersion or complete A2 theorem is asserted.

First-party proof using the accepted actual construction and pinned matrix
APIs. The imported ThreeCycleUnitaryErrorBasis source has SHA256
b2cf6cfa97aa341f80fc9781d28de4a79c1a47e9116a9ff0aefd40ddcffa71ef.
FourierTransport is the existing facade selecting the native Fourier owner,
not a second copy of its declarations. No upstream proof body is copied;
imported owners retain their license and attribution records.
Thanks to the native-model, CKM, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace UnitaryErrorBases.ThreeCycleNormalized

open ThreeCycleMatrix

/-- The exact common-right-normalized construction from MASTER section6.7. -/
def normalizedFamily (Q : Mat) (d : PhaseTriple) : Family :=
  fun p => Q * monomialFamily d p * Q.conjTranspose

private lemma index_cases (i : Index) : i = 0 ∨ i = 1 ∨ i = 2 :=
  (by decide : ∀ j : Index, j = 0 ∨ j = 1 ∨ j = 2) i

private lemma index_val_zero : (0 : Index).val = 0 := by decide
private lemma index_val_one : (1 : Index).val = 1 := by decide
private lemma index_val_two : (2 : Index).val = 2 := by decide

private lemma clock_weights_injective :
    Function.Injective (fun i : Index => omega ^ i.val) := by
  have hsquare : omega ^ 2 = -1 - omega := ThreeCycleFourier.omega_sq
  have h01 : (1 : ℂ) ≠ omega := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [omega] at hr
  have h02 : (1 : ℂ) ≠ omega ^ 2 := by
    intro h
    rw [hsquare] at h
    have hr := congrArg Complex.re h
    norm_num [omega] at hr
  have h12 : omega ≠ omega ^ 2 := by
    intro h
    rw [hsquare] at h
    have hi := congrArg Complex.im h
    have hs : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    norm_num [omega] at hi <;> nlinarith
  intro i j hij
  rcases index_cases i with rfl | rfl | rfl <;>
    rcases index_cases j with rfl | rfl | rfl
  all_goals simp only [index_val_zero, index_val_one, index_val_two] at hij
  · rfl
  · exact False.elim (h01 (by simpa only [pow_zero, pow_one] using
      (hij : omega ^ 0 = omega ^ 1)))
  · exact False.elim (h02 (by simpa only [pow_zero] using
      (hij : omega ^ 0 = omega ^ 2)))
  · exact False.elim (h01 (by simpa only [pow_zero, pow_one] using
      (hij.symm : omega ^ 0 = omega ^ 1)))
  · rfl
  · exact False.elim (h12 (by simpa only [pow_one] using
      (hij : omega ^ 1 = omega ^ 2)))
  · exact False.elim (h02 (by simpa only [pow_zero] using
      (hij.symm : omega ^ 0 = omega ^ 2)))
  · exact False.elim (h12 (by simpa only [pow_one] using
      (hij.symm : omega ^ 1 = omega ^ 2)))
  · rfl

private lemma clock_shift_commutant_scalar (R : Mat)
    (hc : R * clock = clock * R) (hs : R * shift = shift * R) :
    R = (R 0 0) • (1 : Mat) := by
  have hoff (i j : Index) (hij : i ≠ j) : R i j = 0 := by
    have he := congrArg (fun A : Mat => A i j) hc
    simp only [clock, Matrix.mul_diagonal, Matrix.diagonal_mul] at he
    have hdiff : omega ^ j.val - omega ^ i.val ≠ 0 := by
      intro hz
      exact hij (clock_weights_injective (sub_eq_zero.mp hz)).symm
    have hz : R i j * (omega ^ j.val - omega ^ i.val) = 0 := by
      calc
        _ = R i j * omega ^ j.val - omega ^ i.val * R i j := by ring
        _ = 0 := sub_eq_zero.mpr he
    exact (mul_eq_zero.mp hz).resolve_right hdiff
  have hstep (j : Index) : R (j + 1) (j + 1) = R j j := by
    have he := congrArg (fun A : Mat => A (j + 1) j) hs
    simpa only [mul_shift_apply, shift_mul_apply, add_sub_cancel_right] using he
  have hdiag (i : Index) : R i i = R 0 0 := by
    rcases index_cases i with rfl | rfl | rfl
    · rfl
    · simpa only [zero_add] using hstep 0
    · calc
        R 2 2 = R 1 1 := by
          simpa only [show (1 : Index) + 1 = 2 by decide] using hstep 1
        _ = R 0 0 := by simpa only [zero_add] using hstep 0
  ext i j
  change R i j = R 0 0 * (1 : Mat) i j
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.one_apply, ↓reduceIte, mul_one] using hdiag i
  · simp only [Matrix.one_apply, if_neg hij, mul_zero, hoff i j hij]

private lemma monomial_clock (d : PhaseTriple) :
    monomialFamily d (1, 0) = clock := by
  simp [monomialFamily, phaseMatrix, index_val_one, index_val_zero,
    show (0 : Index) ≠ 2 by decide]

private lemma monomial_shift (d : PhaseTriple) :
    monomialFamily d (0, 1) = shift := by
  simp [monomialFamily, phaseMatrix, index_val_one, index_val_zero,
    show (1 : Index) ≠ 2 by decide]

private lemma monomial_phase_entry (d : PhaseTriple) (j : Index) :
    monomialFamily d (0, 2) (j + 2) j = d.val j := by
  rw [monomialFamily_eq]
  change (leftFactor d 2 * clock ^ 0) (j + 2) j = d.val j
  simp only [pow_zero, Matrix.mul_one, leftFactor_apply,
    ThreeCycleFourier.phaseEntry, ↓reduceIte]

private lemma conjugate_equality_intertwines (Q Q' A B : Mat)
    (hQ : Q.conjTranspose * Q = 1) (hQ' : Q'.conjTranspose * Q' = 1)
    (h : Q * A * Q.conjTranspose = Q' * B * Q'.conjTranspose) :
    A * (Q.conjTranspose * Q') = (Q.conjTranspose * Q') * B := by
  calc
    A * (Q.conjTranspose * Q') =
        (Q.conjTranspose * Q) * A * (Q.conjTranspose * Q') := by
      rw [hQ, Matrix.one_mul]
    _ = Q.conjTranspose * (Q * A * Q.conjTranspose) * Q' := by
      simp only [Matrix.mul_assoc]
    _ = Q.conjTranspose * (Q' * B * Q'.conjTranspose) * Q' := by rw [h]
    _ = (Q.conjTranspose * Q') * B * (Q'.conjTranspose * Q') := by
      simp only [Matrix.mul_assoc]
    _ = (Q.conjTranspose * Q') * B := by rw [hQ', Matrix.mul_one]

/-- Equality of the actual normalized constructed arrays recovers the entire
phase triple and the conjugating matrix up to a central cube root of unity.
The matrix and phase hypotheses are exactly the accepted original ones. -/
theorem normalizedFamily_parameter_recovery
    (Q Q' : Mat) (d d' : PhaseTriple)
    (hQ : IsSpecialUnitary Q) (hQ' : IsSpecialUnitary Q')
    (heq : normalizedFamily Q d = normalizedFamily Q' d') :
    d = d' ∧ ∃ c : ℂ, c ^ 3 = 1 ∧ Q' = c • Q := by
  have hinter (p : Label) :
      monomialFamily d p * (Q.conjTranspose * Q') =
        (Q.conjTranspose * Q') * monomialFamily d' p :=
    conjugate_equality_intertwines Q Q' _ _ hQ.1 hQ'.1 (congrFun heq p)
  let R : Mat := Q.conjTranspose * Q'
  have hc : R * clock = clock * R := by
    simpa only [monomial_clock] using (hinter (1, 0)).symm
  have hs : R * shift = shift * R := by
    simpa only [monomial_shift] using (hinter (0, 1)).symm
  let c : ℂ := R 0 0
  have hR : R = c • (1 : Mat) := clock_shift_commutant_scalar R hc hs
  have hQQ : Q * Q.conjTranspose = 1 := mul_eq_one_comm.mp hQ.1
  have hcentral : Q' = c • Q := by
    calc
      Q' = (Q * Q.conjTranspose) * Q' := by rw [hQQ, Matrix.one_mul]
      _ = Q * R := by simp only [R, Matrix.mul_assoc]
      _ = Q * (c • (1 : Mat)) := by rw [hR]
      _ = c • Q := by rw [Matrix.mul_smul, Matrix.mul_one]
  have hcube : c ^ 3 = 1 := by
    have hdet := congrArg Matrix.det hcentral
    have hcard : Fintype.card Index = 3 := by decide
    rw [hQ'.2, Matrix.det_smul, hcard, hQ.2, mul_one] at hdet
    exact hdet.symm
  have hc0 : c ≠ 0 := by
    intro hz
    exact zero_ne_one (by
      simpa only [hz, zero_pow (by decide : (3 : ℕ) ≠ 0)] using hcube)
  have hd : d = d' := by
    apply Subtype.ext
    funext j
    have hp := hinter (0, 2)
    change monomialFamily d (0, 2) * R = R * monomialFamily d' (0, 2) at hp
    rw [hR, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul] at hp
    have he := congrArg (fun A : Mat => A (j + 2) j) hp
    change c * monomialFamily d (0, 2) (j + 2) j =
      c * monomialFamily d' (0, 2) (j + 2) j at he
    rw [monomial_phase_entry, monomial_phase_entry] at he
    exact mul_left_cancel₀ hc0 he
  exact ⟨hd, c, hcube, hcentral⟩

end UnitaryErrorBases.ThreeCycleNormalized

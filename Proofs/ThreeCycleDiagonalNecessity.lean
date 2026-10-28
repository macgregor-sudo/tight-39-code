module

public import ThreeCycleTangentParameters
import all FourierTransport

/-!
# Common diagonals follow from the original within-block equations

An imaginary three-vector with zero sum and one nonzero Fourier mode zero
vanishes: conjugation kills the opposite mode and Fourier inversion finishes.
This is applied to diagonal differences of actual trivialized kernel vectors.
First-party proof; imported mathlib provenance unchanged. No release license assigned.
-/

@[expose] public section
noncomputable section

namespace UnitaryErrorBases.ThreeCycleMatrix

open ThreeCycleFourier ArchitectureUEBDerivative
open scoped BigOperators

lemma star_character (r : Index) : star (character r) = character (-r) := by
  change star (UnitaryErrorBases.omega ^ r.val) = UnitaryErrorBases.omega ^ (-r).val
  rw [star_pow, omega_star, ← pow_mul, pow_eq_pow_mod _ omega_cube]
  congr 1
  exact (by decide : ∀ r : Index, 2 * r.val % 3 = (-r).val) r

theorem imaginary_threeVector_eq_zero (v : Index → ℂ) (q : Index) (hq : q ≠ 0)
    (hv : ∀ k, star (v k) = -v k) (hzero : ∑ k, v k = 0)
    (hmode : ∑ k, character (q * k) * v k = 0) : ∀ k, v k = 0 := by
  have hnegative : ∑ k, character (-q * k) * v k = 0 := by
    have hs := congrArg star hmode
    simp only [star_sum, star_mul, star_character, hv, star_zero] at hs
    have he : (∑ k, -(v k) * character (-(q * k))) =
        -(∑ k, character (-q * k) * v k) := by
      simp only [neg_mul, Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    exact neg_eq_zero.mp (he.symm.trans hs)
  have hall : ∀ r : Index, ∑ k, v k * character (r * k) = 0 := by
    intro r
    rcases (by decide : ∀ q r : Index, q ≠ 0 → r = 0 ∨ r = q ∨ r = -q) q r hq
      with hr | hr | hr
    · subst r
      simpa [character] using hzero
    · subst r
      simpa [mul_comm] using hmode
    · subst r
      simpa [mul_comm] using hnegative
  have hf : forward (fun a _ _ => v a) = 0 := by
    funext b k mu
    change (1 / 3 : ℂ) * (∑ a, v a * character (-mu * a)) = 0
    rw [hall, mul_zero]
  have hi := inverse_forward (fun a _ _ => v a)
  rw [hf] at hi
  intro k
  have he := congrFun (congrFun (congrFun hi k) 0) 0
  simpa [inverse] using he.symm

theorem toCoordinates_trace_of_mem_firstOrder (d : PhaseTriple) (V : Family)
    (hV : V ∈ firstOrderSpace (monomialFamily d)) (p : Label) :
    Matrix.trace (toCoordinates d V p) = 0 := by
  have hk := hV
  change fderiv ℝ residualOnAmbient (monomialFamily d) V = 0 at hk
  rw [(hasFDerivAt_residual (monomialFamily d)).fderiv] at hk
  have hd := congrArg (fun R : AmbientResidual => R.2.1 p) hk
  change detMultilinear.linearDeriv (monomialFamily d p) (V p) = 0 at hd
  calc
    Matrix.trace (toCoordinates d V p) =
      detMultilinear.linearDeriv (monomialFamily d p)
        (fromCoordinates d (toCoordinates d V) p) :=
      (determinantDerivative_fromCoordinates d (toCoordinates d V) p).symm
    _ = 0 := by rw [fromCoordinates_toCoordinates]; exact hd

theorem toCoordinates_diagonal_of_mem_firstOrder (d : PhaseTriple) (V : Family)
    (hV : V ∈ firstOrderSpace (monomialFamily d)) (a a' b k : Index) :
    toCoordinates d V (a, b) k k = toCoordinates d V (a', b) k k := by
  by_cases ha : a = a'
  · subst a'; rfl
  let M := toCoordinates d V
  have hanti : ∀ p, (M p).conjTranspose = -M p :=
    toCoordinates_antiHermitian_of_mem_firstOrder d V hV
  have ht : ∀ p, Matrix.trace (M p) = 0 := toCoordinates_trace_of_mem_firstOrder d V hV
  have hpq : (a, b) ≠ (a', b) := fun h => ha (congrArg Prod.fst h)
  have hp := (gram_pair_of_mem_firstOrder _ V hV).2 (a, b) (a', b) hpq
  have hp' : Matrix.trace
      ((fromCoordinates d M (a, b)).conjTranspose * monomialFamily d (a', b) +
        (monomialFamily d (a, b)).conjTranspose * fromCoordinates d M (a', b)) = 0 := by
    simpa only [M, fromCoordinates_toCoordinates] using hp
  rw [pair_trace_eq_matrix d M a b a' b (hanti (a, b)), rightFactor_character,
    leftFactor_star_mul, Matrix.one_mul, Matrix.mul_one] at hp'
  have hs : ∑ j : Index, (M (a', b) j j - M (a, b) j j) = 0 := by
    rw [Finset.sum_sub_distrib]
    change Matrix.trace (M (a', b)) - Matrix.trace (M (a, b)) = 0
    rw [ht, ht, sub_self]
  have hv : ∀ j, star (M (a', b) j j - M (a, b) j j) =
      -(M (a', b) j j - M (a, b) j j) := by
    intro j
    have h₁ := congrFun (congrFun (hanti (a', b)) j) j
    have h₂ := congrFun (congrFun (hanti (a, b)) j) j
    change star (M (a', b) j j) = -M (a', b) j j at h₁
    change star (M (a, b) j j) = -M (a, b) j j at h₂
    rw [star_sub, h₁, h₂]
    ring
  have hm : ∑ j : Index, character ((a' - a) * j) *
      (M (a', b) j j - M (a, b) j j) = 0 := by
    simpa only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul,
      Matrix.sub_apply] using hp'
  have hh := imaginary_threeVector_eq_zero _ (a' - a) (sub_ne_zero.mpr (Ne.symm ha))
    hv hs hm k
  exact (sub_eq_zero.mp hh).symm

end UnitaryErrorBases.ThreeCycleMatrix

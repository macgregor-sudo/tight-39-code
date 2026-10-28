module

public import ThreeCycleNormalizedParameterRecovery
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-!
# Differential injectivity of the actual lifted normalized family

This proves the finite-matrix zero-derivative argument in
MASTER section 6.7 for the exact `normalizedFamily`, actual PhaseTriple curves,
and explicitly skew-Hermitian, trace-zero conjugation velocities. It does not
declare a quotient manifold, analytic immersion, or native differential result.

The short private clock/shift calculation adapts the first-party private proof
in ThreeCycleNormalizedParameterRecovery, SHA256
cd0d23199cc53cd9e8a6add3e0cd1c99df949122d973a7163e3bd8a4f4326320.
No upstream proof body is copied. Pinned mathlib calculus APIs are imported;
their original owners retain their licenses and attribution.
Thanks to the native-model, CKM, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
open scoped Matrix.Norms.Elementwise

namespace UnitaryErrorBases.ThreeCycleNormalized
open ThreeCycleMatrix

/-- Derivative of the actual phase-dependent monomial matrix. -/
def monomialVelocity (v : Index → ℂ) (p : Label) : Mat :=
  shift ^ p.2.val * Matrix.diagonal (fun j => if p.2 = 2 then v j else 0) *
    clock ^ p.1.val

/-- The lifted differential at right-trivialized conjugation velocity `Q * A`.
No tangent or manifold structure is defined by this formula. -/
def normalizedVelocity (Q : Mat) (d : PhaseTriple) (A : Mat) (v : Index → ℂ) : Family :=
  fun p => Q * (A * monomialFamily d p - monomialFamily d p * A +
    monomialVelocity v p) * Q.conjTranspose

private lemma matrix_hasDerivAt_mul {f g : ℝ → Mat} {f' g' : Mat} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => f s * g s) (f' * g t + f t * g') t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i) k).mul
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp hg k) j)))
  simpa only [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib, Pi.mul_apply] using h

private lemma matrix_hasDerivAt_conjTranspose {f : ℝ → Mat} {f' : Mat} {t : ℝ}
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s).conjTranspose) f'.conjTranspose t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hf j) i).star

private lemma phaseMatrix_hasDerivAt (d : ℝ → PhaseTriple) (v : Index → ℂ) (t : ℝ)
    (hd : HasDerivAt (fun s => (d s).val) v t) (b : Index) :
    HasDerivAt (fun s => phaseMatrix (d s) b)
      (Matrix.diagonal (fun j => if b = 2 then v j else 0)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  by_cases hij : i = j
  · subst j
    by_cases hb : b = 2
    · simpa only [phaseMatrix, Matrix.diagonal_apply, ↓reduceIte, hb] using
        hasDerivAt_pi.mp hd i
    · simpa only [phaseMatrix, Matrix.diagonal_apply, ↓reduceIte, ite_eq_right hb] using
        hasDerivAt_const t (1 : ℂ)
  · simpa only [phaseMatrix, Matrix.diagonal_apply, ite_eq_right hij] using
      hasDerivAt_const t (0 : ℂ)

/-- Differentiation uses the original order `shift * phase * clock`. -/
theorem monomialFamily_hasDerivAt (d : ℝ → PhaseTriple) (v : Index → ℂ) (t : ℝ)
    (hd : HasDerivAt (fun s => (d s).val) v t) (p : Label) :
    HasDerivAt (fun s => monomialFamily (d s) p) (monomialVelocity v p) t := by
  have h := matrix_hasDerivAt_mul
    (matrix_hasDerivAt_mul (hasDerivAt_const t (shift ^ p.2.val))
      (phaseMatrix_hasDerivAt d v t hd p.2))
    (hasDerivAt_const t (clock ^ p.1.val))
  simpa only [monomialFamily, monomialVelocity, zero_mul, mul_zero, zero_add, add_zero] using h

/-- Actual derivative formula along a real curve; the skew condition is explicit.
The phase constraint is retained by the original PhaseTriple subtype. -/
theorem normalizedFamily_hasDerivAt (Q : ℝ → Mat) (d : ℝ → PhaseTriple)
    (A : Mat) (v : Index → ℂ) (t : ℝ)
    (hQ : HasDerivAt Q (Q t * A) t)
    (hd : HasDerivAt (fun s => (d s).val) v t)
    (hA : A.conjTranspose = -A) :
    HasDerivAt (fun s => normalizedFamily (Q s) (d s))
      (normalizedVelocity (Q t) (d t) A v) t := by
  apply hasDerivAt_pi.mpr
  intro p
  have h := matrix_hasDerivAt_mul
    (matrix_hasDerivAt_mul hQ (monomialFamily_hasDerivAt d v t hd p))
    (matrix_hasDerivAt_conjTranspose hQ)
  have he : normalizedVelocity (Q t) (d t) A v p =
      (Q t * A * monomialFamily (d t) p + Q t * monomialVelocity v p) *
        (Q t).conjTranspose + Q t * monomialFamily (d t) p * (Q t * A).conjTranspose := by
    simp only [normalizedVelocity, Matrix.conjTranspose_mul, hA, neg_mul,
      mul_neg, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_assoc, sub_eq_add_neg]
    abel
  rw [he]
  exact h

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
    norm_num [omega] at hi
    nlinarith
  intro i j hij
  rcases index_cases i with rfl | rfl | rfl <;>
    rcases index_cases j with rfl | rfl | rfl
  all_goals simp only [index_val_zero, index_val_one, index_val_two, pow_zero, pow_one] at hij
  all_goals first | rfl | exact False.elim (h01 hij) | exact False.elim (h01 hij.symm) |
    exact False.elim (h02 hij) | exact False.elim (h02 hij.symm) |
    exact False.elim (h12 hij) | exact False.elim (h12 hij.symm)

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
  · simp only [Matrix.one_apply, ite_eq_right hij, mul_zero, hoff i j hij]

private lemma monomial_clock (d : PhaseTriple) : monomialFamily d (1, 0) = clock := by
  simp [monomialFamily, phaseMatrix, show (0 : Index).val = 0 by decide,
    show (1 : Index).val = 1 by decide, show (0 : Index) ≠ 2 by decide]

private lemma monomial_shift (d : PhaseTriple) : monomialFamily d (0, 1) = shift := by
  simp [monomialFamily, phaseMatrix, show (0 : Index).val = 0 by decide,
    show (1 : Index).val = 1 by decide, show (1 : Index) ≠ 2 by decide]

private lemma monomialVelocity_clock (v : Index → ℂ) : monomialVelocity v (1, 0) = 0 := by
  simp [monomialVelocity, show (0 : Index) ≠ 2 by decide]

private lemma monomialVelocity_shift (v : Index → ℂ) : monomialVelocity v (0, 1) = 0 := by
  simp [monomialVelocity, show (1 : Index) ≠ 2 by decide]

private lemma monomialVelocity_phase_entry (v : Index → ℂ) (j : Index) :
    monomialVelocity v (0, 2) (j + 2) j = v j := by
  simp only [monomialVelocity, show (0 : Index).val = 0 by decide, pow_zero,
    Matrix.mul_one, Matrix.mul_diagonal, shift_pow_apply, ↓reduceIte, one_mul]

/-- The concrete lifted differential has zero kernel on trace-zero conjugation
directions. Both original SU(3) equations and the actual phase subtype remain. -/
theorem normalizedVelocity_eq_zero_iff (Q : Mat) (d : PhaseTriple)
    (hQ : IsSpecialUnitary Q) (A : Mat) (v : Index → ℂ)
    (htrace : Matrix.trace A = 0) :
    normalizedVelocity Q d A v = 0 ↔ A = 0 ∧ v = 0 := by
  constructor
  · intro hz
    have hinter (p : Label) :
        A * monomialFamily d p - monomialFamily d p * A + monomialVelocity v p = 0 := by
      have he := congrArg (fun M : Mat => Q.conjTranspose * M * Q) (congrFun hz p)
      simpa only [normalizedVelocity, Matrix.mul_assoc, ← Matrix.mul_assoc Q.conjTranspose Q,
        hQ.1, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Pi.zero_apply] using he
    have hc : A * clock = clock * A := by
      have h := hinter (1, 0)
      simpa only [monomial_clock, monomialVelocity_clock, add_zero, sub_eq_zero] using h
    have hs : A * shift = shift * A := by
      have h := hinter (0, 1)
      simpa only [monomial_shift, monomialVelocity_shift, add_zero, sub_eq_zero] using h
    have hscalar := clock_shift_commutant_scalar A hc hs
    have hc0 : A 0 0 = 0 := by
      rw [hscalar, Matrix.trace_smul, Matrix.trace_one] at htrace
      change A 0 0 * (3 : ℂ) = 0 at htrace
      exact (mul_eq_zero.mp htrace).resolve_right (by norm_num)
    have hA : A = 0 := by simpa only [hc0, zero_smul] using hscalar
    refine ⟨hA, ?_⟩
    funext j
    change v j = 0
    have h := congrArg (fun M : Mat => M (j + 2) j) (hinter (0, 2))
    simpa only [hA, zero_mul, mul_zero, sub_zero, zero_add,
      monomialVelocity_phase_entry, Matrix.zero_apply] using h
  · rintro ⟨rfl, rfl⟩
    ext p i j
    simp [normalizedVelocity, monomialVelocity]

/-- Zero derivative of the exact normalized family along actual parameter curves
forces both parameter velocities to vanish. This is a lifted curve statement;
the special-unitary tangent identification and quotient charts are not assumed
to have been supplied by a manifold instance. -/
theorem normalizedFamily_zero_derivative_recovers_velocity
    (Q : ℝ → Mat) (d : ℝ → PhaseTriple) (A : Mat) (v : Index → ℂ) (t : ℝ)
    (hSU : IsSpecialUnitary (Q t))
    (hQ : HasDerivAt Q (Q t * A) t)
    (hd : HasDerivAt (fun s => (d s).val) v t)
    (hskew : A.conjTranspose = -A) (htrace : Matrix.trace A = 0)
    (hzero : HasDerivAt (fun s => normalizedFamily (Q s) (d s)) 0 t) :
    A = 0 ∧ v = 0 := by
  exact (normalizedVelocity_eq_zero_iff (Q t) (d t) hSU A v htrace).mp
    ((normalizedFamily_hasDerivAt Q d A v t hQ hd hskew).unique hzero)

end UnitaryErrorBases.ThreeCycleNormalized

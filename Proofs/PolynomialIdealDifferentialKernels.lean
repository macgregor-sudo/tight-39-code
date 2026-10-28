module

public import CenteredFirstCoefficient
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Maps

@[expose] public section

/-!
Equal polynomial ideals have the same first-order kernels at a common zero.
The original translated degree-one coefficient matrix is retained literally.
The proof uses ordinary polynomial coefficients and the already accepted affine
coefficient theorem; no analytic carrier, formal-series comparison or desired
kernel equality is assumed. First-party proof; no implementation body copied.
-/

noncomputable section

namespace PolynomialIdealDifferentialKernels

open MvPolynomial PolynomialJets PolynomialJets.AffineMixedCoefficients
open scoped BigOperators

variable {R σ ι κ : Type*} [CommRing R] [Fintype σ]

private theorem coeff_add_eq {τ : Type*} (a b : MvPolynomial τ R) (d : τ →₀ ℕ) :
    (a + b).coeff d = a.coeff d + b.coeff d :=
  map_add (lcoeff R d) a b

private theorem coeff_zero_mul {τ : Type*} (a b : MvPolynomial τ R) :
    (a * b).coeff 0 = a.coeff 0 * b.coeff 0 :=
  map_mul (constantCoeff : MvPolynomial τ R →+* R) a b

private theorem first_coeff_mul (a b : MvPolynomial (Fin 2) R) :
    (a * b).coeff firstExponent =
      a.coeff firstExponent * b.coeff 0 + a.coeff 0 * b.coeff firstExponent := by
  have h := congrArg (fun q : MvPolynomial (Fin 2) R => q.coeff 0)
    (pderiv_mul (i := (0 : Fin 2)) (f := a) (g := b))
  simpa only [coeff_add_eq, coeff_zero_mul, coeff_pderiv, zero_add,
    Finsupp.zero_apply, Nat.cast_zero, Nat.cast_one, mul_one, firstExponent] using h

/-- Ordinary first-jet zero ideal: both the value and the first directional
coefficient vanish. It is an ideal in the existing two-variable polynomial ring. -/
def zeroFirstJetIdeal : Ideal (MvPolynomial (Fin 2) R) where
  carrier := {q | q.coeff 0 = 0 ∧ q.coeff firstExponent = 0}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    intro a b ha hb
    constructor
    · rw [coeff_add_eq, ha.1, hb.1, add_zero]
    · rw [coeff_add_eq, ha.2, hb.2, add_zero]
  smul_mem' := by
    intro a b hb
    change (a * b).coeff 0 = 0 ∧ (a * b).coeff firstExponent = 0
    constructor
    · rw [coeff_zero_mul, hb.1, mul_zero]
    · rw [first_coeff_mul, hb.1, hb.2, mul_zero, mul_zero, add_zero]

/-- The actual affine substitution, using only the existing first variable. -/
def affineDirection (p u : σ → R) : MvPolynomial σ R →+* MvPolynomial (Fin 2) R :=
  eval₂Hom C (fun k => affineTwo (p k) (u k) 0)

theorem affineDirection_constant (p u : σ → R) (f : MvPolynomial σ R) :
    (affineDirection p u f).coeff 0 = eval p f := by
  have hh : (constantCoeff : MvPolynomial (Fin 2) R →+* R).comp
      (affineDirection p u) = eval p := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [affineDirection]
    · intro k
      simp [affineDirection, affineTwo]
  exact RingHom.congr_fun hh f

theorem affineDirection_mem_zeroFirstJetIdeal (p u : σ → R) (f : MvPolynomial σ R) :
    affineDirection p u f ∈ (zeroFirstJetIdeal : Ideal (MvPolynomial (Fin 2) R)) ↔
      eval p f = 0 ∧
        (∑ k : σ, (translate p f).coeff (Finsupp.single k 1) * u k) = 0 := by
  change (affineDirection p u f).coeff 0 = 0 ∧
    (affineDirection p u f).coeff firstExponent = 0 ↔ _
  rw [affineDirection_constant]
  change _ ∧ (eval₂Hom C (fun k => affineTwo (p k) (u k) 0) f).coeff
    firstExponent = 0 ↔ _
  rw [first_coeff_affine_eq_centered_linear]

/-- Equal original ideals give equal full centered linear-matrix kernels at
the same explicit common zero. No rowwise ideal-multiplier table is needed. -/
theorem equal_span_linearMatrix_zero_iff
    (f : ι → MvPolynomial σ R) (g : κ → MvPolynomial σ R)
    (hIdeal : Ideal.span (Set.range f) = Ideal.span (Set.range g))
    (p u : σ → R) (hf : ∀ i, eval p (f i) = 0) (hg : ∀ j, eval p (g j) = 0) :
    (∀ i, (∑ k : σ, equationLinearMatrix (fun i => translate p (f i)) i k * u k) = 0) ↔
      (∀ j, (∑ k : σ, equationLinearMatrix (fun j => translate p (g j)) j k * u k) = 0) := by
  let J : Ideal (MvPolynomial σ R) :=
    Ideal.comap (affineDirection p u) zeroFirstJetIdeal
  have hspan (a : ι → MvPolynomial σ R) (ha : ∀ i, eval p (a i) = 0) :
      Ideal.span (Set.range a) ≤ J ↔
        ∀ i, (∑ k : σ, equationLinearMatrix (fun i => translate p (a i)) i k * u k) = 0 := by
    rw [Ideal.span_le]
    constructor
    · intro h i
      have hi := h (Set.mem_range_self i)
      exact ((affineDirection_mem_zeroFirstJetIdeal p u (a i)).mp hi).2
    · rintro h _ ⟨i, rfl⟩
      exact (affineDirection_mem_zeroFirstJetIdeal p u (a i)).mpr ⟨ha i, h i⟩
  have hspanG : Ideal.span (Set.range g) ≤ J ↔
      ∀ j, (∑ k : σ, equationLinearMatrix (fun j => translate p (g j)) j k * u k) = 0 := by
    rw [Ideal.span_le]
    constructor
    · intro h j
      exact ((affineDirection_mem_zeroFirstJetIdeal p u (g j)).mp
        (h (Set.mem_range_self j))).2
    · rintro h _ ⟨j, rfl⟩
      exact (affineDirection_mem_zeroFirstJetIdeal p u (g j)).mpr ⟨hg j, h j⟩
  rw [← hspan f hf, ← hspanG, hIdeal]

/-- A common zero need only be supplied for one generating family; equality
of the actual ideals proves it for every generator of the other family. -/
theorem eval_eq_zero_of_equal_span
    (f : ι → MvPolynomial σ R) (g : κ → MvPolynomial σ R)
    (hIdeal : Ideal.span (Set.range f) = Ideal.span (Set.range g))
    (p : σ → R) (hf : ∀ i, eval p (f i) = 0) :
    ∀ j, eval p (g j) = 0 := by
  have hle : Ideal.span (Set.range f) ≤ RingHom.ker (eval p) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hf i
  intro j
  apply hle
  rw [hIdeal]
  exact Ideal.subset_span (Set.mem_range_self j)

end PolynomialIdealDifferentialKernels

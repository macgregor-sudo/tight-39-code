module

public import ThreeCycleDiagonalNecessity
import all FourierTransport

/-!
# Recover actual tangent parameters

The diagonal data are extracted at block label a=0. Off-diagonal data retain
the original orientation. This closes surjectivity of the explicit constructor;
real-linearity, uniqueness and the frozen NormalForm equivalence are separate.
First-party proof; imported mathlib provenance unchanged. No release license assigned.
-/

@[expose] public section
noncomputable section

namespace UnitaryErrorBases.ThreeCycleMatrix

open ThreeCycleFourier

def diagonalParameters (M : Family) (b : Index) (t : Fin 2) : ℝ :=
  (M (0, b) (t.val : Index) (t.val : Index)).im

lemma imaginary_eq_I_mul_im (z : ℂ) (hz : star z = -z) :
    z = Complex.I * (z.im : ℂ) := by
  have hr := congrArg Complex.re hz
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at hr
  apply Complex.ext
  · simp
    linarith
  · simp

theorem diagonalParameters_recover (M : Family)
    (hanti : ∀ p, (M p).conjTranspose = -M p)
    (ht : ∀ p, Matrix.trace (M p) = 0) (b k : Index) :
    Complex.I * (tracelessDiagonal (diagonalParameters M b) k : ℂ) = M (0, b) k k := by
  have him (j : Index) : M (0, b) j j = Complex.I * ((M (0, b) j j).im : ℂ) := by
    apply imaginary_eq_I_mul_im
    exact congrFun (congrFun (hanti (0, b)) j) j
  have hs : M (0, b) 0 0 + M (0, b) 1 1 + M (0, b) 2 2 = 0 :=
    (Fin.sum_univ_three (fun j : Index => M (0, b) j j)).symm.trans (ht (0, b))
  rcases (by decide : ∀ k : Index, k = 0 ∨ k = 1 ∨ k = 2) k with hk | hk | hk
  · subst k
    simpa [tracelessDiagonal, diagonalParameters] using (him 0).symm
  · subst k
    simpa [tracelessDiagonal, diagonalParameters] using (him 1).symm
  · subst k
    simp only [tracelessDiagonal, show (2 : Index) ≠ 0 by decide,
      show (2 : Index) ≠ 1 by decide, if_false, diagonalParameters]
    change Complex.I * ((-(M (0, b) 0 0).im - (M (0, b) 1 1).im : ℝ) : ℂ) = _
    rw [Complex.ofReal_sub, Complex.ofReal_neg, mul_sub, mul_neg, ← him 0, ← him 1]
    linear_combination -hs

theorem parameterMatrix_recover (M : Family)
    (hanti : ∀ p, (M p).conjTranspose = -M p)
    (ht : ∀ p, Matrix.trace (M p) = 0)
    (hdiag : ∀ a a' b k, M (a, b) k k = M (a', b) k k) :
    parameterMatrix (diagonalParameters M) (offDiagonalCoordinates M) = M := by
  funext p i j
  by_cases hij : i = j
  · subst j
    change parameterMatrix _ _ (p.1, p.2) i i = _
    rw [parameterMatrix_diagonal, diagonalParameters_recover M hanti ht]
    exact hdiag 0 p.1 p.2 i
  · by_cases hj : j = i + 1
    · simp only [parameterMatrix, if_neg hij, if_pos hj, offDiagonalCoordinates]
      rw [hj]
    · have hi : i = j + 1 :=
        (by decide : ∀ i j : Index, i ≠ j → j ≠ i + 1 → i = j + 1) i j hij hj
      simp only [parameterMatrix, if_neg hij, if_neg hj, offDiagonalCoordinates]
      rw [← hi]
      have ha := congrFun (congrFun (hanti p) i) j
      change star (M p j i) = -M p i j at ha
      rw [ha, neg_neg]

/-- Exact surjectivity onto the original unrestricted real derivative kernel.
Resonance support is the only condition on the complex Fourier seed. -/
theorem mem_firstOrder_iff_parameters (d : PhaseTriple) (V : Family) :
    V ∈ firstOrderSpace (monomialFamily d) ↔
      ∃ (s : Index → Fin 2 → ℝ) (a : Index → Index → ℂ),
        ResonanceSupported d a ∧
          V = fromCoordinates d (parameterMatrix s (inverse (reconstruct d a))) := by
  constructor
  · intro hV
    let M := toCoordinates d V
    have hr := offDiagonal_reconstruction_of_mem_firstOrder d V hV
    refine ⟨diagonalParameters M, forward (offDiagonalCoordinates M) 0, hr.1, ?_⟩
    rw [← hr.2]
    rw [parameterMatrix_recover M
      (toCoordinates_antiHermitian_of_mem_firstOrder d V hV)
      (toCoordinates_trace_of_mem_firstOrder d V hV)
      (toCoordinates_diagonal_of_mem_firstOrder d V hV)]
    exact (fromCoordinates_toCoordinates d V).symm
  · rintro ⟨s, a, ha, rfl⟩
    exact parameterMatrix_mem_firstOrder d s a ha

end UnitaryErrorBases.ThreeCycleMatrix

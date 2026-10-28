module

public import NativeExactCKMAllG
public import NativeConfigurationIdealEquality

/-!
# The original F polynomials at the literal CKM point

Every original G generator vanishes by `ExactCKMAllG.all_gRow_eval_zero`.
The accepted equality of the literal F and G polynomial ideals, at exactly
`h = 1/2` and `t = 1/3`, transfers that common zero to every original F
generator. No F coefficient, point coordinate, or row-numbering convention
is replaced, and no geometric conclusion is inferred here.

This is first-party composition of accepted project theorems. Imported
native/model and mathlib notices remain with their source owners. Thanks to
the CKM construction and Lean contributors. “If I have seen further it is
by standing on the sholders of Giants.” — Isaac Newton, letter to Robert
Hooke, 1676. No release license is selected here.
-/

@[expose] public section
noncomputable section

namespace QuadraticCertificate.ExactCKMAllF

open NativePolynomial.ConfigurationResiduals
open QuadraticCertificate.ExactCKMConfiguration
open MvPolynomial

/-- Every one of the 2,184 originally numbered F polynomials vanishes at the
same literal CKM configuration, with the original coefficients. -/
theorem all_fRow_eval_zero (r : Fin 2184) :
    MvPolynomial.eval pointCoordinates
      (fRow (1/2 : ℝ) (1/3 : ℝ) r) = 0 := by
  have hker :
      Ideal.span (Set.range (gRow (1/2 : ℝ) (1/3 : ℝ))) ≤
        RingHom.ker (eval pointCoordinates) := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact ExactCKMAllG.all_gRow_eval_zero j
  exact hker (fRow_mem_gSpan (1/2 : ℝ) (1/3 : ℝ)
    (by norm_num) (by norm_num) r)

/-- Identical original F evaluations reject the changed value one. -/
theorem all_fRow_changed_value_control (r : Fin 2184) :
    MvPolynomial.eval pointCoordinates
      (fRow (1/2 : ℝ) (1/3 : ℝ) r) ≠ 1 := by
  rw [all_fRow_eval_zero r]
  exact zero_ne_one

end QuadraticCertificate.ExactCKMAllF

#print axioms QuadraticCertificate.ExactCKMAllF.all_fRow_eval_zero
#print axioms QuadraticCertificate.ExactCKMAllF.all_fRow_changed_value_control

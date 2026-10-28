module

public import NativeActualPointPartialPreservation
public import SupportedQuadraticStress
public import Mathlib.Algebra.MvPolynomial.PDeriv

@[expose] public section

/-!
Conditional literal-original-F consumer. `seed_residual_zero` supplies the
native base-point identity. Every quadratic/column/support hypothesis is
visible. No H/T covector, phase identity or analytic derivative is manufactured.
First-party composition; unchanged native and mathlib imports retain their
existing licenses and source attribution.
-/

noncomputable section

namespace Option2.NativeStress

open scoped BigOperators

abbrev NativeAmbient := Fin 1053 → ℝ
abbrev NativeRows := Fin 2184 → ℝ

/-- Exact existing original residuals: original numbering, half and third. -/
def originalF (x : NativeAmbient) : NativeRows := fun r =>
  MvPolynomial.eval x
    (NativePolynomial.ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r)

def originalSeed : NativeAmbient :=
  NativePolynomial.PartialAction.pack
    NativePolynomial.PartialAction.Actual.actualConfiguration

theorem seed_residual_zero (r : Fin 2184) : originalF originalSeed r = 0 :=
  NativePolynomial.PartialAction.Actual.actual_input_all_fRows r

/-- The Jacobian binding quantifies all1053 columns of all2184 original rows.
This record is an unpaid input, not a constructed native instance. -/
structure OriginalQuadraticData where
  algebra : QuadraticResidualData (𝕜 := ℝ) originalF
  columns : ∀ (p v : NativeAmbient) (r : Fin 2184),
    algebra.linear p v r = ∑ c : Fin 1053,
      v c * MvPolynomial.eval p
        (MvPolynomial.pderiv c
          (NativePolynomial.ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r))

/-- A faithful conditional native consumer, for a real component of an H stress.
The anchor map must still be bound to one of the four actual12-state quartets. -/
theorem original_anchor_fixed_stress
    (D : OriginalQuadraticData) (x : NativeAmbient)
    (ell : NativeRows →ₗ[ℝ] ℝ) (anchor : NativeAmbient →ₗ[ℝ] (Fin 324 → ℝ))
    (b : (Fin 324 → ℝ) →ₗ[ℝ] (Fin 324 → ℝ) →ₗ[ℝ] ℝ)
    (hbase : ∀ v, ell (D.algebra.linear originalSeed v) = 0)
    (hsupport : ∀ u v,
      ell (D.algebra.bilinear u v) = b (anchor u) (anchor v))
    (hx : anchor x = 0) :
    ∀ v, ell (D.algebra.linear (originalSeed + x) v) = 0 :=
  anchor_fixed_stress D.algebra originalSeed x ell anchor b hbase hsupport hx

end Option2.NativeStress

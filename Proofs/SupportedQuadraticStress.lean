module

public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Module.Equiv.Basic

@[expose] public section

/-!
First-party conditional quadratic-stress criterion.
No native certificate, differentiability theorem, sheet or phase input is proved here.
The linear term must be identified with the derivative by its native consumer.
This is ordinary quadratic algebra, with no novelty claim or copied implementation.
-/

namespace Option2.NativeStress

variable {𝕜 E R A : Type*} [CommRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup R] [Module 𝕜 R]
  [AddCommGroup A] [Module 𝕜 A]

/-- The two exact quadratic identities needed at the native/analysis boundary. -/
structure QuadraticResidualData (F : E → R) where
  linear : E → E →ₗ[𝕜] R
  bilinear : E →ₗ[𝕜] E →ₗ[𝕜] R
  increment : ∀ p x, F (p + x) = F p + linear p x + bilinear x x
  affine : ∀ p x v,
    linear (p + x) v = linear p v + bilinear x v + bilinear v x

variable {F : E → R} (D : QuadraticResidualData (𝕜 := 𝕜) F)

/-- Full ambient bilinear support, together with base annihilation, gives an
exact stress on every anchor-fixed translate. Neither input can be dropped. -/
theorem anchor_fixed_stress
    (p x : E) (ell : R →ₗ[𝕜] 𝕜) (anchor : E →ₗ[𝕜] A)
    (b : A →ₗ[𝕜] A →ₗ[𝕜] 𝕜)
    (hbase : ∀ v, ell (D.linear p v) = 0)
    (hsupport : ∀ u v, ell (D.bilinear u v) = b (anchor u) (anchor v))
    (hx : anchor x = 0) :
    ∀ v, ell (D.linear (p + x) v) = 0 := by
  intro v
  simp only [D.affine, map_add, hbase, hsupport, hx, map_zero,
    LinearMap.zero_apply, zero_add, add_zero]

/-- Transport uses an actual derivative intertwiner on the full row space.
A phase-dependent row twist without this identity does not meet this hypothesis. -/
theorem transported_stress
    (g : E ≃ₗ[𝕜] E) (rho : R ≃ₗ[𝕜] R)
    (hcov : ∀ x v, D.linear (g x) (g v) = rho (D.linear x v))
    (x : E) (ell : R →ₗ[𝕜] 𝕜)
    (hstress : ∀ v, ell (D.linear x v) = 0) :
    ∀ v, ell (rho.symm (D.linear (g x) v)) = 0 := by
  intro v
  have h := congrArg (fun y => ell (rho.symm y)) (hcov x (g.symm v))
  simpa only [g.apply_symm_apply, rho.symm_apply_apply, hstress] using h

/-- The scalar equation has an exact quadratic remainder at a stressed point. -/
theorem paired_increment
    (s x : E) (ell : R →ₗ[𝕜] 𝕜)
    (hstress : ∀ v, ell (D.linear s v) = 0) :
    ell (F (s + x)) = ell (F s) + ell (D.bilinear x x) := by
  have h := congrArg ell (D.increment s x)
  simpa only [map_add, hstress, add_zero] using h

end Option2.NativeStress

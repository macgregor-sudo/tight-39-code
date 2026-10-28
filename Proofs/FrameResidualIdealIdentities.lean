module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Tactic.Ring

/-
# Generic frame-residual identities

Exact first-party source: post1700/sol-jet-certificate/
FrameResidualIdealIdentities.lean, SHA256
2233177f67ebbeb44a69682ccbe74242d745b204cd0f1785ff31379f5c8cbccd.
Its entire FrameResiduals namespace body is byte-identical to the body in
the source assembly 2ac2d694cf42c0223c2132326c17192f3267a9e5286b3c9e4206e278f6af77d7.

Packaging only: replace PolynomialTerminalInputs by the three existing
mathlib API owners below; add explicit module/public/expose visibility.
This module defines the FrameResiduals declarations. A combined source
containing those same declarations must not be imported alongside it.
Actual native coordinate-product and full F/G row instantiation stay separate.

Imported API source: https://github.com/leanprover-community/mathlib4,
commit 065356127b1dc0016f66b7283ce0ce2c4055aa55, Apache-2.0.
No upstream implementation is copied; original import provenance/thanks and
the original mathematical-scope comments are retained verbatim below.
-/


@[expose] public section

/-
First-party proof scripts; no upstream implementation is copied or adapted.
The elementary bilinear expansion below is the F/G residual identity already
derived in post1700/sol-jet-certificate.md §3 and incoming/certificate-review.md
§4. It needs no associativity or Jordan identity and makes no novelty claim.

Imports reuse the admitted mathlib closure at commit
065356127b1dc0016f66b7283ce0ce2c4055aa55, Lean v4.35.0-rc2.
Imported APIs: Mathlib/LinearAlgebra/Pi.lean ::
LinearMap.pi_apply_eq_sum_univ; Mathlib/RingTheory/Ideal/Defs.lean ::
Ideal.unit_mul_mem_iff_mem; Mathlib/Tactic/Ring.lean :: ring.
Upstream source headers and Apache-2.0 license are preserved by the existing
dependency/provenance ledger. These are imports, not copied source bodies.
Thank you to the Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/


/-!
# Frame residual identities and their coordinate-ideal consequences

The intended scalar ring P is an actual polynomial ring. A product B is a
P-bilinear map on finite coordinate vectors, symmetric and with unit e.
We prove the concrete algebraic steps for both F/G ideal inclusions, without
assuming either inclusion or equality. The trace is an actual P-linear map.

This is a generic identity prototype. The old first-party Python checker has
literal 2184/3159 native residual families, but the Lean native Albert carrier
is specialized to real scalars. Its polynomial B/trace, literal variables and
residual-index bindings must still be instantiated. No native tensor identity,
coordinate transport, data certificate or concrete ideal equality is claimed.
-/

namespace FrameResiduals

open scoped BigOperators

variable {P κ : Type*} [CommRing P]

/-- The literal point-idempotency residual. -/
def idempotencyResidual (B : (κ → P) →ₗ[P] (κ → P) →ₗ[P] (κ → P))
    (p : κ → P) : κ → P := B p p - p

/-- The literal sum residual of one ordered frame. -/
def frameSumResidual (e p q r : κ → P) : κ → P := p + q + r - e

/-- Exact expansion producing a within-frame product from idempotency and
frame-sum residuals. No division, associativity or Jordan axiom is used. -/
theorem twice_product_eq_residuals
    (B : (κ → P) →ₗ[P] (κ → P) →ₗ[P] (κ → P)) (e : κ → P)
    (hComm : ∀ x y, B x y = B y x) (hUnit : ∀ x, B e x = x)
    (p q r : κ → P) :
    (2 : P) • B p q =
      idempotencyResidual B r - idempotencyResidual B p - idempotencyResidual B q -
        B (e - (2 : P) • p - (2 : P) • q) (frameSumResidual e p q r) -
        B (frameSumResidual e p q r) (frameSumResidual e p q r) := by
  have hRightUnit (x : κ → P) : B x e = x := (hComm x e).trans (hUnit x)
  funext j
  simp only [idempotencyResidual, frameSumResidual, map_sub, map_add, map_smul,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    hUnit, hRightUnit, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hComm q p, hComm r p, hComm r q]
  ring

section CoordinateIdeal

variable [Fintype κ]

/-- Finite-coordinate linear combinations preserve a scalar ideal. This is
applied to actual product-coordinate maps and to the trace. -/
theorem linearMap_mem_of_coordinates (I : Ideal P) (L : (κ → P) →ₗ[P] P)
    (x : κ → P) (hx : ∀ j, x j ∈ I) : L x ∈ I := by
  classical
  rw [LinearMap.pi_apply_eq_sum_univ L x]
  apply I.sum_mem
  intro j _
  change x j * L (fun k => if j = k then 1 else 0) ∈ I
  exact I.mul_mem_right _ (hx j)

/-- Multiplication by an arbitrary coordinate vector preserves coordinatewise
membership in a scalar ideal because the actual second slot is linear. -/
theorem product_mem_of_coordinates (I : Ideal P)
    (B : (κ → P) →ₗ[P] (κ → P) →ₗ[P] (κ → P))
    (v x : κ → P) (hx : ∀ j, x j ∈ I) : ∀ j, B v x j ∈ I := by
  intro j
  exact linearMap_mem_of_coordinates I ((LinearMap.proj j).comp (B v)) x hx

/-- The G within-frame vector residual follows from the F idempotency and
frame-sum generators. The unit hypothesis is needed only to divide by two. -/
theorem product_mem_of_frame_residuals (I : Ideal P)
    (B : (κ → P) →ₗ[P] (κ → P) →ₗ[P] (κ → P)) (e : κ → P)
    (hComm : ∀ x y, B x y = B y x) (hUnit : ∀ x, B e x = x)
    (hTwo : IsUnit (2 : P)) (p q r : κ → P)
    (hp : ∀ j, idempotencyResidual B p j ∈ I)
    (hq : ∀ j, idempotencyResidual B q j ∈ I)
    (hr : ∀ j, idempotencyResidual B r j ∈ I)
    (hSum : ∀ j, frameSumResidual e p q r j ∈ I) :
    ∀ j, B p q j ∈ I := by
  have hFirst := product_mem_of_coordinates I B
    (e - (2 : P) • p - (2 : P) • q) (frameSumResidual e p q r) hSum
  have hSecond := product_mem_of_coordinates I B
    (frameSumResidual e p q r) (frameSumResidual e p q r) hSum
  intro j
  apply (I.unit_mul_mem_iff_mem hTwo).mp
  change ((2 : P) • B p q) j ∈ I
  rw [twice_product_eq_residuals B e hComm hUnit p q r]
  exact I.sub_mem (I.sub_mem (I.sub_mem (I.sub_mem (hr j) (hp j)) (hq j))
    (hFirst j)) (hSecond j)

/-- Applying the actual trace to a G vector-product generator gives its F
scalar within-frame overlap; no trace positivity is needed. -/
theorem trace_product_mem_of_coordinates (I : Ideal P)
    (tr : (κ → P) →ₗ[P] P)
    (B : (κ → P) →ₗ[P] (κ → P) →ₗ[P] (κ → P))
    (p q : κ → P) (hProduct : ∀ j, B p q j ∈ I) : tr (B p q) ∈ I :=
  linearMap_mem_of_coordinates I tr (B p q) hProduct

/-- Exact trace recovery using another frame. The scalar third need only
satisfy 3*third=1, including over a general polynomial coefficient ring. -/
theorem trace_residual_eq_cross_and_sum
    (tr : (κ → P) →ₗ[P] P)
    (B : (κ → P) →ₗ[P] (κ → P) →ₗ[P] (κ → P)) (e : κ → P)
    (hRightUnit : ∀ x, B x e = x)
    (third : P) (hThird : (3 : P) * third = 1)
    (p q₀ q₁ q₂ : κ → P) :
    tr p - 1 =
      (tr (B p q₀) - third) + (tr (B p q₁) - third) +
        (tr (B p q₂) - third) - tr (B p (frameSumResidual e q₀ q₁ q₂)) := by
  simp only [frameSumResidual, map_sub, map_add, hRightUnit]
  calc
    tr p - 1 = tr p - (3 : P) * third := by rw [hThird]
    _ = _ := by ring

/-- The F trace residual belongs to the G ideal using actual cross-overlap
residuals and the sum residual of an actual other frame. -/
theorem trace_mem_of_other_frame_residuals (I : Ideal P)
    (tr : (κ → P) →ₗ[P] P)
    (B : (κ → P) →ₗ[P] (κ → P) →ₗ[P] (κ → P)) (e : κ → P)
    (hRightUnit : ∀ x, B x e = x)
    (third : P) (hThird : (3 : P) * third = 1)
    (p q₀ q₁ q₂ : κ → P)
    (h₀ : tr (B p q₀) - third ∈ I)
    (h₁ : tr (B p q₁) - third ∈ I)
    (h₂ : tr (B p q₂) - third ∈ I)
    (hSum : ∀ j, frameSumResidual e q₀ q₁ q₂ j ∈ I) : tr p - 1 ∈ I := by
  have hCorrection : tr (B p (frameSumResidual e q₀ q₁ q₂)) ∈ I :=
    linearMap_mem_of_coordinates I (tr.comp (B p)) _ hSum
  rw [trace_residual_eq_cross_and_sum tr B e hRightUnit third hThird p q₀ q₁ q₂]
  exact I.sub_mem (I.add_mem (I.add_mem h₀ h₁) h₂) hCorrection

end CoordinateIdeal

end FrameResiduals

/- Existing nine type/seven theorem reports, plus the two definition reports. -/


#check @FrameResiduals.idempotencyResidual
#check @FrameResiduals.frameSumResidual
#check @FrameResiduals.twice_product_eq_residuals
#check @FrameResiduals.linearMap_mem_of_coordinates
#check @FrameResiduals.product_mem_of_coordinates
#check @FrameResiduals.product_mem_of_frame_residuals
#check @FrameResiduals.trace_product_mem_of_coordinates
#check @FrameResiduals.trace_residual_eq_cross_and_sum
#check @FrameResiduals.trace_mem_of_other_frame_residuals

#print axioms FrameResiduals.twice_product_eq_residuals
#print axioms FrameResiduals.linearMap_mem_of_coordinates
#print axioms FrameResiduals.product_mem_of_coordinates
#print axioms FrameResiduals.product_mem_of_frame_residuals
#print axioms FrameResiduals.trace_product_mem_of_coordinates
#print axioms FrameResiduals.trace_residual_eq_cross_and_sum
#print axioms FrameResiduals.trace_mem_of_other_frame_residuals

#print axioms FrameResiduals.idempotencyResidual
#print axioms FrameResiduals.frameSumResidual

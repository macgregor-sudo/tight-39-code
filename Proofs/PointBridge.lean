module

public import NativeExactCKMAllF

/-!
# Point bridge, part P1: the accepted real CKM point, complexified

The accepted real theorems `ExactCKMAllF.all_fRow_eval_zero` and
`ExactCKMAllG.all_gRow_eval_zero` are transported to the complex point
`P v = ((pointCoordinates v : ℝ) : ℂ)` through one generic lemma: the
coefficient map along any ring hom `f` sends the literal F/G rows at `(h, t)`
to the literal rows at `(f h, f t)`. No row is re-expanded.

First-party composition of accepted project definitions and Mathlib API
(`MvPolynomial.eval_map`, `MvPolynomial.eval₂_comp`); no borrowed proof text.
-/

@[expose] public section
noncomputable section

namespace FourSheets.PointBridge

open MvPolynomial
open NativePolynomial.CoordinateMaps FrameResiduals ConfigurationResidualIndices
open QuadraticCertificate.ExactCKMConfiguration

namespace Rows
open NativePolynomial.ConfigurationResiduals

variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_point (f : R →+* S) (i : Fin 39) (k : Fin 27) :
    map f (point (R := R) i k) = point i k := by
  simp only [point, map_X]

theorem map_coordinateProduct (f : R →+* S) (h : R)
    (x y : Fin 27 → MvPolynomial (Fin 1053) R) (k : Fin 27) :
    map f (coordinateProduct (C h) x y k) =
      coordinateProduct (C (f h)) (fun i => map f (x i)) (fun j => map f (y j)) k := by
  simp only [coordinateProduct_apply, map_sum, map_mul, map_C, map_intCast]

theorem map_coordinatePairing (f : R →+* S)
    (x y : Fin 27 → MvPolynomial (Fin 1053) R) :
    map f (coordinatePairing x y) =
      coordinatePairing (fun i => map f (x i)) (fun j => map f (y j)) := by
  simp only [coordinatePairing, map_sum, map_mul, map_intCast]

theorem map_coordinateUnit (f : R →+* S) (k : Fin 27) :
    map f (coordinateUnit (P := MvPolynomial (Fin 1053) R) k) = coordinateUnit k := by
  unfold coordinateUnit
  split_ifs <;> simp only [map_one, map_zero]

theorem map_coordinateTrace (f : R →+* S)
    (x : Fin 27 → MvPolynomial (Fin 1053) R) :
    map f (coordinateTrace x) = coordinateTrace (fun i => map f (x i)) := by
  simp only [coordinateTrace_apply, map_add]

/-- The coefficient map sends every literal F residual at `(h,t)` to the one at `(f h, f t)`. -/
theorem map_fResidual (f : R →+* S) (h t : R) (q : FLabel) :
    map f (fResidual h t q) = fResidual (f h) (f t) q := by
  rcases q with ⟨i, k⟩ | i | ⟨g, k⟩ | ij
  · simp only [fResidual, idempotencyResidual, Pi.sub_apply, map_sub,
      map_coordinateProduct, map_point]
  · simp only [fResidual, map_sub, map_one, map_coordinateTrace, map_point]
  · simp only [fResidual, map_sub, map_sum, map_point, map_coordinateUnit]
  · simp only [fResidual, map_sub, map_coordinatePairing, map_point]
    split_ifs <;> simp only [map_zero, map_C]

theorem map_gResidual (f : R →+* S) (h t : R) (q : GLabel) :
    map f (gResidual h t q) = gResidual (f h) (f t) q := by
  rcases q with ⟨i, k⟩ | ⟨⟨g, s⟩, k⟩ | ⟨g, k⟩ | ⟨fg, a, b⟩
  · simp only [gResidual, idempotencyResidual, Pi.sub_apply, map_sub,
      map_coordinateProduct, map_point]
  · simp only [gResidual, map_coordinateProduct, map_point]
  · simp only [gResidual, map_sub, map_sum, map_point, map_coordinateUnit]
  · simp only [gResidual, map_sub, map_coordinatePairing, map_point, map_C]

theorem map_fRow (f : R →+* S) (h t : R) (r : Fin 2184) :
    map f (fRow h t r) = fRow (f h) (f t) r :=
  map_fResidual f h t _

theorem map_gRow (f : R →+* S) (h t : R) (r : Fin 3159) :
    map f (gRow h t r) = gRow (f h) (f t) r :=
  map_gResidual f h t _

end Rows

/-- The accepted exact real point, complexified, in the original 1053 variables. -/
def P : Fin 1053 → ℂ := fun v => ((pointCoordinates v : ℝ) : ℂ)

private theorem half_complex : (1/2 : ℂ) = Complex.ofRealHom (1/2 : ℝ) := by
  simp
private theorem third_complex : (1/3 : ℂ) = Complex.ofRealHom (1/3 : ℝ) := by
  simp

/-- Complex evaluation of a real-coefficient polynomial at `P` is the cast of the real value. -/
theorem eval_P_map (p : MvPolynomial (Fin 1053) ℝ) :
    eval P (map Complex.ofRealHom p) = ((eval pointCoordinates p : ℝ) : ℂ) := by
  rw [eval_map]
  exact (eval₂_comp Complex.ofRealHom pointCoordinates p).symm

/-- P1: every original F row vanishes at the complexified point over ℂ. -/
theorem hPoint (r : Fin 2184) :
    eval P (NativePolynomial.ConfigurationResiduals.fRow (1/2 : ℂ) (1/3 : ℂ) r) = 0 := by
  rw [half_complex, third_complex, ← Rows.map_fRow, eval_P_map,
    QuadraticCertificate.ExactCKMAllF.all_fRow_eval_zero r, Complex.ofReal_zero]

/-- P1 with the consumer's literal lambda (definitionally the same point). -/
theorem hPoint_lambda (r : Fin 2184) :
    eval (fun v => ((pointCoordinates v : ℝ) : ℂ))
      (NativePolynomial.ConfigurationResiduals.fRow (1/2 : ℂ) (1/3 : ℂ) r) = 0 :=
  hPoint r

/-- The same for every original G row. -/
theorem hPointG (r : Fin 3159) :
    eval P (NativePolynomial.ConfigurationResiduals.gRow (1/2 : ℂ) (1/3 : ℂ) r) = 0 := by
  rw [half_complex, third_complex, ← Rows.map_gRow, eval_P_map,
    QuadraticCertificate.ExactCKMAllG.all_gRow_eval_zero r, Complex.ofReal_zero]

/-- P4 (first control): no F row evaluates to one at P. -/
theorem hPoint_ne_one (r : Fin 2184) :
    eval P (NativePolynomial.ConfigurationResiduals.fRow (1/2 : ℂ) (1/3 : ℂ) r) ≠ 1 := by
  rw [hPoint r]; exact zero_ne_one

end FourSheets.PointBridge

#print axioms FourSheets.PointBridge.Rows.map_fRow
#print axioms FourSheets.PointBridge.Rows.map_gRow
#print axioms FourSheets.PointBridge.hPoint
#print axioms FourSheets.PointBridge.hPoint_lambda
#print axioms FourSheets.PointBridge.hPointG
#print axioms FourSheets.PointBridge.hPoint_ne_one

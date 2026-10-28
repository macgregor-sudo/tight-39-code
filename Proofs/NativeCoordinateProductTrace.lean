module

public import NativeIntegralUnitTraceContractions

@[expose] public section

/-!
# Coordinate product, unit and trace from the actual integer numerator

These are maps on the ordinary module Fin27 -> P for a commutative ring P.
No Albert carrier, algebra typeclass or Jordan identity over P is introduced.
The product is the finite contraction h*N, with P-bilinearity proved directly.
The accepted integer contractions supply its unit and trace laws;2*h=1 enters
only at the normalized corollaries. Polynomial compatibility identifies this
formula with the unchanged tensorPolynomial, then the accepted real/native
evaluation theorem supplies actual native semantics.

This is classical finite bilinearity and coordinate arithmetic, with no novelty
claim. The native source is imported, not copied, from
https://github.com/macgregor-sudo/compact-albert-recognition, commit
40d3b344180d9ddb78aaa2876873377c1e631515. Existing Apache-2.0 notices and prior
law extraction remain at THIRD_PARTY_NOTICES.md#native-albert-code. The tensor/evaluation
API is the first-party NativePolynomialEvaluationStaged; imported Mathlib APIs
are pinned at065356127b1dc0016f66b7283ce0ce2c4055aa55. No upstream proof body
is copied here and no outbound license is chosen. Full F/G rows, ideal equality
and certificate/data binding remain separate.
Thanks to the native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace NativePolynomial.CoordinateMaps

open scoped BigOperators
open IntegralStructureConstants MvPolynomial

variable {P : Type*} [CommRing P]

/-- The literal finite contraction as a curried P-bilinear map. -/
def coordinateProduct (h : P) :
    (Fin 27 → P) →ₗ[P] (Fin 27 → P) →ₗ[P] (Fin 27 → P) where
  toFun x :=
    { toFun := fun y k => ∑ i, ∑ j, x i * y j * (h * (numerator i j k : P))
      map_add' y z := by
        funext k
        simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
      map_smul' r y := by
        funext k
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    funext k
    change (∑ i, ∑ j, (x i + z i) * y j * (h * (numerator i j k : P))) =
      (∑ i, ∑ j, x i * y j * (h * (numerator i j k : P))) +
        (∑ i, ∑ j, z i * y j * (h * (numerator i j k : P)))
    simp only [Pi.add_apply, LinearMap.add_apply, mul_add, add_mul,
      Finset.sum_add_distrib]
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    funext k
    change (∑ i, ∑ j, (r * x i) * y j * (h * (numerator i j k : P))) =
      r * (∑ i, ∑ j, x i * y j * (h * (numerator i j k : P)))
    simp only [RingHom.id_apply, Pi.smul_apply, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem coordinateProduct_apply (h : P) (x y : Fin 27 → P) (k : Fin 27) :
    coordinateProduct h x y k =
      ∑ i, ∑ j, x i * y j * (h * (numerator i j k : P)) := rfl

/-- The original unit has its first three coordinates1 and all others0. -/
def coordinateUnit : Fin 27 → P := fun k => if k.val < 3 then 1 else 0

/-- Trace is the sum of the three diagonal coordinate projections. -/
def coordinateTrace : (Fin 27 → P) →ₗ[P] P where
  toFun x := ∑ r : Fin 3, x (diagonalCoordinateIndex r)
  map_add' x y := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem coordinateTrace_apply (x : Fin 27 → P) :
    coordinateTrace x = x 0 + x 1 + x 2 := by
  change (∑ r : Fin 3, x (diagonalCoordinateIndex r)) = _
  rw [Fin.sum_univ_three]
  rfl

/-- The integer weights are1 on diagonal coordinates and2 on upper ones. -/
def coordinatePairing (x y : Fin 27 → P) : P :=
  ∑ i, (coordinateTraceWeight i : P) * x i * y i

theorem coordinateProduct_comm (h : P) (x y : Fin 27 → P) :
    coordinateProduct h x y = coordinateProduct h y x := by
  funext k
  simp only [coordinateProduct_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [numerator_comm j i k]
  ring

private theorem unit_eq_sum :
    coordinateUnit (P := P) =
      ∑ r : Fin 3, (fun k : Fin 27 => if k = diagonalCoordinateIndex r then 1 else 0) := by
  rw [Fin.sum_univ_three]
  funext k
  fin_cases k <;>
    norm_num [coordinateUnit, diagonalCoordinateIndex]

private theorem coordinateProduct_basis_left (h : P) (d k : Fin 27)
    (x : Fin 27 → P) :
    coordinateProduct h (fun i => if i = d then 1 else 0) x k =
      ∑ j, x j * (h * (numerator d j k : P)) := by
  classical
  simp [coordinateProduct_apply, ite_mul, mul_ite]

private theorem coordinateProduct_unit_left_factor (h : P) (x : Fin 27 → P) :
    coordinateProduct h coordinateUnit x = ((2 : P) * h) • x := by
  classical
  rw [unit_eq_sum]
  funext k
  simp only [map_sum, LinearMap.sum_apply, Finset.sum_apply,
    coordinateProduct_basis_left, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  have hCoefficients (j : Fin 27) :
      (∑ r : Fin 3, (numerator (diagonalCoordinateIndex r) j k : P)) =
        if k = j then 2 else 0 := by
    simpa using congrArg (Int.castRingHom P) (numerator_unit_contraction j k)
  calc
    _ = ∑ j, x j * h * (∑ r : Fin 3, (numerator (diagonalCoordinateIndex r) j k : P)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = x k * h * 2 := by simp [hCoefficients, mul_ite, ite_mul]
    _ = _ := by ring

theorem coordinateProduct_unit_left (h : P) (hHalf : (2 : P) * h = 1)
    (x : Fin 27 → P) : coordinateProduct h coordinateUnit x = x := by
  rw [coordinateProduct_unit_left_factor, hHalf, one_smul]

theorem coordinateProduct_unit_right (h : P) (hHalf : (2 : P) * h = 1)
    (x : Fin 27 → P) : coordinateProduct h x coordinateUnit = x := by
  rw [coordinateProduct_comm, coordinateProduct_unit_left h hHalf]

private theorem coordinateTrace_product_factor (h : P) (x y : Fin 27 → P) :
    coordinateTrace (coordinateProduct h x y) =
      ((2 : P) * h) * coordinatePairing x y := by
  classical
  change (∑ r : Fin 3, coordinateProduct h x y (diagonalCoordinateIndex r)) = _
  simp only [coordinateProduct_apply]
  rw [Finset.sum_comm]
  have hCoefficients (i j : Fin 27) :
      (∑ r : Fin 3, (numerator i j (diagonalCoordinateIndex r) : P)) =
        if i = j then 2 * (coordinateTraceWeight i : P) else 0 := by
    simpa using congrArg (Int.castRingHom P) (numerator_trace_contraction i j)
  calc
    _ = ∑ i, ∑ j, ∑ r : Fin 3,
        x i * y j * (h * (numerator i j (diagonalCoordinateIndex r) : P)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, x i * y j * h *
        (∑ r : Fin 3, (numerator i j (diagonalCoordinateIndex r) : P)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = ∑ i, x i * y i * h * (2 * (coordinateTraceWeight i : P)) := by
      simp [hCoefficients, mul_ite, ite_mul]
    _ = _ := by
      unfold coordinatePairing
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem coordinateTrace_product (h : P) (hHalf : (2 : P) * h = 1)
    (x y : Fin 27 → P) :
    coordinateTrace (coordinateProduct h x y) = coordinatePairing x y := by
  rw [coordinateTrace_product_factor, hHalf, one_mul]

theorem coordinate_two_isUnit (h : P) (hHalf : (2 : P) * h = 1) : IsUnit (2 : P) := by
  refine ⟨⟨2, h, hHalf, ?_⟩, rfl⟩
  simpa only [mul_comm] using hHalf

variable {σ R : Type*} [CommRing R]

/-- The polynomial specialization is the unchanged tensor formula for every h. -/
theorem coordinateProduct_polynomial_apply (h : R)
    (x y : Fin 27 → MvPolynomial σ R) (k : Fin 27) :
    coordinateProduct (C h) x y k =
      tensorPolynomial (fun i j k => h * (numerator i j k : R)) x y k := by
  simp only [coordinateProduct_apply, tensorPolynomial, map_mul, map_intCast]

/-- The real polynomial specialization agrees with the actual native tensor. -/
theorem coordinateProduct_polynomial_real (h : ℝ) (hHalf : (2 : ℝ) * h = 1)
    (x y : Fin 27 → MvPolynomial σ ℝ) :
    coordinateProduct (C h) x y = tensorPolynomial nativeStructureConstant x y := by
  have hCoefficients :
      (fun i j k => h * (numerator i j k : ℝ)) = nativeStructureConstant := by
    funext i j k
    rw [numerator_cast_eq_two_nativeStructureConstant]
    calc
      _ = (2 * h) * nativeStructureConstant i j k := by ring
      _ = _ := by rw [hHalf, one_mul]
  funext k
  rw [coordinateProduct_polynomial_apply, hCoefficients]

/-- The general trace uses exactly the already passed real polynomial trace. -/
theorem coordinateTrace_polynomial_real (x : Fin 27 → MvPolynomial σ ℝ) :
    coordinateTrace x = tracePolynomial x := by
  rw [coordinateTrace_apply]
  rfl

/-- Actual native evaluation, without any native carrier over a new ring. -/
theorem evaluate_coordinateProduct_real (h : ℝ) (hHalf : (2 : ℝ) * h = 1)
    (a : σ → ℝ) (x y : Fin 27 → MvPolynomial σ ℝ) :
    evaluateNative a (coordinateProduct (C h) x y) =
      Glennie.jordan (evaluateNative a x) (evaluateNative a y) := by
  rw [coordinateProduct_polynomial_real h hHalf, evaluateNative_tensorPolynomial]

end NativePolynomial.CoordinateMaps



#check @NativePolynomial.CoordinateMaps.coordinateProduct
#check @NativePolynomial.CoordinateMaps.coordinateProduct_apply
#check @NativePolynomial.CoordinateMaps.coordinateUnit
#check @NativePolynomial.CoordinateMaps.coordinateTrace
#check @NativePolynomial.CoordinateMaps.coordinateTrace_apply
#check @NativePolynomial.CoordinateMaps.coordinatePairing
#check @NativePolynomial.CoordinateMaps.coordinateProduct_comm
#check @NativePolynomial.CoordinateMaps.coordinateProduct_unit_left
#check @NativePolynomial.CoordinateMaps.coordinateProduct_unit_right
#check @NativePolynomial.CoordinateMaps.coordinateTrace_product
#check @NativePolynomial.CoordinateMaps.coordinate_two_isUnit
#check @NativePolynomial.CoordinateMaps.coordinateProduct_polynomial_apply
#check @NativePolynomial.CoordinateMaps.coordinateProduct_polynomial_real
#check @NativePolynomial.CoordinateMaps.coordinateTrace_polynomial_real
#check @NativePolynomial.CoordinateMaps.evaluate_coordinateProduct_real

#print axioms NativePolynomial.CoordinateMaps.coordinateProduct
#print axioms NativePolynomial.CoordinateMaps.coordinateProduct_apply
#print axioms NativePolynomial.CoordinateMaps.coordinateUnit
#print axioms NativePolynomial.CoordinateMaps.coordinateTrace
#print axioms NativePolynomial.CoordinateMaps.coordinateTrace_apply
#print axioms NativePolynomial.CoordinateMaps.coordinatePairing
#print axioms NativePolynomial.CoordinateMaps.coordinateProduct_comm
#print axioms NativePolynomial.CoordinateMaps.coordinateProduct_unit_left
#print axioms NativePolynomial.CoordinateMaps.coordinateProduct_unit_right
#print axioms NativePolynomial.CoordinateMaps.coordinateTrace_product
#print axioms NativePolynomial.CoordinateMaps.coordinate_two_isUnit
#print axioms NativePolynomial.CoordinateMaps.coordinateProduct_polynomial_apply
#print axioms NativePolynomial.CoordinateMaps.coordinateProduct_polynomial_real
#print axioms NativePolynomial.CoordinateMaps.coordinateTrace_polynomial_real
#print axioms NativePolynomial.CoordinateMaps.evaluate_coordinateProduct_real

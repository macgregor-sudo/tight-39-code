module

public import NativeTrialityPeirce

/-!
# Every native Jordan derivation is trace-free, skew and kills the unit

For every real Jordan derivation `D` of the actual native Albert algebra (MASTER §6.6, first paragraph):

* `tr (D x) = 0`: the coordinate trace of Jordan left multiplication is `Tr_{End J} L_x = 9 tr x`, and
  `[D, L_x] = L_{D x}` has trace zero;
* `⟨D x, y⟩ + ⟨x, D y⟩ = 0` for the positive native trace pairing `Glennie.inner x y = tr (x ∘ y)`
  (positivity: the native `Glennie.inner_self_nonneg`, `Glennie.inner_self_eq_zero`);
* `D 1 = 0`.

No trace-free hypothesis is assumed anywhere; this supplies it.
-/

@[expose] public section

noncomputable section

namespace CKM.NativeDerivationTriality

open Glennie Reuse

/-! ## Coordinate basis and the diagonal of `L_x`

Adapted from `RealOrbitSlice/Native/AlgebraTrace.lean` (`nativeProductDiagonal`,
`nativeProduct_single_apply_self`, `trace_nativeProduct`) of
the original first-party real orbit-slice implementation, rewritten
directly on `Glennie.Albert` with the basis transported along the native
`NativePolynomial.upperCoordinateEquiv`. -/

/-- The native coordinate basis of `Albert`, transported from the standard basis of `Fin 27 → ℝ`. -/
def upperBasis : Module.Basis (Fin 27) ℝ Albert :=
  (Pi.basisFun ℝ (Fin 27)).map NativePolynomial.upperCoordinateEquiv.symm

/-- The diagonal entries of the matrix of `L_x` in `upperBasis`: `x_i` on the diagonal coordinates, and
`(x_i + x_j)/2` on each real coordinate of the octonion slot `ij`. -/
def jordanDiagonal (x : Albert) : Fin 27 → ℝ :=
  ![x.d0, x.d1, x.d2,
    (x.d0 + x.d1) / 2, (x.d0 + x.d1) / 2, (x.d0 + x.d1) / 2, (x.d0 + x.d1) / 2,
    (x.d0 + x.d1) / 2, (x.d0 + x.d1) / 2, (x.d0 + x.d1) / 2, (x.d0 + x.d1) / 2,
    (x.d0 + x.d2) / 2, (x.d0 + x.d2) / 2, (x.d0 + x.d2) / 2, (x.d0 + x.d2) / 2,
    (x.d0 + x.d2) / 2, (x.d0 + x.d2) / 2, (x.d0 + x.d2) / 2, (x.d0 + x.d2) / 2,
    (x.d1 + x.d2) / 2, (x.d1 + x.d2) / 2, (x.d1 + x.d2) / 2, (x.d1 + x.d2) / 2,
    (x.d1 + x.d2) / 2, (x.d1 + x.d2) / 2, (x.d1 + x.d2) / 2, (x.d1 + x.d2) / 2]

theorem jordan_single_apply_self (x : Albert) (k : Fin 27) :
    NativePolynomial.upperCoordinates
        (jordan x (NativePolynomial.fromUpperCoordinates (Pi.single k 1))) k =
      jordanDiagonal x k := by
  fin_cases k
  all_goals
    simp only [NativePolynomial.upperCoordinates, jordanDiagonal, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    simp [NativePolynomial.fromUpperCoordinates, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12, octDot_coordinates, octMul, octConj]
  all_goals ring

/-- The coordinate trace of native Jordan left multiplication: `Tr L_x = 9 tr x`. -/
theorem trace_jordanLinear (x : Albert) : LinearMap.trace ℝ Albert (jordanLinear x) = 9 * Glennie.trace x := by
  rw [LinearMap.trace_eq_matrix_trace ℝ upperBasis]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, upperBasis, Module.Basis.map_apply,
    Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm, Pi.basisFun_apply,
    Pi.basisFun_repr, jordanLinear_apply]
  change ∑ k, NativePolynomial.upperCoordinates
      (jordan x (NativePolynomial.fromUpperCoordinates (Pi.single k 1))) k = _
  simp only [jordan_single_apply_self, jordanDiagonal, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  simp only [Glennie.trace]
  ring

theorem derivation_map_one {D : Module.End ℝ Albert} (hD : IsJordanDerivation D) : D 1 = 0 := by
  exact hD.map_one

theorem derivation_trace_eq_zero {D : Module.End ℝ Albert} (hD : IsJordanDerivation D) (x : Albert) :
    Glennie.trace (D x) = 0 := by
  have hcomm : D * jordanLinear x - jordanLinear x * D = jordanLinear (D x) := by
    refine LinearMap.ext fun y => ?_
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, jordanLinear_apply,
      jordanLinear_apply, jordanLinear_apply, hD x y]
    abel
  have h := trace_jordanLinear (D x)
  rw [← hcomm, map_sub, LinearMap.trace_mul_comm ℝ D (jordanLinear x), sub_self] at h
  linarith

theorem derivation_inner_skew {D : Module.End ℝ Albert} (hD : IsJordanDerivation D) (x y : Albert) :
    Glennie.inner (D x) y + Glennie.inner x (D y) = 0 := by
  simp only [Glennie.inner]
  rw [← trace_add, ← hD x y]
  exact derivation_trace_eq_zero hD (jordan x y)

end CKM.NativeDerivationTriality

#print axioms CKM.NativeDerivationTriality.jordan_single_apply_self
#print axioms CKM.NativeDerivationTriality.trace_jordanLinear
#print axioms CKM.NativeDerivationTriality.derivation_map_one
#print axioms CKM.NativeDerivationTriality.derivation_trace_eq_zero
#print axioms CKM.NativeDerivationTriality.derivation_inner_skew

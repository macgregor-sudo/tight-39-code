module

public import A3PhaseTriples

@[expose] public section

/-!
# Native automorphisms: R0, the transports and R1
-/

noncomputable section

namespace CKM.NativeFirstOrder

open CompactAlbert

/-! ## Coordinate bridges (re-derived; `NativeCanonicalPartialPreservation` is not mirrored) -/

theorem alg_upper_jordan (x y : Glennie.Albert) :
    NativePolynomial.upperCoordinates (Glennie.jordan x y) =
      NativePolynomial.CoordinateMaps.coordinateProduct (1 / 2 : ℝ)
        (NativePolynomial.upperCoordinates x) (NativePolynomial.upperCoordinates y) := by
  funext k
  rw [NativePolynomial.CoordinateMaps.coordinateProduct_apply]
  conv_lhs => rw [← NativePolynomial.fromUpperCoordinates_upperCoordinates x,
    ← NativePolynomial.fromUpperCoordinates_upperCoordinates y]
  rw [NativePolynomial.upperCoordinates_jordan]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [NativePolynomial.IntegralStructureConstants.numerator_cast_eq_two_nativeStructureConstant]
  ring

theorem alg_upper_trace (x : Glennie.Albert) :
    NativePolynomial.CoordinateMaps.coordinateTrace (NativePolynomial.upperCoordinates x) =
      Glennie.trace x := by
  simp [NativePolynomial.CoordinateMaps.coordinateTrace_apply, NativePolynomial.upperCoordinates,
    Glennie.trace]

/-- A native map whose coordinate form is an accepted coordinate automorphism is native. -/
theorem isNativeAut_of_coordinates (g : Glennie.Albert →ₗ[ℝ] Glennie.Albert)
    (φ : (Fin 27 → ℝ) → (Fin 27 → ℝ)) (hφ : TitsS.IsAut (1 / 2 : ℝ) φ)
    (hg : ∀ x, NativePolynomial.upperCoordinates (g x) = φ (NativePolynomial.upperCoordinates x)) :
    IsNativeAut g where
  jordan x y := by
    apply NativePolynomial.upperCoordinateEquiv.injective
    change NativePolynomial.upperCoordinates _ = NativePolynomial.upperCoordinates _
    rw [hg, alg_upper_jordan, hφ.map_prod, alg_upper_jordan, hg, hg]
  trace x := by
    rw [← alg_upper_trace, hg, hφ.map_trace, alg_upper_trace]

theorem upper_signedTransport (p : Fin 27 → Fin 27) (s : Fin 27 → ℤ) (x : Glennie.Albert) :
    NativePolynomial.upperCoordinates (signedTransport p s x) =
      TitsS.sgnPerm p s (NativePolynomial.upperCoordinates x) := by
  funext k
  change NativePolynomial.upperCoordinateEquiv (NativePolynomial.upperCoordinateEquiv.symm _) k = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem signedTransport_comp_eq_id (p : Fin 27 → Fin 27) (s : Fin 27 → ℤ)
    (p' : Fin 27 → Fin 27) (s' : Fin 27 → ℤ) (h : ∀ k, s k * s' (p k) = 1 ∧ p' (p k) = k) :
    signedTransport p s ∘ₗ signedTransport p' s' = LinearMap.id := by
  ext1 x
  apply NativePolynomial.upperCoordinateEquiv.injective
  change NativePolynomial.upperCoordinates _ = NativePolynomial.upperCoordinates _
  rw [LinearMap.comp_apply, upper_signedTransport, upper_signedTransport, LinearMap.id_apply]
  funext k
  simp only [TitsS.sgnPerm]
  rw [(h k).2, ← mul_assoc, ← Int.cast_mul, (h k).1, Int.cast_one, one_mul]

theorem IsNativeAut.comp {f g : Glennie.Albert →ₗ[ℝ] Glennie.Albert} (hf : IsNativeAut f)
    (hg : IsNativeAut g) : IsNativeAut (f ∘ₗ g) where
  jordan x y := by simp only [LinearMap.comp_apply, hg.jordan, hf.jordan]
  trace x := by simp only [LinearMap.comp_apply, hf.trace, hg.trace]

theorem T1_inv_rel' : ∀ k, TitsS.Transport.T1si k * TitsS.Transport.T1s (TitsS.Transport.T1pinv k) = 1 ∧
    TitsS.Transport.T1p (TitsS.Transport.T1pinv k) = k := by decide
theorem T2_inv_rel' : ∀ k, TitsS.Transport.T2si k * TitsS.Transport.T2s (TitsS.Transport.T2pinv k) = 1 ∧
    TitsS.Transport.T2p (TitsS.Transport.T2pinv k) = k := by decide
theorem T3_inv_rel' : ∀ k, TitsS.Transport.T3si k * TitsS.Transport.T3s (TitsS.Transport.T3pinv k) = 1 ∧
    TitsS.Transport.T3p (TitsS.Transport.T3pinv k) = k := by decide

theorem omega_re : UnitaryErrorBases.ThreeCycleFourier.omega.re = -1 / 2 := by
  simp [UnitaryErrorBases.ThreeCycleFourier.omega]

theorem omega_im : UnitaryErrorBases.ThreeCycleFourier.omega.im = Real.sqrt 3 / 2 := by
  simp [UnitaryErrorBases.ThreeCycleFourier.omega]

/-- Coordinate form of right multiplication by a unit scalar of real part `-1/2` and imaginary
part `c` (`c = √3/2` gives `R0`, `c = -√3/2` gives `R0²`). -/
def rotc (c : ℝ) (v : Fin 27 → ℝ) : Fin 27 → ℝ :=
  ![v 0,
    v 1,
    v 2,
    v 3,
    v 4,
    -(v 5) / 2 + c * v 6,
    -(c * v 5) - v 6 / 2,
    -(v 7) / 2 + c * v 8,
    -(c * v 7) - v 8 / 2,
    -(v 9) / 2 - c * v 10,
    c * v 9 - v 10 / 2,
    v 11,
    v 12,
    -(v 13) / 2 + c * v 14,
    -(c * v 13) - v 14 / 2,
    -(v 15) / 2 + c * v 16,
    -(c * v 15) - v 16 / 2,
    -(v 17) / 2 - c * v 18,
    c * v 17 - v 18 / 2,
    v 19,
    v 20,
    -(v 21) / 2 + c * v 22,
    -(c * v 21) - v 22 / 2,
    -(v 23) / 2 + c * v 24,
    -(c * v 23) - v 24 / 2,
    -(v 25) / 2 - c * v 26,
    c * v 25 - v 26 / 2]

theorem upper_R0 (x : Glennie.Albert) :
    NativePolynomial.upperCoordinates (R0 x) =
      rotc (Real.sqrt 3 / 2) (NativePolynomial.upperCoordinates x) := by
  have hx : R0 x = fromTitsCoordinates ((toTitsCoordinates x).1, (toTitsCoordinates x).2.1,
      Matrix.of fun i j => (toTitsCoordinates x).2.2 i j * UnitaryErrorBases.ThreeCycleFourier.omega) := by
    change fromTitsCoordinates (titsRightMultiply _ (toTitsCoordinates x)) = _
    simp only [titsRightMultiply, LinearMap.coe_mk, AddHom.coe_mk]
    congr 3
    ext i j
    simp [mul_comm]
  rw [hx]
  funext k
  fin_cases k <;>
    simp [NativePolynomial.upperCoordinates, fromTitsCoordinates, toTitsCoordinates,
      octonionFromTitsRow, octonionToTitsRow, rotc, Glennie.octConj, omega_re, omega_im,
      Complex.mul_re, Complex.mul_im] <;> ring


/-! ## Literal transport tables (decided against the accepted data) -/

theorem T1p_at_0 : TitsS.Transport.T1p 0 = 0 := by decide
theorem T1p_at_1 : TitsS.Transport.T1p 1 = 1 := by decide
theorem T1p_at_2 : TitsS.Transport.T1p 2 = 2 := by decide
theorem T1p_at_3 : TitsS.Transport.T1p 3 = 5 := by decide
theorem T1p_at_4 : TitsS.Transport.T1p 4 = 6 := by decide
theorem T1p_at_5 : TitsS.Transport.T1p 5 = 3 := by decide
theorem T1p_at_6 : TitsS.Transport.T1p 6 = 4 := by decide
theorem T1p_at_7 : TitsS.Transport.T1p 7 = 9 := by decide
theorem T1p_at_8 : TitsS.Transport.T1p 8 = 10 := by decide
theorem T1p_at_9 : TitsS.Transport.T1p 9 = 7 := by decide
theorem T1p_at_10 : TitsS.Transport.T1p 10 = 8 := by decide
theorem T1p_at_11 : TitsS.Transport.T1p 11 = 15 := by decide
theorem T1p_at_12 : TitsS.Transport.T1p 12 = 16 := by decide
theorem T1p_at_13 : TitsS.Transport.T1p 13 = 17 := by decide
theorem T1p_at_14 : TitsS.Transport.T1p 14 = 18 := by decide
theorem T1p_at_15 : TitsS.Transport.T1p 15 = 11 := by decide
theorem T1p_at_16 : TitsS.Transport.T1p 16 = 12 := by decide
theorem T1p_at_17 : TitsS.Transport.T1p 17 = 13 := by decide
theorem T1p_at_18 : TitsS.Transport.T1p 18 = 14 := by decide
theorem T1p_at_19 : TitsS.Transport.T1p 19 = 25 := by decide
theorem T1p_at_20 : TitsS.Transport.T1p 20 = 26 := by decide
theorem T1p_at_21 : TitsS.Transport.T1p 21 = 23 := by decide
theorem T1p_at_22 : TitsS.Transport.T1p 22 = 24 := by decide
theorem T1p_at_23 : TitsS.Transport.T1p 23 = 21 := by decide
theorem T1p_at_24 : TitsS.Transport.T1p 24 = 22 := by decide
theorem T1p_at_25 : TitsS.Transport.T1p 25 = 19 := by decide
theorem T1p_at_26 : TitsS.Transport.T1p 26 = 20 := by decide
theorem T1s_at_0 : TitsS.Transport.T1s 0 = 1 := by decide
theorem T1s_at_1 : TitsS.Transport.T1s 1 = 1 := by decide
theorem T1s_at_2 : TitsS.Transport.T1s 2 = 1 := by decide
theorem T1s_at_3 : TitsS.Transport.T1s 3 = -1 := by decide
theorem T1s_at_4 : TitsS.Transport.T1s 4 = 1 := by decide
theorem T1s_at_5 : TitsS.Transport.T1s 5 = 1 := by decide
theorem T1s_at_6 : TitsS.Transport.T1s 6 = 1 := by decide
theorem T1s_at_7 : TitsS.Transport.T1s 7 = 1 := by decide
theorem T1s_at_8 : TitsS.Transport.T1s 8 = 1 := by decide
theorem T1s_at_9 : TitsS.Transport.T1s 9 = -1 := by decide
theorem T1s_at_10 : TitsS.Transport.T1s 10 = 1 := by decide
theorem T1s_at_11 : TitsS.Transport.T1s 11 = -1 := by decide
theorem T1s_at_12 : TitsS.Transport.T1s 12 = -1 := by decide
theorem T1s_at_13 : TitsS.Transport.T1s 13 = -1 := by decide
theorem T1s_at_14 : TitsS.Transport.T1s 14 = 1 := by decide
theorem T1s_at_15 : TitsS.Transport.T1s 15 = 1 := by decide
theorem T1s_at_16 : TitsS.Transport.T1s 16 = -1 := by decide
theorem T1s_at_17 : TitsS.Transport.T1s 17 = 1 := by decide
theorem T1s_at_18 : TitsS.Transport.T1s 18 = 1 := by decide
theorem T1s_at_19 : TitsS.Transport.T1s 19 = -1 := by decide
theorem T1s_at_20 : TitsS.Transport.T1s 20 = -1 := by decide
theorem T1s_at_21 : TitsS.Transport.T1s 21 = 1 := by decide
theorem T1s_at_22 : TitsS.Transport.T1s 22 = -1 := by decide
theorem T1s_at_23 : TitsS.Transport.T1s 23 = 1 := by decide
theorem T1s_at_24 : TitsS.Transport.T1s 24 = 1 := by decide
theorem T1s_at_25 : TitsS.Transport.T1s 25 = -1 := by decide
theorem T1s_at_26 : TitsS.Transport.T1s 26 = 1 := by decide
theorem T1pinv_at_0 : TitsS.Transport.T1pinv 0 = 0 := by decide
theorem T1pinv_at_1 : TitsS.Transport.T1pinv 1 = 1 := by decide
theorem T1pinv_at_2 : TitsS.Transport.T1pinv 2 = 2 := by decide
theorem T1pinv_at_3 : TitsS.Transport.T1pinv 3 = 5 := by decide
theorem T1pinv_at_4 : TitsS.Transport.T1pinv 4 = 6 := by decide
theorem T1pinv_at_5 : TitsS.Transport.T1pinv 5 = 3 := by decide
theorem T1pinv_at_6 : TitsS.Transport.T1pinv 6 = 4 := by decide
theorem T1pinv_at_7 : TitsS.Transport.T1pinv 7 = 9 := by decide
theorem T1pinv_at_8 : TitsS.Transport.T1pinv 8 = 10 := by decide
theorem T1pinv_at_9 : TitsS.Transport.T1pinv 9 = 7 := by decide
theorem T1pinv_at_10 : TitsS.Transport.T1pinv 10 = 8 := by decide
theorem T1pinv_at_11 : TitsS.Transport.T1pinv 11 = 15 := by decide
theorem T1pinv_at_12 : TitsS.Transport.T1pinv 12 = 16 := by decide
theorem T1pinv_at_13 : TitsS.Transport.T1pinv 13 = 17 := by decide
theorem T1pinv_at_14 : TitsS.Transport.T1pinv 14 = 18 := by decide
theorem T1pinv_at_15 : TitsS.Transport.T1pinv 15 = 11 := by decide
theorem T1pinv_at_16 : TitsS.Transport.T1pinv 16 = 12 := by decide
theorem T1pinv_at_17 : TitsS.Transport.T1pinv 17 = 13 := by decide
theorem T1pinv_at_18 : TitsS.Transport.T1pinv 18 = 14 := by decide
theorem T1pinv_at_19 : TitsS.Transport.T1pinv 19 = 25 := by decide
theorem T1pinv_at_20 : TitsS.Transport.T1pinv 20 = 26 := by decide
theorem T1pinv_at_21 : TitsS.Transport.T1pinv 21 = 23 := by decide
theorem T1pinv_at_22 : TitsS.Transport.T1pinv 22 = 24 := by decide
theorem T1pinv_at_23 : TitsS.Transport.T1pinv 23 = 21 := by decide
theorem T1pinv_at_24 : TitsS.Transport.T1pinv 24 = 22 := by decide
theorem T1pinv_at_25 : TitsS.Transport.T1pinv 25 = 19 := by decide
theorem T1pinv_at_26 : TitsS.Transport.T1pinv 26 = 20 := by decide
theorem T1si_at_0 : TitsS.Transport.T1si 0 = 1 := by decide
theorem T1si_at_1 : TitsS.Transport.T1si 1 = 1 := by decide
theorem T1si_at_2 : TitsS.Transport.T1si 2 = 1 := by decide
theorem T1si_at_3 : TitsS.Transport.T1si 3 = 1 := by decide
theorem T1si_at_4 : TitsS.Transport.T1si 4 = 1 := by decide
theorem T1si_at_5 : TitsS.Transport.T1si 5 = -1 := by decide
theorem T1si_at_6 : TitsS.Transport.T1si 6 = 1 := by decide
theorem T1si_at_7 : TitsS.Transport.T1si 7 = -1 := by decide
theorem T1si_at_8 : TitsS.Transport.T1si 8 = 1 := by decide
theorem T1si_at_9 : TitsS.Transport.T1si 9 = 1 := by decide
theorem T1si_at_10 : TitsS.Transport.T1si 10 = 1 := by decide
theorem T1si_at_11 : TitsS.Transport.T1si 11 = 1 := by decide
theorem T1si_at_12 : TitsS.Transport.T1si 12 = -1 := by decide
theorem T1si_at_13 : TitsS.Transport.T1si 13 = 1 := by decide
theorem T1si_at_14 : TitsS.Transport.T1si 14 = 1 := by decide
theorem T1si_at_15 : TitsS.Transport.T1si 15 = -1 := by decide
theorem T1si_at_16 : TitsS.Transport.T1si 16 = -1 := by decide
theorem T1si_at_17 : TitsS.Transport.T1si 17 = -1 := by decide
theorem T1si_at_18 : TitsS.Transport.T1si 18 = 1 := by decide
theorem T1si_at_19 : TitsS.Transport.T1si 19 = -1 := by decide
theorem T1si_at_20 : TitsS.Transport.T1si 20 = 1 := by decide
theorem T1si_at_21 : TitsS.Transport.T1si 21 = 1 := by decide
theorem T1si_at_22 : TitsS.Transport.T1si 22 = 1 := by decide
theorem T1si_at_23 : TitsS.Transport.T1si 23 = 1 := by decide
theorem T1si_at_24 : TitsS.Transport.T1si 24 = -1 := by decide
theorem T1si_at_25 : TitsS.Transport.T1si 25 = -1 := by decide
theorem T1si_at_26 : TitsS.Transport.T1si 26 = -1 := by decide
theorem T2pinv_at_0 : TitsS.Transport.T2pinv 0 = 0 := by decide
theorem T2pinv_at_1 : TitsS.Transport.T2pinv 1 = 1 := by decide
theorem T2pinv_at_2 : TitsS.Transport.T2pinv 2 = 2 := by decide
theorem T2pinv_at_3 : TitsS.Transport.T2pinv 3 = 7 := by decide
theorem T2pinv_at_4 : TitsS.Transport.T2pinv 4 = 8 := by decide
theorem T2pinv_at_5 : TitsS.Transport.T2pinv 5 = 9 := by decide
theorem T2pinv_at_6 : TitsS.Transport.T2pinv 6 = 10 := by decide
theorem T2pinv_at_7 : TitsS.Transport.T2pinv 7 = 3 := by decide
theorem T2pinv_at_8 : TitsS.Transport.T2pinv 8 = 4 := by decide
theorem T2pinv_at_9 : TitsS.Transport.T2pinv 9 = 5 := by decide
theorem T2pinv_at_10 : TitsS.Transport.T2pinv 10 = 6 := by decide
theorem T2pinv_at_11 : TitsS.Transport.T2pinv 11 = 17 := by decide
theorem T2pinv_at_12 : TitsS.Transport.T2pinv 12 = 18 := by decide
theorem T2pinv_at_13 : TitsS.Transport.T2pinv 13 = 15 := by decide
theorem T2pinv_at_14 : TitsS.Transport.T2pinv 14 = 16 := by decide
theorem T2pinv_at_15 : TitsS.Transport.T2pinv 15 = 13 := by decide
theorem T2pinv_at_16 : TitsS.Transport.T2pinv 16 = 14 := by decide
theorem T2pinv_at_17 : TitsS.Transport.T2pinv 17 = 11 := by decide
theorem T2pinv_at_18 : TitsS.Transport.T2pinv 18 = 12 := by decide
theorem T2pinv_at_19 : TitsS.Transport.T2pinv 19 = 21 := by decide
theorem T2pinv_at_20 : TitsS.Transport.T2pinv 20 = 22 := by decide
theorem T2pinv_at_21 : TitsS.Transport.T2pinv 21 = 19 := by decide
theorem T2pinv_at_22 : TitsS.Transport.T2pinv 22 = 20 := by decide
theorem T2pinv_at_23 : TitsS.Transport.T2pinv 23 = 25 := by decide
theorem T2pinv_at_24 : TitsS.Transport.T2pinv 24 = 26 := by decide
theorem T2pinv_at_25 : TitsS.Transport.T2pinv 25 = 23 := by decide
theorem T2pinv_at_26 : TitsS.Transport.T2pinv 26 = 24 := by decide
theorem T2si_at_0 : TitsS.Transport.T2si 0 = 1 := by decide
theorem T2si_at_1 : TitsS.Transport.T2si 1 = 1 := by decide
theorem T2si_at_2 : TitsS.Transport.T2si 2 = 1 := by decide
theorem T2si_at_3 : TitsS.Transport.T2si 3 = -1 := by decide
theorem T2si_at_4 : TitsS.Transport.T2si 4 = 1 := by decide
theorem T2si_at_5 : TitsS.Transport.T2si 5 = -1 := by decide
theorem T2si_at_6 : TitsS.Transport.T2si 6 = 1 := by decide
theorem T2si_at_7 : TitsS.Transport.T2si 7 = 1 := by decide
theorem T2si_at_8 : TitsS.Transport.T2si 8 = 1 := by decide
theorem T2si_at_9 : TitsS.Transport.T2si 9 = 1 := by decide
theorem T2si_at_10 : TitsS.Transport.T2si 10 = 1 := by decide
theorem T2si_at_11 : TitsS.Transport.T2si 11 = -1 := by decide
theorem T2si_at_12 : TitsS.Transport.T2si 12 = 1 := by decide
theorem T2si_at_13 : TitsS.Transport.T2si 13 = 1 := by decide
theorem T2si_at_14 : TitsS.Transport.T2si 14 = -1 := by decide
theorem T2si_at_15 : TitsS.Transport.T2si 15 = -1 := by decide
theorem T2si_at_16 : TitsS.Transport.T2si 16 = -1 := by decide
theorem T2si_at_17 : TitsS.Transport.T2si 17 = 1 := by decide
theorem T2si_at_18 : TitsS.Transport.T2si 18 = 1 := by decide
theorem T2si_at_19 : TitsS.Transport.T2si 19 = -1 := by decide
theorem T2si_at_20 : TitsS.Transport.T2si 20 = 1 := by decide
theorem T2si_at_21 : TitsS.Transport.T2si 21 = -1 := by decide
theorem T2si_at_22 : TitsS.Transport.T2si 22 = -1 := by decide
theorem T2si_at_23 : TitsS.Transport.T2si 23 = 1 := by decide
theorem T2si_at_24 : TitsS.Transport.T2si 24 = 1 := by decide
theorem T2si_at_25 : TitsS.Transport.T2si 25 = 1 := by decide
theorem T2si_at_26 : TitsS.Transport.T2si 26 = -1 := by decide
theorem T3pinv_at_0 : TitsS.Transport.T3pinv 0 = 0 := by decide
theorem T3pinv_at_1 : TitsS.Transport.T3pinv 1 = 1 := by decide
theorem T3pinv_at_2 : TitsS.Transport.T3pinv 2 = 2 := by decide
theorem T3pinv_at_3 : TitsS.Transport.T3pinv 3 = 9 := by decide
theorem T3pinv_at_4 : TitsS.Transport.T3pinv 4 = 10 := by decide
theorem T3pinv_at_5 : TitsS.Transport.T3pinv 5 = 7 := by decide
theorem T3pinv_at_6 : TitsS.Transport.T3pinv 6 = 8 := by decide
theorem T3pinv_at_7 : TitsS.Transport.T3pinv 7 = 5 := by decide
theorem T3pinv_at_8 : TitsS.Transport.T3pinv 8 = 6 := by decide
theorem T3pinv_at_9 : TitsS.Transport.T3pinv 9 = 3 := by decide
theorem T3pinv_at_10 : TitsS.Transport.T3pinv 10 = 4 := by decide
theorem T3pinv_at_11 : TitsS.Transport.T3pinv 11 = 13 := by decide
theorem T3pinv_at_12 : TitsS.Transport.T3pinv 12 = 14 := by decide
theorem T3pinv_at_13 : TitsS.Transport.T3pinv 13 = 11 := by decide
theorem T3pinv_at_14 : TitsS.Transport.T3pinv 14 = 12 := by decide
theorem T3pinv_at_15 : TitsS.Transport.T3pinv 15 = 17 := by decide
theorem T3pinv_at_16 : TitsS.Transport.T3pinv 16 = 18 := by decide
theorem T3pinv_at_17 : TitsS.Transport.T3pinv 17 = 15 := by decide
theorem T3pinv_at_18 : TitsS.Transport.T3pinv 18 = 16 := by decide
theorem T3pinv_at_19 : TitsS.Transport.T3pinv 19 = 23 := by decide
theorem T3pinv_at_20 : TitsS.Transport.T3pinv 20 = 24 := by decide
theorem T3pinv_at_21 : TitsS.Transport.T3pinv 21 = 25 := by decide
theorem T3pinv_at_22 : TitsS.Transport.T3pinv 22 = 26 := by decide
theorem T3pinv_at_23 : TitsS.Transport.T3pinv 23 = 19 := by decide
theorem T3pinv_at_24 : TitsS.Transport.T3pinv 24 = 20 := by decide
theorem T3pinv_at_25 : TitsS.Transport.T3pinv 25 = 21 := by decide
theorem T3pinv_at_26 : TitsS.Transport.T3pinv 26 = 22 := by decide
theorem T3si_at_0 : TitsS.Transport.T3si 0 = 1 := by decide
theorem T3si_at_1 : TitsS.Transport.T3si 1 = 1 := by decide
theorem T3si_at_2 : TitsS.Transport.T3si 2 = 1 := by decide
theorem T3si_at_3 : TitsS.Transport.T3si 3 = -1 := by decide
theorem T3si_at_4 : TitsS.Transport.T3si 4 = 1 := by decide
theorem T3si_at_5 : TitsS.Transport.T3si 5 = 1 := by decide
theorem T3si_at_6 : TitsS.Transport.T3si 6 = 1 := by decide
theorem T3si_at_7 : TitsS.Transport.T3si 7 = -1 := by decide
theorem T3si_at_8 : TitsS.Transport.T3si 8 = 1 := by decide
theorem T3si_at_9 : TitsS.Transport.T3si 9 = 1 := by decide
theorem T3si_at_10 : TitsS.Transport.T3si 10 = 1 := by decide
theorem T3si_at_11 : TitsS.Transport.T3si 11 = 1 := by decide
theorem T3si_at_12 : TitsS.Transport.T3si 12 = -1 := by decide
theorem T3si_at_13 : TitsS.Transport.T3si 13 = -1 := by decide
theorem T3si_at_14 : TitsS.Transport.T3si 14 = -1 := by decide
theorem T3si_at_15 : TitsS.Transport.T3si 15 = -1 := by decide
theorem T3si_at_16 : TitsS.Transport.T3si 16 = 1 := by decide
theorem T3si_at_17 : TitsS.Transport.T3si 17 = 1 := by decide
theorem T3si_at_18 : TitsS.Transport.T3si 18 = 1 := by decide
theorem T3si_at_19 : TitsS.Transport.T3si 19 = 1 := by decide
theorem T3si_at_20 : TitsS.Transport.T3si 20 = 1 := by decide
theorem T3si_at_21 : TitsS.Transport.T3si 21 = -1 := by decide
theorem T3si_at_22 : TitsS.Transport.T3si 22 = -1 := by decide
theorem T3si_at_23 : TitsS.Transport.T3si 23 = 1 := by decide
theorem T3si_at_24 : TitsS.Transport.T3si 24 = -1 := by decide
theorem T3si_at_25 : TitsS.Transport.T3si 25 = -1 := by decide
theorem T3si_at_26 : TitsS.Transport.T3si 26 = 1 := by decide

theorem rotc_apply_0 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 0 = v 0 := rfl
theorem rotc_apply_1 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 1 = v 1 := rfl
theorem rotc_apply_2 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 2 = v 2 := rfl
theorem rotc_apply_3 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 3 = v 3 := rfl
theorem rotc_apply_4 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 4 = v 4 := rfl
theorem rotc_apply_5 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 5 = -(v 5) / 2 + c * v 6 := rfl
theorem rotc_apply_6 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 6 = -(c * v 5) - v 6 / 2 := rfl
theorem rotc_apply_7 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 7 = -(v 7) / 2 + c * v 8 := rfl
theorem rotc_apply_8 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 8 = -(c * v 7) - v 8 / 2 := rfl
theorem rotc_apply_9 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 9 = -(v 9) / 2 - c * v 10 := rfl
theorem rotc_apply_10 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 10 = c * v 9 - v 10 / 2 := rfl
theorem rotc_apply_11 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 11 = v 11 := rfl
theorem rotc_apply_12 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 12 = v 12 := rfl
theorem rotc_apply_13 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 13 = -(v 13) / 2 + c * v 14 := rfl
theorem rotc_apply_14 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 14 = -(c * v 13) - v 14 / 2 := rfl
theorem rotc_apply_15 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 15 = -(v 15) / 2 + c * v 16 := rfl
theorem rotc_apply_16 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 16 = -(c * v 15) - v 16 / 2 := rfl
theorem rotc_apply_17 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 17 = -(v 17) / 2 - c * v 18 := rfl
theorem rotc_apply_18 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 18 = c * v 17 - v 18 / 2 := rfl
theorem rotc_apply_19 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 19 = v 19 := rfl
theorem rotc_apply_20 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 20 = v 20 := rfl
theorem rotc_apply_21 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 21 = -(v 21) / 2 + c * v 22 := rfl
theorem rotc_apply_22 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 22 = -(c * v 21) - v 22 / 2 := rfl
theorem rotc_apply_23 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 23 = -(v 23) / 2 + c * v 24 := rfl
theorem rotc_apply_24 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 24 = -(c * v 23) - v 24 / 2 := rfl
theorem rotc_apply_25 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 25 = -(v 25) / 2 - c * v 26 := rfl
theorem rotc_apply_26 (c : ℝ) (v : Fin 27 → ℝ) : rotc c v 26 = c * v 25 - v 26 / 2 := rfl

/-- Extensionality on the 27 literal coordinates (keeps literal indices in the goals). -/
theorem fun27_ext {f g : Fin 27 → ℝ} (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h2 : f 2 = g 2) (h3 : f 3 = g 3) (h4 : f 4 = g 4) (h5 : f 5 = g 5) (h6 : f 6 = g 6) (h7 : f 7 = g 7) (h8 : f 8 = g 8) (h9 : f 9 = g 9) (h10 : f 10 = g 10) (h11 : f 11 = g 11) (h12 : f 12 = g 12) (h13 : f 13 = g 13) (h14 : f 14 = g 14) (h15 : f 15 = g 15) (h16 : f 16 = g 16) (h17 : f 17 = g 17) (h18 : f 18 = g 18) (h19 : f 19 = g 19) (h20 : f 20 = g 20) (h21 : f 21 = g 21) (h22 : f 22 = g 22) (h23 : f 23 = g 23) (h24 : f 24 = g 24) (h25 : f 25 = g 25) (h26 : f 26 = g 26) : f = g := by
  funext k
  fin_cases k <;> assumption

theorem rotc_rotc (c : ℝ) (hc : c ^ 2 = 3 / 4) (v : Fin 27 → ℝ) :
    rotc c (rotc c v) = rotc (-c) v := by
  funext k
  fin_cases k <;> simp [rotc] <;> ring_nf <;> (try simp only [hc]) <;> ring_nf

theorem sqrt3_half_sq : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem upper_R0_R0 (x : Glennie.Albert) :
    NativePolynomial.upperCoordinates (R0 (R0 x)) =
      rotc (-(Real.sqrt 3 / 2)) (NativePolynomial.upperCoordinates x) := by
  rw [upper_R0, upper_R0, rotc_rotc _ sqrt3_half_sq]

theorem upper_T0 (x : Glennie.Albert) :
    NativePolynomial.upperCoordinates (transportT 0 x) =
      TitsS.sgnPerm TitsS.Transport.T1p TitsS.Transport.T1s (NativePolynomial.upperCoordinates x) :=
  upper_signedTransport _ _ x

theorem upper_Ti0 (x : Glennie.Albert) :
    NativePolynomial.upperCoordinates (transportTinv 0 x) =
      TitsS.sgnPerm TitsS.Transport.T1pinv TitsS.Transport.T1si (NativePolynomial.upperCoordinates x) :=
  upper_signedTransport _ _ x

theorem upper_Ti1 (x : Glennie.Albert) :
    NativePolynomial.upperCoordinates (transportTinv 1 x) =
      TitsS.sgnPerm TitsS.Transport.T2pinv TitsS.Transport.T2si (NativePolynomial.upperCoordinates x) :=
  upper_signedTransport _ _ x

theorem upper_Ti2 (x : Glennie.Albert) :
    NativePolynomial.upperCoordinates (transportTinv 2 x) =
      TitsS.sgnPerm TitsS.Transport.T3pinv TitsS.Transport.T3si (NativePolynomial.upperCoordinates x) :=
  upper_signedTransport _ _ x

theorem sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem omega_smul_one_unitary :
    (UnitaryErrorBases.ThreeCycleFourier.omega • (1 : TitsComplexMatrix)) *
      (UnitaryErrorBases.ThreeCycleFourier.omega • (1 : TitsComplexMatrix)).conjTranspose = 1 := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, smul_mul_smul_comm, Matrix.one_mul]
  have h : UnitaryErrorBases.ThreeCycleFourier.omega * star UnitaryErrorBases.ThreeCycleFourier.omega = 1 := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, omega_re, omega_im] <;> ring_nf
    norm_num [Real.sq_sqrt]
  rw [h, one_smul]

theorem omega_smul_one_det :
    (UnitaryErrorBases.ThreeCycleFourier.omega • (1 : TitsComplexMatrix)).det = 1 := by
  rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one,
    UnitaryErrorBases.ThreeCycleFourier.omega_cube]


-- The shared table list leaves most entries unused in each coordinate goal.
set_option linter.unusedSimpArgs false in
theorem coord_comm (v : Fin 27 → ℝ) :
    (rotc (Real.sqrt 3 / 2) (TitsS.sgnPerm TitsS.Transport.T1p TitsS.Transport.T1s (rotc (Real.sqrt 3 / 2) (TitsS.sgnPerm TitsS.Transport.T1pinv TitsS.Transport.T1si v)))) =
      (TitsS.sgnPerm TitsS.Transport.T1p TitsS.Transport.T1s (rotc (Real.sqrt 3 / 2) (TitsS.sgnPerm TitsS.Transport.T1pinv TitsS.Transport.T1si (rotc (Real.sqrt 3 / 2) v)))) := by
  refine fun27_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    simp only [TitsS.sgnPerm, T1p_at_0, T1p_at_1, T1p_at_2, T1p_at_3, T1p_at_4, T1p_at_5, T1p_at_6, T1p_at_7, T1p_at_8, T1p_at_9, T1p_at_10, T1p_at_11, T1p_at_12, T1p_at_13, T1p_at_14, T1p_at_15, T1p_at_16, T1p_at_17, T1p_at_18, T1p_at_19, T1p_at_20, T1p_at_21, T1p_at_22, T1p_at_23, T1p_at_24, T1p_at_25, T1p_at_26, T1s_at_0, T1s_at_1, T1s_at_2, T1s_at_3, T1s_at_4, T1s_at_5, T1s_at_6, T1s_at_7, T1s_at_8, T1s_at_9, T1s_at_10, T1s_at_11, T1s_at_12, T1s_at_13, T1s_at_14, T1s_at_15, T1s_at_16, T1s_at_17, T1s_at_18, T1s_at_19, T1s_at_20, T1s_at_21, T1s_at_22, T1s_at_23, T1s_at_24, T1s_at_25, T1s_at_26, T1pinv_at_0, T1pinv_at_1, T1pinv_at_2, T1pinv_at_3, T1pinv_at_4, T1pinv_at_5, T1pinv_at_6, T1pinv_at_7, T1pinv_at_8, T1pinv_at_9, T1pinv_at_10, T1pinv_at_11, T1pinv_at_12, T1pinv_at_13, T1pinv_at_14, T1pinv_at_15, T1pinv_at_16, T1pinv_at_17, T1pinv_at_18, T1pinv_at_19, T1pinv_at_20, T1pinv_at_21, T1pinv_at_22, T1pinv_at_23, T1pinv_at_24, T1pinv_at_25, T1pinv_at_26, T1si_at_0, T1si_at_1, T1si_at_2, T1si_at_3, T1si_at_4, T1si_at_5, T1si_at_6, T1si_at_7, T1si_at_8, T1si_at_9, T1si_at_10, T1si_at_11, T1si_at_12, T1si_at_13, T1si_at_14, T1si_at_15, T1si_at_16, T1si_at_17, T1si_at_18, T1si_at_19, T1si_at_20, T1si_at_21, T1si_at_22, T1si_at_23, T1si_at_24, T1si_at_25, T1si_at_26, T2pinv_at_0, T2pinv_at_1, T2pinv_at_2, T2pinv_at_3, T2pinv_at_4, T2pinv_at_5, T2pinv_at_6, T2pinv_at_7, T2pinv_at_8, T2pinv_at_9, T2pinv_at_10, T2pinv_at_11, T2pinv_at_12, T2pinv_at_13, T2pinv_at_14, T2pinv_at_15, T2pinv_at_16, T2pinv_at_17, T2pinv_at_18, T2pinv_at_19, T2pinv_at_20, T2pinv_at_21, T2pinv_at_22, T2pinv_at_23, T2pinv_at_24, T2pinv_at_25, T2pinv_at_26, T2si_at_0, T2si_at_1, T2si_at_2, T2si_at_3, T2si_at_4, T2si_at_5, T2si_at_6, T2si_at_7, T2si_at_8, T2si_at_9, T2si_at_10, T2si_at_11, T2si_at_12, T2si_at_13, T2si_at_14, T2si_at_15, T2si_at_16, T2si_at_17, T2si_at_18, T2si_at_19, T2si_at_20, T2si_at_21, T2si_at_22, T2si_at_23, T2si_at_24, T2si_at_25, T2si_at_26, T3pinv_at_0, T3pinv_at_1, T3pinv_at_2, T3pinv_at_3, T3pinv_at_4, T3pinv_at_5, T3pinv_at_6, T3pinv_at_7, T3pinv_at_8, T3pinv_at_9, T3pinv_at_10, T3pinv_at_11, T3pinv_at_12, T3pinv_at_13, T3pinv_at_14, T3pinv_at_15, T3pinv_at_16, T3pinv_at_17, T3pinv_at_18, T3pinv_at_19, T3pinv_at_20, T3pinv_at_21, T3pinv_at_22, T3pinv_at_23, T3pinv_at_24, T3pinv_at_25, T3pinv_at_26, T3si_at_0, T3si_at_1, T3si_at_2, T3si_at_3, T3si_at_4, T3si_at_5, T3si_at_6, T3si_at_7, T3si_at_8, T3si_at_9, T3si_at_10, T3si_at_11, T3si_at_12, T3si_at_13, T3si_at_14, T3si_at_15, T3si_at_16, T3si_at_17, T3si_at_18, T3si_at_19, T3si_at_20, T3si_at_21, T3si_at_22, T3si_at_23, T3si_at_24, T3si_at_25, T3si_at_26,
      rotc_apply_0, rotc_apply_1, rotc_apply_2, rotc_apply_3, rotc_apply_4, rotc_apply_5, rotc_apply_6, rotc_apply_7, rotc_apply_8, rotc_apply_9, rotc_apply_10, rotc_apply_11, rotc_apply_12, rotc_apply_13, rotc_apply_14, rotc_apply_15, rotc_apply_16, rotc_apply_17, rotc_apply_18, rotc_apply_19, rotc_apply_20, rotc_apply_21, rotc_apply_22, rotc_apply_23, rotc_apply_24, rotc_apply_25, rotc_apply_26]
    try push_cast
    try ring_nf
    try simp only [sqrt3_sq]
    try ring_nf

-- The shared table list leaves most entries unused in each coordinate goal.
set_option linter.unusedSimpArgs false in
theorem coord_one_conj (v : Fin 27 → ℝ) :
    (TitsS.sgnPerm TitsS.Transport.T2pinv TitsS.Transport.T2si (rotc (-(Real.sqrt 3 / 2)) (TitsS.sgnPerm TitsS.Transport.T1p TitsS.Transport.T1s (rotc (-(Real.sqrt 3 / 2)) (TitsS.sgnPerm TitsS.Transport.T1pinv TitsS.Transport.T1si v))))) =
      (rotc (Real.sqrt 3 / 2) (TitsS.sgnPerm TitsS.Transport.T2pinv TitsS.Transport.T2si v)) := by
  refine fun27_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    simp only [TitsS.sgnPerm, T1p_at_0, T1p_at_1, T1p_at_2, T1p_at_3, T1p_at_4, T1p_at_5, T1p_at_6, T1p_at_7, T1p_at_8, T1p_at_9, T1p_at_10, T1p_at_11, T1p_at_12, T1p_at_13, T1p_at_14, T1p_at_15, T1p_at_16, T1p_at_17, T1p_at_18, T1p_at_19, T1p_at_20, T1p_at_21, T1p_at_22, T1p_at_23, T1p_at_24, T1p_at_25, T1p_at_26, T1s_at_0, T1s_at_1, T1s_at_2, T1s_at_3, T1s_at_4, T1s_at_5, T1s_at_6, T1s_at_7, T1s_at_8, T1s_at_9, T1s_at_10, T1s_at_11, T1s_at_12, T1s_at_13, T1s_at_14, T1s_at_15, T1s_at_16, T1s_at_17, T1s_at_18, T1s_at_19, T1s_at_20, T1s_at_21, T1s_at_22, T1s_at_23, T1s_at_24, T1s_at_25, T1s_at_26, T1pinv_at_0, T1pinv_at_1, T1pinv_at_2, T1pinv_at_3, T1pinv_at_4, T1pinv_at_5, T1pinv_at_6, T1pinv_at_7, T1pinv_at_8, T1pinv_at_9, T1pinv_at_10, T1pinv_at_11, T1pinv_at_12, T1pinv_at_13, T1pinv_at_14, T1pinv_at_15, T1pinv_at_16, T1pinv_at_17, T1pinv_at_18, T1pinv_at_19, T1pinv_at_20, T1pinv_at_21, T1pinv_at_22, T1pinv_at_23, T1pinv_at_24, T1pinv_at_25, T1pinv_at_26, T1si_at_0, T1si_at_1, T1si_at_2, T1si_at_3, T1si_at_4, T1si_at_5, T1si_at_6, T1si_at_7, T1si_at_8, T1si_at_9, T1si_at_10, T1si_at_11, T1si_at_12, T1si_at_13, T1si_at_14, T1si_at_15, T1si_at_16, T1si_at_17, T1si_at_18, T1si_at_19, T1si_at_20, T1si_at_21, T1si_at_22, T1si_at_23, T1si_at_24, T1si_at_25, T1si_at_26, T2pinv_at_0, T2pinv_at_1, T2pinv_at_2, T2pinv_at_3, T2pinv_at_4, T2pinv_at_5, T2pinv_at_6, T2pinv_at_7, T2pinv_at_8, T2pinv_at_9, T2pinv_at_10, T2pinv_at_11, T2pinv_at_12, T2pinv_at_13, T2pinv_at_14, T2pinv_at_15, T2pinv_at_16, T2pinv_at_17, T2pinv_at_18, T2pinv_at_19, T2pinv_at_20, T2pinv_at_21, T2pinv_at_22, T2pinv_at_23, T2pinv_at_24, T2pinv_at_25, T2pinv_at_26, T2si_at_0, T2si_at_1, T2si_at_2, T2si_at_3, T2si_at_4, T2si_at_5, T2si_at_6, T2si_at_7, T2si_at_8, T2si_at_9, T2si_at_10, T2si_at_11, T2si_at_12, T2si_at_13, T2si_at_14, T2si_at_15, T2si_at_16, T2si_at_17, T2si_at_18, T2si_at_19, T2si_at_20, T2si_at_21, T2si_at_22, T2si_at_23, T2si_at_24, T2si_at_25, T2si_at_26, T3pinv_at_0, T3pinv_at_1, T3pinv_at_2, T3pinv_at_3, T3pinv_at_4, T3pinv_at_5, T3pinv_at_6, T3pinv_at_7, T3pinv_at_8, T3pinv_at_9, T3pinv_at_10, T3pinv_at_11, T3pinv_at_12, T3pinv_at_13, T3pinv_at_14, T3pinv_at_15, T3pinv_at_16, T3pinv_at_17, T3pinv_at_18, T3pinv_at_19, T3pinv_at_20, T3pinv_at_21, T3pinv_at_22, T3pinv_at_23, T3pinv_at_24, T3pinv_at_25, T3pinv_at_26, T3si_at_0, T3si_at_1, T3si_at_2, T3si_at_3, T3si_at_4, T3si_at_5, T3si_at_6, T3si_at_7, T3si_at_8, T3si_at_9, T3si_at_10, T3si_at_11, T3si_at_12, T3si_at_13, T3si_at_14, T3si_at_15, T3si_at_16, T3si_at_17, T3si_at_18, T3si_at_19, T3si_at_20, T3si_at_21, T3si_at_22, T3si_at_23, T3si_at_24, T3si_at_25, T3si_at_26,
      rotc_apply_0, rotc_apply_1, rotc_apply_2, rotc_apply_3, rotc_apply_4, rotc_apply_5, rotc_apply_6, rotc_apply_7, rotc_apply_8, rotc_apply_9, rotc_apply_10, rotc_apply_11, rotc_apply_12, rotc_apply_13, rotc_apply_14, rotc_apply_15, rotc_apply_16, rotc_apply_17, rotc_apply_18, rotc_apply_19, rotc_apply_20, rotc_apply_21, rotc_apply_22, rotc_apply_23, rotc_apply_24, rotc_apply_25, rotc_apply_26]
    try push_cast
    try ring_nf
    try simp only [sqrt3_sq]
    try ring_nf

-- The shared table list leaves most entries unused in each coordinate goal.
set_option linter.unusedSimpArgs false in
theorem coord_two_conj (v : Fin 27 → ℝ) :
    (TitsS.sgnPerm TitsS.Transport.T3pinv TitsS.Transport.T3si (rotc (-(Real.sqrt 3 / 2)) (TitsS.sgnPerm TitsS.Transport.T1p TitsS.Transport.T1s (rotc (Real.sqrt 3 / 2) (TitsS.sgnPerm TitsS.Transport.T1pinv TitsS.Transport.T1si v))))) =
      (rotc (Real.sqrt 3 / 2) (TitsS.sgnPerm TitsS.Transport.T3pinv TitsS.Transport.T3si v)) := by
  refine fun27_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    simp only [TitsS.sgnPerm, T1p_at_0, T1p_at_1, T1p_at_2, T1p_at_3, T1p_at_4, T1p_at_5, T1p_at_6, T1p_at_7, T1p_at_8, T1p_at_9, T1p_at_10, T1p_at_11, T1p_at_12, T1p_at_13, T1p_at_14, T1p_at_15, T1p_at_16, T1p_at_17, T1p_at_18, T1p_at_19, T1p_at_20, T1p_at_21, T1p_at_22, T1p_at_23, T1p_at_24, T1p_at_25, T1p_at_26, T1s_at_0, T1s_at_1, T1s_at_2, T1s_at_3, T1s_at_4, T1s_at_5, T1s_at_6, T1s_at_7, T1s_at_8, T1s_at_9, T1s_at_10, T1s_at_11, T1s_at_12, T1s_at_13, T1s_at_14, T1s_at_15, T1s_at_16, T1s_at_17, T1s_at_18, T1s_at_19, T1s_at_20, T1s_at_21, T1s_at_22, T1s_at_23, T1s_at_24, T1s_at_25, T1s_at_26, T1pinv_at_0, T1pinv_at_1, T1pinv_at_2, T1pinv_at_3, T1pinv_at_4, T1pinv_at_5, T1pinv_at_6, T1pinv_at_7, T1pinv_at_8, T1pinv_at_9, T1pinv_at_10, T1pinv_at_11, T1pinv_at_12, T1pinv_at_13, T1pinv_at_14, T1pinv_at_15, T1pinv_at_16, T1pinv_at_17, T1pinv_at_18, T1pinv_at_19, T1pinv_at_20, T1pinv_at_21, T1pinv_at_22, T1pinv_at_23, T1pinv_at_24, T1pinv_at_25, T1pinv_at_26, T1si_at_0, T1si_at_1, T1si_at_2, T1si_at_3, T1si_at_4, T1si_at_5, T1si_at_6, T1si_at_7, T1si_at_8, T1si_at_9, T1si_at_10, T1si_at_11, T1si_at_12, T1si_at_13, T1si_at_14, T1si_at_15, T1si_at_16, T1si_at_17, T1si_at_18, T1si_at_19, T1si_at_20, T1si_at_21, T1si_at_22, T1si_at_23, T1si_at_24, T1si_at_25, T1si_at_26, T2pinv_at_0, T2pinv_at_1, T2pinv_at_2, T2pinv_at_3, T2pinv_at_4, T2pinv_at_5, T2pinv_at_6, T2pinv_at_7, T2pinv_at_8, T2pinv_at_9, T2pinv_at_10, T2pinv_at_11, T2pinv_at_12, T2pinv_at_13, T2pinv_at_14, T2pinv_at_15, T2pinv_at_16, T2pinv_at_17, T2pinv_at_18, T2pinv_at_19, T2pinv_at_20, T2pinv_at_21, T2pinv_at_22, T2pinv_at_23, T2pinv_at_24, T2pinv_at_25, T2pinv_at_26, T2si_at_0, T2si_at_1, T2si_at_2, T2si_at_3, T2si_at_4, T2si_at_5, T2si_at_6, T2si_at_7, T2si_at_8, T2si_at_9, T2si_at_10, T2si_at_11, T2si_at_12, T2si_at_13, T2si_at_14, T2si_at_15, T2si_at_16, T2si_at_17, T2si_at_18, T2si_at_19, T2si_at_20, T2si_at_21, T2si_at_22, T2si_at_23, T2si_at_24, T2si_at_25, T2si_at_26, T3pinv_at_0, T3pinv_at_1, T3pinv_at_2, T3pinv_at_3, T3pinv_at_4, T3pinv_at_5, T3pinv_at_6, T3pinv_at_7, T3pinv_at_8, T3pinv_at_9, T3pinv_at_10, T3pinv_at_11, T3pinv_at_12, T3pinv_at_13, T3pinv_at_14, T3pinv_at_15, T3pinv_at_16, T3pinv_at_17, T3pinv_at_18, T3pinv_at_19, T3pinv_at_20, T3pinv_at_21, T3pinv_at_22, T3pinv_at_23, T3pinv_at_24, T3pinv_at_25, T3pinv_at_26, T3si_at_0, T3si_at_1, T3si_at_2, T3si_at_3, T3si_at_4, T3si_at_5, T3si_at_6, T3si_at_7, T3si_at_8, T3si_at_9, T3si_at_10, T3si_at_11, T3si_at_12, T3si_at_13, T3si_at_14, T3si_at_15, T3si_at_16, T3si_at_17, T3si_at_18, T3si_at_19, T3si_at_20, T3si_at_21, T3si_at_22, T3si_at_23, T3si_at_24, T3si_at_25, T3si_at_26,
      rotc_apply_0, rotc_apply_1, rotc_apply_2, rotc_apply_3, rotc_apply_4, rotc_apply_5, rotc_apply_6, rotc_apply_7, rotc_apply_8, rotc_apply_9, rotc_apply_10, rotc_apply_11, rotc_apply_12, rotc_apply_13, rotc_apply_14, rotc_apply_15, rotc_apply_16, rotc_apply_17, rotc_apply_18, rotc_apply_19, rotc_apply_20, rotc_apply_21, rotc_apply_22, rotc_apply_23, rotc_apply_24, rotc_apply_25, rotc_apply_26]
    try push_cast
    try ring_nf
    try simp only [sqrt3_sq]
    try ring_nf

theorem R0_isNativeAut : IsNativeAut R0 := by
  exact ⟨nativeRightMultiply_jordan _ omega_smul_one_unitary omega_smul_one_det,
    nativeRightMultiply_trace _⟩

theorem transportT_isNativeAut (i : Fin 3) : IsNativeAut (transportT i) := by
  fin_cases i
  · exact isNativeAut_of_coordinates _ _ (TitsS.Transport.T1_isAut (1 / 2 : ℝ))
      (upper_signedTransport _ _)
  · exact isNativeAut_of_coordinates _ _ (TitsS.Transport.T2_isAut (1 / 2 : ℝ))
      (upper_signedTransport _ _)
  · exact isNativeAut_of_coordinates _ _ (TitsS.Transport.T3_isAut (1 / 2 : ℝ))
      (upper_signedTransport _ _)

theorem transportTinv_isNativeAut (i : Fin 3) : IsNativeAut (transportTinv i) := by
  fin_cases i
  · exact isNativeAut_of_coordinates _ _ (TitsS.Transport.T1_inv_isAut (1 / 2 : ℝ))
      (upper_signedTransport _ _)
  · exact isNativeAut_of_coordinates _ _ (TitsS.Transport.T2_inv_isAut (1 / 2 : ℝ))
      (upper_signedTransport _ _)
  · exact isNativeAut_of_coordinates _ _ (TitsS.Transport.T3_inv_isAut (1 / 2 : ℝ))
      (upper_signedTransport _ _)

theorem transportTinv_comp_transportT (i : Fin 3) :
    transportTinv i ∘ₗ transportT i = LinearMap.id := by
  fin_cases i
  · exact signedTransport_comp_eq_id _ _ _ _ T1_inv_rel'
  · exact signedTransport_comp_eq_id _ _ _ _ T2_inv_rel'
  · exact signedTransport_comp_eq_id _ _ _ _ T3_inv_rel'

theorem transportT_comp_transportTinv (i : Fin 3) :
    transportT i ∘ₗ transportTinv i = LinearMap.id := by
  fin_cases i
  · exact signedTransport_comp_eq_id _ _ _ _ TitsS.Transport.T1_inv_rel
  · exact signedTransport_comp_eq_id _ _ _ _ TitsS.Transport.T2_inv_rel
  · exact signedTransport_comp_eq_id _ _ _ _ TitsS.Transport.T3_inv_rel

theorem R1_isNativeAut : IsNativeAut R1 := by
  exact (transportT_isNativeAut 0).comp (R0_isNativeAut.comp (transportTinv_isNativeAut 0))

theorem R0_cube : R0 ^ 3 = 1 := by
  refine LinearMap.ext fun x => ?_
  rw [pow_three, Module.End.mul_apply, Module.End.mul_apply, Module.End.one_apply]
  change nativeRightMultiply _ (nativeRightMultiply _ (nativeRightMultiply _ x)) = x
  rw [nativeRightMultiply_comp, nativeRightMultiply_comp, smul_mul_smul_comm, Matrix.one_mul,
    smul_mul_smul_comm, Matrix.one_mul, ← pow_two, ← pow_succ',
    UnitaryErrorBases.ThreeCycleFourier.omega_cube, one_smul, nativeRightMultiply_one]

theorem R1_cube : R1 ^ 3 = 1 := by
  have hTiT : ∀ y, transportTinv 0 (transportT 0 y) = y := fun y =>
    LinearMap.congr_fun (transportTinv_comp_transportT 0) y
  have hTTi : ∀ y, transportT 0 (transportTinv 0 y) = y := fun y =>
    LinearMap.congr_fun (transportT_comp_transportTinv 0) y
  have h0 : ∀ y, R0 (R0 (R0 y)) = y := fun y => by
    have := LinearMap.congr_fun R0_cube y
    rwa [pow_three, Module.End.mul_apply, Module.End.mul_apply, Module.End.one_apply] at this
  refine LinearMap.ext fun x => ?_
  rw [pow_three, Module.End.mul_apply, Module.End.mul_apply, Module.End.one_apply]
  simp only [R1, LinearMap.comp_apply, hTiT, h0, hTTi]

theorem R0_mul_R1_comm : R0 * R1 = R1 * R0 := by
  refine LinearMap.ext fun x => ?_
  apply NativePolynomial.upperCoordinateEquiv.injective
  change NativePolynomial.upperCoordinates _ = NativePolynomial.upperCoordinates _
  simp only [Module.End.mul_apply, R1, LinearMap.comp_apply]
  rw [upper_R0, upper_T0, upper_R0, upper_Ti0, upper_T0, upper_R0, upper_Ti0, upper_R0]
  exact coord_comm _

/-- MASTER §6.5: `T₂ R₀ T₂⁻¹ = R₀² R₁²`, stated as the conjugation used by anchor 2. -/
theorem transportTinv_one_conj : transportTinv 1 ∘ₗ (R0 ^ 2 * R1 ^ 2) = R0 ∘ₗ transportTinv 1 := by
  have hTiT : ∀ y, transportTinv 0 (transportT 0 y) = y := fun y =>
    LinearMap.congr_fun (transportTinv_comp_transportT 0) y
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, pow_two, Module.End.mul_apply]
  simp only [R1, LinearMap.comp_apply, hTiT]
  apply NativePolynomial.upperCoordinateEquiv.injective
  change NativePolynomial.upperCoordinates _ = NativePolynomial.upperCoordinates _
  rw [upper_Ti1, upper_R0_R0, upper_T0, upper_R0_R0, upper_Ti0, upper_R0, upper_Ti1]
  exact coord_one_conj _

/-- MASTER §6.5: `T₃ R₀ T₃⁻¹ = R₀² R₁`, stated as the conjugation used by anchor 3. -/
theorem transportTinv_two_conj : transportTinv 2 ∘ₗ (R0 ^ 2 * R1) = R0 ∘ₗ transportTinv 2 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, pow_two, Module.End.mul_apply]
  simp only [R1, LinearMap.comp_apply]
  apply NativePolynomial.upperCoordinateEquiv.injective
  change NativePolynomial.upperCoordinates _ = NativePolynomial.upperCoordinates _
  rw [upper_Ti2, upper_R0_R0, upper_T0, upper_R0, upper_Ti0, upper_R0, upper_Ti2]
  exact coord_two_conj _

end CKM.NativeFirstOrder

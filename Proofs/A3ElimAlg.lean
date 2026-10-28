module

public import A3Interfaces

@[expose] public section

/-!
# Elimination helpers I: Tits-pair algebra

General facts about the native compact Albert algebra read through the injective matrix-pair map
`nativeTitsMatrixPair`, the cube root `ω`, and the special-unitary adjugate polarization.
No phase or configuration data enters.
-/

noncomputable section

namespace CKM.NativeFirstOrder.Elim

open CompactAlbert

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega
local notation "πp" => CompactAlbert.nativeTitsMatrixPair

/-! ## Cube root of unity -/

theorem omega_ne_one : ω ≠ 1 := by
  intro h
  have h2 := UnitaryErrorBases.ThreeCycleFourier.omega_sq
  rw [h] at h2
  norm_num at h2

theorem one_add_omega_add_sq : 1 + ω + ω ^ 2 = 0 := by
  rw [UnitaryErrorBases.ThreeCycleFourier.omega_sq]; ring

theorem star_omega : star ω = ω ^ 2 := by
  rw [UnitaryErrorBases.ThreeCycleFourier.omega_sq]
  apply Complex.ext <;>
    simp [UnitaryErrorBases.ThreeCycleFourier.omega] <;> ring

theorem omega_im_ne_zero : Complex.im ω ≠ 0 := by
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  simp [UnitaryErrorBases.ThreeCycleFourier.omega, h3]

theorem omega_mul_star : ω * star ω = 1 := by
  rw [star_omega, ← pow_succ', UnitaryErrorBases.ThreeCycleFourier.omega_cube]

theorem omega_pow_mul_star (n : ℕ) : ω ^ n * star (ω ^ n) = 1 := by
  rw [star_pow, ← mul_pow, omega_mul_star, one_pow]

theorem omega_pow_cube (n : ℕ) : (ω ^ n) ^ 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, UnitaryErrorBases.ThreeCycleFourier.omega_cube, one_pow]

/-- A complex number with vanishing real part against `1` and `ω` is zero. -/
theorem eq_zero_of_re_of_re_omega {X : ℂ} (h0 : X.re = 0) (h1 : (ω * X).re = 0) : X = 0 := by
  rw [Complex.mul_re, h0, mul_zero, zero_sub, neg_eq_zero] at h1
  have him : X.im = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h omega_im_ne_zero
    · exact h
  exact Complex.ext h0 him

/-! ## The matrix-pair reading -/

theorem pair_fst_isHermitian (x : Glennie.Albert) : (πp x).1.IsHermitian :=
  hermitianMatrix_isHermitian (toTitsCoordinates x)

/-- A native point with prescribed Hermitian visible part and arbitrary hidden part. -/
def mkPoint (a : TitsComplexMatrix) (ha : a.IsHermitian) (B : TitsComplexMatrix) : Glennie.Albert :=
  fromTitsCoordinates (fromHermitianPair (⟨a, ha⟩, B))

theorem mkPoint_pair (a : TitsComplexMatrix) (ha : a.IsHermitian) (B : TitsComplexMatrix) :
    πp (mkPoint a ha B) = (a, B) := by
  have h : toHermitianPair (toTitsCoordinates (mkPoint a ha B)) = (⟨a, ha⟩, B) := by
    unfold mkPoint
    rw [toTitsCoordinates_fromTitsCoordinates, toHermitianPair_fromHermitianPair]
  apply Prod.ext
  · change hermitianMatrix (toTitsCoordinates (mkPoint a ha B)) = a
    exact congrArg (fun q : HermitianTitsPair => q.1.val) h
  · change (toTitsCoordinates (mkPoint a ha B)).2.2 = B
    exact congrArg (fun q : HermitianTitsPair => q.2) h

theorem pair_inj {x y : Glennie.Albert} : πp x = πp y ↔ x = y :=
  nativeTitsMatrixPair_injective.eq_iff

theorem pair_eq_zero {x : Glennie.Albert} : πp x = 0 ↔ x = 0 := by
  rw [← (πp).map_zero, pair_inj]

theorem jordan_pair (x y : Glennie.Albert) :
    πp (Glennie.jordan x y) = compactSecondTitsProduct (πp x) (πp y) :=
  native_tits_product_pair x y

theorem trace_jordan_pair (x y : Glennie.Albert) :
    Glennie.trace (Glennie.jordan x y) =
      ((πp x).1 * (πp y).1).trace.re + 2 * ((πp x).2 * (πp y).2.conjTranspose).trace.re :=
  native_trace_jordan_eq_tits_pairing x y

theorem R0_pair (x : Glennie.Albert) : πp (R0 x) = ((πp x).1, ω • (πp x).2) := by
  unfold R0
  rw [nativeRightMultiply_pair, Matrix.mul_smul, Matrix.mul_one]

theorem unit_pair : πp (1 : Glennie.Albert) = (1, 0) := by
  change toMatrixPair (compactTitsCoordinateEquiv (1 : Glennie.Albert)) = _
  rw [compactTitsCoordinateEquiv_unit]
  apply Prod.ext
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [toMatrixPair, hermitianMatrix, titsUnit]
  · rfl

/-- Product of two points with zero hidden part. -/
theorem jordan_pair_visible (x y : Glennie.Albert) {a c : TitsComplexMatrix}
    (hx : πp x = (a, 0)) (hy : πp y = (c, 0)) :
    πp (Glennie.jordan x y) = ((1 / 2 : ℂ) • (a * c + c * a), 0) := by
  rw [jordan_pair, hx, hy]
  simp [compactSecondTitsProduct, compactSecondTitsProductComplex,
    compactSecondTitsProductHidden, Matrix.adjugate_zero]

/-- Product of a point with visible part `I/3` and a point with zero visible part. -/
theorem jordan_pair_third_hidden (x y : Glennie.Albert) {B D : TitsComplexMatrix}
    (hx : πp x = ((1 / 3 : ℂ) • (1 : TitsComplexMatrix), B)) (hy : πp y = (0, D)) :
    πp (Glennie.jordan x y) =
      ((1 / 2 : ℂ) • (-(B * D.conjTranspose) - D * B.conjTranspose) +
          (((B * D.conjTranspose).trace.re : ℝ) : ℂ) • (1 : TitsComplexMatrix),
        (1 / 2 : ℂ) • ((2 / 3 : ℂ) • D +
          ((B + D).adjugate.conjTranspose - B.adjugate.conjTranspose -
            D.adjugate.conjTranspose))) := by
  rw [jordan_pair, hx, hy]
  have htr : (((1 / 3 : ℂ) • (1 : TitsComplexMatrix)).trace.re : ℂ) = 1 := by
    simp [Matrix.trace_smul, Matrix.trace_one]
  apply Prod.ext
  · simp only [compactSecondTitsProduct, compactSecondTitsProductComplex, Matrix.mul_zero,
      Matrix.zero_mul, zero_add, zero_sub]
  · simp only [compactSecondTitsProduct, compactSecondTitsProductHidden, htr, Matrix.trace_zero,
      Complex.zero_re, Complex.ofReal_zero, zero_smul, sub_zero, Matrix.zero_mul, zero_add]
    congr 2
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, one_smul]
    module

/-! ## Adjugate polarization -/

/-- Polarization of the `3 × 3` adjugate at a scalar matrix. -/
theorem adjugate_polar_scalar (s t : ℂ) (M : TitsComplexMatrix) :
    (s • (1 : TitsComplexMatrix) + t • M).adjugate - (s • (1 : TitsComplexMatrix)).adjugate -
        (t • M).adjugate = (s * t) • (M.trace • (1 : TitsComplexMatrix) - M) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_three, Matrix.trace_fin_three] <;> ring

theorem mul_conjTranspose_of_specialUnitary {W : TitsComplexMatrix}
    (hW : W.conjTranspose * W = 1) : W * W.conjTranspose = 1 :=
  mul_eq_one_comm.mp hW

theorem adjugate_of_specialUnitary {W : TitsComplexMatrix} (hW : W.conjTranspose * W = 1)
    (hd : W.det = 1) : W.adjugate = W.conjTranspose := by
  have h := (adjugate_conjTranspose_eq_iff_det_eq_one W
    (mul_conjTranspose_of_specialUnitary hW)).mpr hd
  have h' := congrArg Matrix.conjTranspose h
  simpa only [Matrix.conjTranspose_conjTranspose] using h'

/-- The hidden polarization at a special unitary `W`, as it enters the native product. -/
theorem polar_specialUnitary {W : TitsComplexMatrix} (hW : W.conjTranspose * W = 1)
    (hd : W.det = 1) (s t : ℂ) (V : TitsComplexMatrix) :
    (s • W + t • V).adjugate.conjTranspose - (s • W).adjugate.conjTranspose -
        (t • V).adjugate.conjTranspose =
      star (s * t) • (star (W.conjTranspose * V).trace • W -
        W * V.conjTranspose * W) := by
  have hWW := mul_conjTranspose_of_specialUnitary hW
  set M := W.conjTranspose * V with hM
  have hV : V = W * M := by rw [hM, ← Matrix.mul_assoc, hWW, Matrix.one_mul]
  have e1 : s • W = W * (s • (1 : TitsComplexMatrix)) := by
    rw [Matrix.mul_smul, Matrix.mul_one]
  have e2 : t • V = W * (t • M) := by rw [Matrix.mul_smul, ← hV]
  have e3 : s • W + t • V = W * (s • (1 : TitsComplexMatrix) + t • M) := by
    rw [Matrix.mul_add, ← e1, ← e2]
  rw [e3, e1, e2, ← Matrix.conjTranspose_sub, ← Matrix.conjTranspose_sub,
    Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
    ← Matrix.sub_mul, ← Matrix.sub_mul, adjugate_polar_scalar,
    adjugate_of_specialUnitary hW hd, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

end CKM.NativeFirstOrder.Elim

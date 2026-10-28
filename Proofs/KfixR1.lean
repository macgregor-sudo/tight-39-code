module

public import A3Interfaces

@[expose] public section

/-!
# KFIX helper: the coordinate and Tits forms of `R1 = T₁ R₀ T₁⁻¹`

`R1` acts on the 27 upper coordinates by an explicit rotation, and in Tits matrix-pair coordinates
by `(a, B) ↦ (g a gᴴ, g B hᴴ)` with `g = diag(1, ω², ω)`, `h = diag(ω, ω², 1)`.
-/


noncomputable section

namespace CKM.NativeFirstOrder

open NativePolynomial CompactAlbert

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega

/-- `g = diag(1, ω², ω)`. -/
def kfG : TitsComplexMatrix := Matrix.diagonal ![1, ω ^ 2, ω]

/-- `h = diag(ω, ω², 1)`. -/
def kfH : TitsComplexMatrix := Matrix.diagonal ![ω, ω ^ 2, 1]

theorem kf_omega_re : (ω).re = -1 / 2 := by
  simp [UnitaryErrorBases.ThreeCycleFourier.omega]

theorem kf_omega_im : (ω).im = Real.sqrt 3 / 2 := by
  simp [UnitaryErrorBases.ThreeCycleFourier.omega]

theorem kf_sqrt3_sq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)

theorem kf_omega_sq_re : (ω ^ 2).re = -1 / 2 := by
  rw [pow_two, Complex.mul_re, kf_omega_re, kf_omega_im]
  nlinarith [kf_sqrt3_sq]

theorem kf_omega_sq_im : (ω ^ 2).im = -(Real.sqrt 3 / 2) := by
  rw [pow_two, Complex.mul_im, kf_omega_re, kf_omega_im]
  ring

/-- The explicit coordinate rotation of `R1` (development numerics: kfix/py/gen_r1.py). -/
def kfR1coord (v : Fin 27 → ℝ) : Fin 27 → ℝ :=
  let c := Real.sqrt 3 / 2
  ![v 0,
    v 1,
    v 2,
    -(v 3) / 2 - (c * v 4),
    c * v 3 - (v 4) / 2,
    v 5,
    v 6,
    -(v 7) / 2 - (c * v 8),
    c * v 7 - (v 8) / 2,
    -(v 9) / 2 - (c * v 10),
    c * v 9 - (v 10) / 2,
    -(v 11) / 2 + c * v 12,
    -(c * v 11) - (v 12) / 2,
    -(v 13) / 2 + c * v 14,
    -(c * v 13) - (v 14) / 2,
    v 15,
    v 16,
    -(v 17) / 2 + c * v 18,
    -(c * v 17) - (v 18) / 2,
    -(v 19) / 2 - (c * v 20),
    c * v 19 - (v 20) / 2,
    -(v 21) / 2 - (c * v 22),
    c * v 21 - (v 22) / 2,
    -(v 23) / 2 + c * v 24,
    -(c * v 23) - (v 24) / 2,
    v 25,
    v 26]

theorem kf_upper_signedTransport (p : Fin 27 → Fin 27) (s : Fin 27 → ℤ) (x : Glennie.Albert) :
    upperCoordinates (signedTransport p s x) = fun k => (s k : ℝ) * upperCoordinates x (p k) := by
  funext k
  change upperCoordinateEquiv (upperCoordinateEquiv.symm _) k = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The coordinate form of `R0`. -/
def kfR0coord (v : Fin 27 → ℝ) : Fin 27 → ℝ :=
  let c := Real.sqrt 3 / 2
  ![v 0, v 1, v 2, v 3, v 4,
    -(v 5) / 2 + c * v 6, -(c * v 5) - v 6 / 2,
    -(v 7) / 2 + c * v 8, -(c * v 7) - v 8 / 2,
    -(v 9) / 2 - c * v 10, c * v 9 - v 10 / 2,
    v 11, v 12,
    -(v 13) / 2 + c * v 14, -(c * v 13) - v 14 / 2,
    -(v 15) / 2 + c * v 16, -(c * v 15) - v 16 / 2,
    -(v 17) / 2 - c * v 18, c * v 17 - v 18 / 2,
    v 19, v 20,
    -(v 21) / 2 + c * v 22, -(c * v 21) - v 22 / 2,
    -(v 23) / 2 + c * v 24, -(c * v 23) - v 24 / 2,
    -(v 25) / 2 - c * v 26, c * v 25 - v 26 / 2]

theorem kf_upper_R0 (x : Glennie.Albert) :
    upperCoordinates (R0 x) = kfR0coord (upperCoordinates x) := by
  have hx : R0 x = fromTitsCoordinates ((toTitsCoordinates x).1, (toTitsCoordinates x).2.1,
      Matrix.of fun i j => (toTitsCoordinates x).2.2 i j * ω) := by
    change fromTitsCoordinates (titsRightMultiply _ (toTitsCoordinates x)) = _
    simp only [titsRightMultiply, LinearMap.coe_mk, AddHom.coe_mk]
    congr 3
    ext i j
    simp [mul_comm]
  rw [hx]
  funext k
  fin_cases k <;>
    simp [upperCoordinates, fromTitsCoordinates, toTitsCoordinates,
      octonionFromTitsRow, octonionToTitsRow, kfR0coord, Glennie.octConj, kf_omega_re, kf_omega_im,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem kfR0coord_0 (v : Fin 27 → ℝ) : kfR0coord v 0 = v 0 := rfl
theorem kfR0coord_1 (v : Fin 27 → ℝ) : kfR0coord v 1 = v 1 := rfl
theorem kfR0coord_2 (v : Fin 27 → ℝ) : kfR0coord v 2 = v 2 := rfl
theorem kfR0coord_3 (v : Fin 27 → ℝ) : kfR0coord v 3 = v 3 := rfl
theorem kfR0coord_4 (v : Fin 27 → ℝ) : kfR0coord v 4 = v 4 := rfl
theorem kfR0coord_5 (v : Fin 27 → ℝ) : kfR0coord v 5 = -(v 5) / 2 + (Real.sqrt 3 / 2) * v 6 := rfl
theorem kfR0coord_6 (v : Fin 27 → ℝ) : kfR0coord v 6 = -((Real.sqrt 3 / 2) * v 5) - v 6 / 2 := rfl
theorem kfR0coord_7 (v : Fin 27 → ℝ) : kfR0coord v 7 = -(v 7) / 2 + (Real.sqrt 3 / 2) * v 8 := rfl
theorem kfR0coord_8 (v : Fin 27 → ℝ) : kfR0coord v 8 = -((Real.sqrt 3 / 2) * v 7) - v 8 / 2 := rfl
theorem kfR0coord_9 (v : Fin 27 → ℝ) : kfR0coord v 9 = -(v 9) / 2 - (Real.sqrt 3 / 2) * v 10 := rfl
theorem kfR0coord_10 (v : Fin 27 → ℝ) : kfR0coord v 10 = (Real.sqrt 3 / 2) * v 9 - v 10 / 2 := rfl
theorem kfR0coord_11 (v : Fin 27 → ℝ) : kfR0coord v 11 = v 11 := rfl
theorem kfR0coord_12 (v : Fin 27 → ℝ) : kfR0coord v 12 = v 12 := rfl
theorem kfR0coord_13 (v : Fin 27 → ℝ) : kfR0coord v 13 = -(v 13) / 2 + (Real.sqrt 3 / 2) * v 14 := rfl
theorem kfR0coord_14 (v : Fin 27 → ℝ) : kfR0coord v 14 = -((Real.sqrt 3 / 2) * v 13) - v 14 / 2 := rfl
theorem kfR0coord_15 (v : Fin 27 → ℝ) : kfR0coord v 15 = -(v 15) / 2 + (Real.sqrt 3 / 2) * v 16 := rfl
theorem kfR0coord_16 (v : Fin 27 → ℝ) : kfR0coord v 16 = -((Real.sqrt 3 / 2) * v 15) - v 16 / 2 := rfl
theorem kfR0coord_17 (v : Fin 27 → ℝ) : kfR0coord v 17 = -(v 17) / 2 - (Real.sqrt 3 / 2) * v 18 := rfl
theorem kfR0coord_18 (v : Fin 27 → ℝ) : kfR0coord v 18 = (Real.sqrt 3 / 2) * v 17 - v 18 / 2 := rfl
theorem kfR0coord_19 (v : Fin 27 → ℝ) : kfR0coord v 19 = v 19 := rfl
theorem kfR0coord_20 (v : Fin 27 → ℝ) : kfR0coord v 20 = v 20 := rfl
theorem kfR0coord_21 (v : Fin 27 → ℝ) : kfR0coord v 21 = -(v 21) / 2 + (Real.sqrt 3 / 2) * v 22 := rfl
theorem kfR0coord_22 (v : Fin 27 → ℝ) : kfR0coord v 22 = -((Real.sqrt 3 / 2) * v 21) - v 22 / 2 := rfl
theorem kfR0coord_23 (v : Fin 27 → ℝ) : kfR0coord v 23 = -(v 23) / 2 + (Real.sqrt 3 / 2) * v 24 := rfl
theorem kfR0coord_24 (v : Fin 27 → ℝ) : kfR0coord v 24 = -((Real.sqrt 3 / 2) * v 23) - v 24 / 2 := rfl
theorem kfR0coord_25 (v : Fin 27 → ℝ) : kfR0coord v 25 = -(v 25) / 2 - (Real.sqrt 3 / 2) * v 26 := rfl
theorem kfR0coord_26 (v : Fin 27 → ℝ) : kfR0coord v 26 = (Real.sqrt 3 / 2) * v 25 - v 26 / 2 := rfl
theorem kfR1coord_0 (v : Fin 27 → ℝ) : kfR1coord v 0 = v 0 := rfl
theorem kfR1coord_1 (v : Fin 27 → ℝ) : kfR1coord v 1 = v 1 := rfl
theorem kfR1coord_2 (v : Fin 27 → ℝ) : kfR1coord v 2 = v 2 := rfl
theorem kfR1coord_3 (v : Fin 27 → ℝ) : kfR1coord v 3 = -(v 3) / 2 - ((Real.sqrt 3 / 2) * v 4) := rfl
theorem kfR1coord_4 (v : Fin 27 → ℝ) : kfR1coord v 4 = (Real.sqrt 3 / 2) * v 3 - (v 4) / 2 := rfl
theorem kfR1coord_5 (v : Fin 27 → ℝ) : kfR1coord v 5 = v 5 := rfl
theorem kfR1coord_6 (v : Fin 27 → ℝ) : kfR1coord v 6 = v 6 := rfl
theorem kfR1coord_7 (v : Fin 27 → ℝ) : kfR1coord v 7 = -(v 7) / 2 - ((Real.sqrt 3 / 2) * v 8) := rfl
theorem kfR1coord_8 (v : Fin 27 → ℝ) : kfR1coord v 8 = (Real.sqrt 3 / 2) * v 7 - (v 8) / 2 := rfl
theorem kfR1coord_9 (v : Fin 27 → ℝ) : kfR1coord v 9 = -(v 9) / 2 - ((Real.sqrt 3 / 2) * v 10) := rfl
theorem kfR1coord_10 (v : Fin 27 → ℝ) : kfR1coord v 10 = (Real.sqrt 3 / 2) * v 9 - (v 10) / 2 := rfl
theorem kfR1coord_11 (v : Fin 27 → ℝ) : kfR1coord v 11 = -(v 11) / 2 + (Real.sqrt 3 / 2) * v 12 := rfl
theorem kfR1coord_12 (v : Fin 27 → ℝ) : kfR1coord v 12 = -((Real.sqrt 3 / 2) * v 11) - (v 12) / 2 := rfl
theorem kfR1coord_13 (v : Fin 27 → ℝ) : kfR1coord v 13 = -(v 13) / 2 + (Real.sqrt 3 / 2) * v 14 := rfl
theorem kfR1coord_14 (v : Fin 27 → ℝ) : kfR1coord v 14 = -((Real.sqrt 3 / 2) * v 13) - (v 14) / 2 := rfl
theorem kfR1coord_15 (v : Fin 27 → ℝ) : kfR1coord v 15 = v 15 := rfl
theorem kfR1coord_16 (v : Fin 27 → ℝ) : kfR1coord v 16 = v 16 := rfl
theorem kfR1coord_17 (v : Fin 27 → ℝ) : kfR1coord v 17 = -(v 17) / 2 + (Real.sqrt 3 / 2) * v 18 := rfl
theorem kfR1coord_18 (v : Fin 27 → ℝ) : kfR1coord v 18 = -((Real.sqrt 3 / 2) * v 17) - (v 18) / 2 := rfl
theorem kfR1coord_19 (v : Fin 27 → ℝ) : kfR1coord v 19 = -(v 19) / 2 - ((Real.sqrt 3 / 2) * v 20) := rfl
theorem kfR1coord_20 (v : Fin 27 → ℝ) : kfR1coord v 20 = (Real.sqrt 3 / 2) * v 19 - (v 20) / 2 := rfl
theorem kfR1coord_21 (v : Fin 27 → ℝ) : kfR1coord v 21 = -(v 21) / 2 - ((Real.sqrt 3 / 2) * v 22) := rfl
theorem kfR1coord_22 (v : Fin 27 → ℝ) : kfR1coord v 22 = (Real.sqrt 3 / 2) * v 21 - (v 22) / 2 := rfl
theorem kfR1coord_23 (v : Fin 27 → ℝ) : kfR1coord v 23 = -(v 23) / 2 + (Real.sqrt 3 / 2) * v 24 := rfl
theorem kfR1coord_24 (v : Fin 27 → ℝ) : kfR1coord v 24 = -((Real.sqrt 3 / 2) * v 23) - (v 24) / 2 := rfl
theorem kfR1coord_25 (v : Fin 27 → ℝ) : kfR1coord v 25 = v 25 := rfl
theorem kfR1coord_26 (v : Fin 27 → ℝ) : kfR1coord v 26 = v 26 := rfl

theorem kf_T1p_0 : TitsS.Transport.T1p 0 = 0 := by decide
theorem kf_T1pinv_0 : TitsS.Transport.T1pinv 0 = 0 := by decide
theorem kf_T1s_0 : TitsS.Transport.T1s 0 = 1 := by decide
theorem kf_T1si_0 : TitsS.Transport.T1si 0 = 1 := by decide
theorem kf_T1p_1 : TitsS.Transport.T1p 1 = 1 := by decide
theorem kf_T1pinv_1 : TitsS.Transport.T1pinv 1 = 1 := by decide
theorem kf_T1s_1 : TitsS.Transport.T1s 1 = 1 := by decide
theorem kf_T1si_1 : TitsS.Transport.T1si 1 = 1 := by decide
theorem kf_T1p_2 : TitsS.Transport.T1p 2 = 2 := by decide
theorem kf_T1pinv_2 : TitsS.Transport.T1pinv 2 = 2 := by decide
theorem kf_T1s_2 : TitsS.Transport.T1s 2 = 1 := by decide
theorem kf_T1si_2 : TitsS.Transport.T1si 2 = 1 := by decide
theorem kf_T1p_3 : TitsS.Transport.T1p 3 = 5 := by decide
theorem kf_T1pinv_3 : TitsS.Transport.T1pinv 3 = 5 := by decide
theorem kf_T1s_3 : TitsS.Transport.T1s 3 = -1 := by decide
theorem kf_T1si_3 : TitsS.Transport.T1si 3 = 1 := by decide
theorem kf_T1p_4 : TitsS.Transport.T1p 4 = 6 := by decide
theorem kf_T1pinv_4 : TitsS.Transport.T1pinv 4 = 6 := by decide
theorem kf_T1s_4 : TitsS.Transport.T1s 4 = 1 := by decide
theorem kf_T1si_4 : TitsS.Transport.T1si 4 = 1 := by decide
theorem kf_T1p_5 : TitsS.Transport.T1p 5 = 3 := by decide
theorem kf_T1pinv_5 : TitsS.Transport.T1pinv 5 = 3 := by decide
theorem kf_T1s_5 : TitsS.Transport.T1s 5 = 1 := by decide
theorem kf_T1si_5 : TitsS.Transport.T1si 5 = -1 := by decide
theorem kf_T1p_6 : TitsS.Transport.T1p 6 = 4 := by decide
theorem kf_T1pinv_6 : TitsS.Transport.T1pinv 6 = 4 := by decide
theorem kf_T1s_6 : TitsS.Transport.T1s 6 = 1 := by decide
theorem kf_T1si_6 : TitsS.Transport.T1si 6 = 1 := by decide
theorem kf_T1p_7 : TitsS.Transport.T1p 7 = 9 := by decide
theorem kf_T1pinv_7 : TitsS.Transport.T1pinv 7 = 9 := by decide
theorem kf_T1s_7 : TitsS.Transport.T1s 7 = 1 := by decide
theorem kf_T1si_7 : TitsS.Transport.T1si 7 = -1 := by decide
theorem kf_T1p_8 : TitsS.Transport.T1p 8 = 10 := by decide
theorem kf_T1pinv_8 : TitsS.Transport.T1pinv 8 = 10 := by decide
theorem kf_T1s_8 : TitsS.Transport.T1s 8 = 1 := by decide
theorem kf_T1si_8 : TitsS.Transport.T1si 8 = 1 := by decide
theorem kf_T1p_9 : TitsS.Transport.T1p 9 = 7 := by decide
theorem kf_T1pinv_9 : TitsS.Transport.T1pinv 9 = 7 := by decide
theorem kf_T1s_9 : TitsS.Transport.T1s 9 = -1 := by decide
theorem kf_T1si_9 : TitsS.Transport.T1si 9 = 1 := by decide
theorem kf_T1p_10 : TitsS.Transport.T1p 10 = 8 := by decide
theorem kf_T1pinv_10 : TitsS.Transport.T1pinv 10 = 8 := by decide
theorem kf_T1s_10 : TitsS.Transport.T1s 10 = 1 := by decide
theorem kf_T1si_10 : TitsS.Transport.T1si 10 = 1 := by decide
theorem kf_T1p_11 : TitsS.Transport.T1p 11 = 15 := by decide
theorem kf_T1pinv_11 : TitsS.Transport.T1pinv 11 = 15 := by decide
theorem kf_T1s_11 : TitsS.Transport.T1s 11 = -1 := by decide
theorem kf_T1si_11 : TitsS.Transport.T1si 11 = 1 := by decide
theorem kf_T1p_12 : TitsS.Transport.T1p 12 = 16 := by decide
theorem kf_T1pinv_12 : TitsS.Transport.T1pinv 12 = 16 := by decide
theorem kf_T1s_12 : TitsS.Transport.T1s 12 = -1 := by decide
theorem kf_T1si_12 : TitsS.Transport.T1si 12 = -1 := by decide
theorem kf_T1p_13 : TitsS.Transport.T1p 13 = 17 := by decide
theorem kf_T1pinv_13 : TitsS.Transport.T1pinv 13 = 17 := by decide
theorem kf_T1s_13 : TitsS.Transport.T1s 13 = -1 := by decide
theorem kf_T1si_13 : TitsS.Transport.T1si 13 = 1 := by decide
theorem kf_T1p_14 : TitsS.Transport.T1p 14 = 18 := by decide
theorem kf_T1pinv_14 : TitsS.Transport.T1pinv 14 = 18 := by decide
theorem kf_T1s_14 : TitsS.Transport.T1s 14 = 1 := by decide
theorem kf_T1si_14 : TitsS.Transport.T1si 14 = 1 := by decide
theorem kf_T1p_15 : TitsS.Transport.T1p 15 = 11 := by decide
theorem kf_T1pinv_15 : TitsS.Transport.T1pinv 15 = 11 := by decide
theorem kf_T1s_15 : TitsS.Transport.T1s 15 = 1 := by decide
theorem kf_T1si_15 : TitsS.Transport.T1si 15 = -1 := by decide
theorem kf_T1p_16 : TitsS.Transport.T1p 16 = 12 := by decide
theorem kf_T1pinv_16 : TitsS.Transport.T1pinv 16 = 12 := by decide
theorem kf_T1s_16 : TitsS.Transport.T1s 16 = -1 := by decide
theorem kf_T1si_16 : TitsS.Transport.T1si 16 = -1 := by decide
theorem kf_T1p_17 : TitsS.Transport.T1p 17 = 13 := by decide
theorem kf_T1pinv_17 : TitsS.Transport.T1pinv 17 = 13 := by decide
theorem kf_T1s_17 : TitsS.Transport.T1s 17 = 1 := by decide
theorem kf_T1si_17 : TitsS.Transport.T1si 17 = -1 := by decide
theorem kf_T1p_18 : TitsS.Transport.T1p 18 = 14 := by decide
theorem kf_T1pinv_18 : TitsS.Transport.T1pinv 18 = 14 := by decide
theorem kf_T1s_18 : TitsS.Transport.T1s 18 = 1 := by decide
theorem kf_T1si_18 : TitsS.Transport.T1si 18 = 1 := by decide
theorem kf_T1p_19 : TitsS.Transport.T1p 19 = 25 := by decide
theorem kf_T1pinv_19 : TitsS.Transport.T1pinv 19 = 25 := by decide
theorem kf_T1s_19 : TitsS.Transport.T1s 19 = -1 := by decide
theorem kf_T1si_19 : TitsS.Transport.T1si 19 = -1 := by decide
theorem kf_T1p_20 : TitsS.Transport.T1p 20 = 26 := by decide
theorem kf_T1pinv_20 : TitsS.Transport.T1pinv 20 = 26 := by decide
theorem kf_T1s_20 : TitsS.Transport.T1s 20 = -1 := by decide
theorem kf_T1si_20 : TitsS.Transport.T1si 20 = 1 := by decide
theorem kf_T1p_21 : TitsS.Transport.T1p 21 = 23 := by decide
theorem kf_T1pinv_21 : TitsS.Transport.T1pinv 21 = 23 := by decide
theorem kf_T1s_21 : TitsS.Transport.T1s 21 = 1 := by decide
theorem kf_T1si_21 : TitsS.Transport.T1si 21 = 1 := by decide
theorem kf_T1p_22 : TitsS.Transport.T1p 22 = 24 := by decide
theorem kf_T1pinv_22 : TitsS.Transport.T1pinv 22 = 24 := by decide
theorem kf_T1s_22 : TitsS.Transport.T1s 22 = -1 := by decide
theorem kf_T1si_22 : TitsS.Transport.T1si 22 = 1 := by decide
theorem kf_T1p_23 : TitsS.Transport.T1p 23 = 21 := by decide
theorem kf_T1pinv_23 : TitsS.Transport.T1pinv 23 = 21 := by decide
theorem kf_T1s_23 : TitsS.Transport.T1s 23 = 1 := by decide
theorem kf_T1si_23 : TitsS.Transport.T1si 23 = 1 := by decide
theorem kf_T1p_24 : TitsS.Transport.T1p 24 = 22 := by decide
theorem kf_T1pinv_24 : TitsS.Transport.T1pinv 24 = 22 := by decide
theorem kf_T1s_24 : TitsS.Transport.T1s 24 = 1 := by decide
theorem kf_T1si_24 : TitsS.Transport.T1si 24 = -1 := by decide
theorem kf_T1p_25 : TitsS.Transport.T1p 25 = 19 := by decide
theorem kf_T1pinv_25 : TitsS.Transport.T1pinv 25 = 19 := by decide
theorem kf_T1s_25 : TitsS.Transport.T1s 25 = -1 := by decide
theorem kf_T1si_25 : TitsS.Transport.T1si 25 = -1 := by decide
theorem kf_T1p_26 : TitsS.Transport.T1p 26 = 20 := by decide
theorem kf_T1pinv_26 : TitsS.Transport.T1pinv 26 = 20 := by decide
theorem kf_T1s_26 : TitsS.Transport.T1s 26 = 1 := by decide
theorem kf_T1si_26 : TitsS.Transport.T1si 26 = -1 := by decide

theorem kf_upper_R1_c0 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 0 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 0) = kfR1coord u 0 := by
  rw [kf_T1s_0, kf_T1p_0, kfR0coord_0]
  rw [kf_T1si_0, kf_T1pinv_0]
  rw [kfR1coord_0]
  push_cast
  ring

theorem kf_upper_R1_c1 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 1 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 1) = kfR1coord u 1 := by
  rw [kf_T1s_1, kf_T1p_1, kfR0coord_1]
  rw [kf_T1si_1, kf_T1pinv_1]
  rw [kfR1coord_1]
  push_cast
  ring

theorem kf_upper_R1_c2 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 2 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 2) = kfR1coord u 2 := by
  rw [kf_T1s_2, kf_T1p_2, kfR0coord_2]
  rw [kf_T1si_2, kf_T1pinv_2]
  rw [kfR1coord_2]
  push_cast
  ring

theorem kf_upper_R1_c3 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 3 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 3) = kfR1coord u 3 := by
  rw [kf_T1s_3, kf_T1p_3, kfR0coord_5]
  rw [kf_T1si_5, kf_T1pinv_5, kf_T1si_6, kf_T1pinv_6]
  rw [kfR1coord_3]
  push_cast
  ring

theorem kf_upper_R1_c4 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 4 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 4) = kfR1coord u 4 := by
  rw [kf_T1s_4, kf_T1p_4, kfR0coord_6]
  rw [kf_T1si_5, kf_T1pinv_5, kf_T1si_6, kf_T1pinv_6]
  rw [kfR1coord_4]
  push_cast
  ring

theorem kf_upper_R1_c5 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 5 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 5) = kfR1coord u 5 := by
  rw [kf_T1s_5, kf_T1p_5, kfR0coord_3]
  rw [kf_T1si_3, kf_T1pinv_3]
  rw [kfR1coord_5]
  push_cast
  ring

theorem kf_upper_R1_c6 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 6 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 6) = kfR1coord u 6 := by
  rw [kf_T1s_6, kf_T1p_6, kfR0coord_4]
  rw [kf_T1si_4, kf_T1pinv_4]
  rw [kfR1coord_6]
  push_cast
  ring

theorem kf_upper_R1_c7 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 7 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 7) = kfR1coord u 7 := by
  rw [kf_T1s_7, kf_T1p_7, kfR0coord_9]
  rw [kf_T1si_9, kf_T1pinv_9, kf_T1si_10, kf_T1pinv_10]
  rw [kfR1coord_7]
  push_cast
  ring

theorem kf_upper_R1_c8 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 8 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 8) = kfR1coord u 8 := by
  rw [kf_T1s_8, kf_T1p_8, kfR0coord_10]
  rw [kf_T1si_9, kf_T1pinv_9, kf_T1si_10, kf_T1pinv_10]
  rw [kfR1coord_8]
  push_cast
  ring

theorem kf_upper_R1_c9 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 9 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 9) = kfR1coord u 9 := by
  rw [kf_T1s_9, kf_T1p_9, kfR0coord_7]
  rw [kf_T1si_7, kf_T1pinv_7, kf_T1si_8, kf_T1pinv_8]
  rw [kfR1coord_9]
  push_cast
  ring

theorem kf_upper_R1_c10 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 10 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 10) = kfR1coord u 10 := by
  rw [kf_T1s_10, kf_T1p_10, kfR0coord_8]
  rw [kf_T1si_7, kf_T1pinv_7, kf_T1si_8, kf_T1pinv_8]
  rw [kfR1coord_10]
  push_cast
  ring

theorem kf_upper_R1_c11 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 11 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 11) = kfR1coord u 11 := by
  rw [kf_T1s_11, kf_T1p_11, kfR0coord_15]
  rw [kf_T1si_15, kf_T1pinv_15, kf_T1si_16, kf_T1pinv_16]
  rw [kfR1coord_11]
  push_cast
  ring

theorem kf_upper_R1_c12 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 12 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 12) = kfR1coord u 12 := by
  rw [kf_T1s_12, kf_T1p_12, kfR0coord_16]
  rw [kf_T1si_15, kf_T1pinv_15, kf_T1si_16, kf_T1pinv_16]
  rw [kfR1coord_12]
  push_cast
  ring

theorem kf_upper_R1_c13 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 13 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 13) = kfR1coord u 13 := by
  rw [kf_T1s_13, kf_T1p_13, kfR0coord_17]
  rw [kf_T1si_17, kf_T1pinv_17, kf_T1si_18, kf_T1pinv_18]
  rw [kfR1coord_13]
  push_cast
  ring

theorem kf_upper_R1_c14 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 14 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 14) = kfR1coord u 14 := by
  rw [kf_T1s_14, kf_T1p_14, kfR0coord_18]
  rw [kf_T1si_17, kf_T1pinv_17, kf_T1si_18, kf_T1pinv_18]
  rw [kfR1coord_14]
  push_cast
  ring

theorem kf_upper_R1_c15 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 15 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 15) = kfR1coord u 15 := by
  rw [kf_T1s_15, kf_T1p_15, kfR0coord_11]
  rw [kf_T1si_11, kf_T1pinv_11]
  rw [kfR1coord_15]
  push_cast
  ring

theorem kf_upper_R1_c16 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 16 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 16) = kfR1coord u 16 := by
  rw [kf_T1s_16, kf_T1p_16, kfR0coord_12]
  rw [kf_T1si_12, kf_T1pinv_12]
  rw [kfR1coord_16]
  push_cast
  ring

theorem kf_upper_R1_c17 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 17 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 17) = kfR1coord u 17 := by
  rw [kf_T1s_17, kf_T1p_17, kfR0coord_13]
  rw [kf_T1si_13, kf_T1pinv_13, kf_T1si_14, kf_T1pinv_14]
  rw [kfR1coord_17]
  push_cast
  ring

theorem kf_upper_R1_c18 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 18 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 18) = kfR1coord u 18 := by
  rw [kf_T1s_18, kf_T1p_18, kfR0coord_14]
  rw [kf_T1si_13, kf_T1pinv_13, kf_T1si_14, kf_T1pinv_14]
  rw [kfR1coord_18]
  push_cast
  ring

theorem kf_upper_R1_c19 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 19 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 19) = kfR1coord u 19 := by
  rw [kf_T1s_19, kf_T1p_19, kfR0coord_25]
  rw [kf_T1si_25, kf_T1pinv_25, kf_T1si_26, kf_T1pinv_26]
  rw [kfR1coord_19]
  push_cast
  ring

theorem kf_upper_R1_c20 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 20 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 20) = kfR1coord u 20 := by
  rw [kf_T1s_20, kf_T1p_20, kfR0coord_26]
  rw [kf_T1si_25, kf_T1pinv_25, kf_T1si_26, kf_T1pinv_26]
  rw [kfR1coord_20]
  push_cast
  ring

theorem kf_upper_R1_c21 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 21 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 21) = kfR1coord u 21 := by
  rw [kf_T1s_21, kf_T1p_21, kfR0coord_23]
  rw [kf_T1si_23, kf_T1pinv_23, kf_T1si_24, kf_T1pinv_24]
  rw [kfR1coord_21]
  push_cast
  ring

theorem kf_upper_R1_c22 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 22 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 22) = kfR1coord u 22 := by
  rw [kf_T1s_22, kf_T1p_22, kfR0coord_24]
  rw [kf_T1si_23, kf_T1pinv_23, kf_T1si_24, kf_T1pinv_24]
  rw [kfR1coord_22]
  push_cast
  ring

theorem kf_upper_R1_c23 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 23 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 23) = kfR1coord u 23 := by
  rw [kf_T1s_23, kf_T1p_23, kfR0coord_21]
  rw [kf_T1si_21, kf_T1pinv_21, kf_T1si_22, kf_T1pinv_22]
  rw [kfR1coord_23]
  push_cast
  ring

theorem kf_upper_R1_c24 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 24 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 24) = kfR1coord u 24 := by
  rw [kf_T1s_24, kf_T1p_24, kfR0coord_22]
  rw [kf_T1si_21, kf_T1pinv_21, kf_T1si_22, kf_T1pinv_22]
  rw [kfR1coord_24]
  push_cast
  ring

theorem kf_upper_R1_c25 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 25 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 25) = kfR1coord u 25 := by
  rw [kf_T1s_25, kf_T1p_25, kfR0coord_19]
  rw [kf_T1si_19, kf_T1pinv_19]
  rw [kfR1coord_25]
  push_cast
  ring

theorem kf_upper_R1_c26 (u : Fin 27 → ℝ) :
    ((TitsS.Transport.T1s 26 : ℤ) : ℝ) * kfR0coord (fun j => ((TitsS.Transport.T1si j : ℤ) : ℝ) *
      u (TitsS.Transport.T1pinv j)) (TitsS.Transport.T1p 26) = kfR1coord u 26 := by
  rw [kf_T1s_26, kf_T1p_26, kfR0coord_20]
  rw [kf_T1si_20, kf_T1pinv_20]
  rw [kfR1coord_26]
  push_cast
  ring

theorem kf_upper_R1 (x : Glennie.Albert) :
    upperCoordinates (R1 x) = kfR1coord (upperCoordinates x) := by
  have h1 : R1 x = signedTransport TitsS.Transport.T1p TitsS.Transport.T1s
      (R0 (signedTransport TitsS.Transport.T1pinv TitsS.Transport.T1si x)) := rfl
  rw [h1, kf_upper_signedTransport, kf_upper_R0, kf_upper_signedTransport]
  funext k
  fin_cases k
  exacts [kf_upper_R1_c0 _, kf_upper_R1_c1 _, kf_upper_R1_c2 _, kf_upper_R1_c3 _, kf_upper_R1_c4 _, kf_upper_R1_c5 _, kf_upper_R1_c6 _, kf_upper_R1_c7 _, kf_upper_R1_c8 _, kf_upper_R1_c9 _, kf_upper_R1_c10 _, kf_upper_R1_c11 _, kf_upper_R1_c12 _, kf_upper_R1_c13 _, kf_upper_R1_c14 _, kf_upper_R1_c15 _, kf_upper_R1_c16 _, kf_upper_R1_c17 _, kf_upper_R1_c18 _, kf_upper_R1_c19 _, kf_upper_R1_c20 _, kf_upper_R1_c21 _, kf_upper_R1_c22 _, kf_upper_R1_c23 _, kf_upper_R1_c24 _, kf_upper_R1_c25 _, kf_upper_R1_c26 _]


/-! ## Tits pair form -/

/-- The Tits matrix pair as an explicit function of the 27 upper coordinates. -/
def kfPairExpl (v : Fin 27 → ℝ) : TitsMatrixPair :=
  (!![((v 0 : ℝ) : ℂ), ⟨v 3, v 4⟩, star (⟨v 11, -v 12⟩ : ℂ);
      star (⟨v 3, v 4⟩ : ℂ), ((v 1 : ℝ) : ℂ), ⟨v 19, v 20⟩;
      ⟨v 11, -v 12⟩, star (⟨v 19, v 20⟩ : ℂ), ((v 2 : ℝ) : ℂ)],
   !![⟨-v 21, v 22⟩, ⟨-v 23, v 24⟩, ⟨-v 25, -v 26⟩;
      ⟨v 13, -v 14⟩, ⟨v 15, -v 16⟩, ⟨v 17, v 18⟩;
      ⟨-v 5, v 6⟩, ⟨-v 7, v 8⟩, ⟨-v 9, -v 10⟩])

-- This entrywise coordinate identity needs a bounded fourfold kernel-check budget.
-- The option applies only to this declaration; the proof and host limits are unchanged.
set_option maxHeartbeats 800000 in
theorem kf_pair_expl (y : Glennie.Albert) :
    nativeTitsMatrixPair y = kfPairExpl (upperCoordinates y) := by
  refine Prod.ext ?_ ?_ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | (apply Complex.ext <;>
        simp [nativeTitsMatrixPair, titsMatrixPairLinear, compactTitsCoordinateEquiv, toMatrixPair,
          hermitianMatrix, toTitsCoordinates, octonionToTitsRow, Glennie.octConj, upperCoordinates,
          kfPairExpl])

/-- `g` conjugation is entrywise multiplication by powers of `ω`. -/
def kfGG : Fin 3 → Fin 3 → ℂ := ![![1, ω, ω ^ 2], ![ω ^ 2, 1, ω], ![ω, ω ^ 2, 1]]
/-- `X ↦ g X hᴴ` is entrywise multiplication by powers of `ω`. -/
def kfGH : Fin 3 → Fin 3 → ℂ := ![![ω ^ 2, ω, 1], ![ω, 1, ω ^ 2], ![1, ω ^ 2, ω]]

theorem kf_star_omega : star ω = ω ^ 2 := by
  apply Complex.ext <;> simp [kf_omega_re, kf_omega_im, kf_omega_sq_re, kf_omega_sq_im]

theorem kf_omega_cube : ω ^ 3 = 1 := UnitaryErrorBases.ThreeCycleFourier.omega_cube

theorem kf_omega_four : ω ^ 4 = ω := by
  rw [show (4 : ℕ) = 3 + 1 by rfl, pow_succ, kf_omega_cube, one_mul]

theorem kf_omega_five : ω ^ 5 = ω ^ 2 := by
  rw [show (5 : ℕ) = 3 + 2 by rfl, pow_add, kf_omega_cube, one_mul]

theorem kf_omega_six : ω ^ 6 = 1 := by
  rw [show (6 : ℕ) = 3 + 3 by rfl, pow_add, kf_omega_cube, one_mul]

theorem kf_G_conj (a : TitsComplexMatrix) :
    kfG * a * kfG.conjTranspose = Matrix.of fun i j => kfGG i j * a i j := by
  ext i j
  rw [kfG, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;>
    simp [kfGG, kf_star_omega, star_pow] <;> ring_nf <;>
    (try simp only [kf_omega_cube, kf_omega_four, kf_omega_five, kf_omega_six, one_mul])

theorem kf_GH_conj (a : TitsComplexMatrix) :
    kfG * a * kfH.conjTranspose = Matrix.of fun i j => kfGH i j * a i j := by
  ext i j
  rw [kfG, kfH, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;>
    simp [kfGH, kf_star_omega, star_pow] <;> ring_nf <;>
    (try simp only [kf_omega_cube, kf_omega_four, kf_omega_five, kf_omega_six, one_mul])


/-- MASTER §6.5: `R1` acts in Tits coordinates as `(a, B) ↦ (g a gᴴ, g B hᴴ)`. -/
theorem kf_pair_R1 (x : Glennie.Albert) :
    nativeTitsMatrixPair (R1 x) =
      (kfG * (nativeTitsMatrixPair x).1 * kfG.conjTranspose,
        kfG * (nativeTitsMatrixPair x).2 * kfH.conjTranspose) := by
  rw [kf_pair_expl (R1 x), kf_pair_expl x, kf_upper_R1, kf_G_conj, kf_GH_conj]
  generalize upperCoordinates x = u
  unfold kfPairExpl
  rw [kfR1coord_0, kfR1coord_1, kfR1coord_2, kfR1coord_3, kfR1coord_4, kfR1coord_5, kfR1coord_6, kfR1coord_7, kfR1coord_8, kfR1coord_9, kfR1coord_10, kfR1coord_11, kfR1coord_12, kfR1coord_13, kfR1coord_14, kfR1coord_15, kfR1coord_16, kfR1coord_17, kfR1coord_18, kfR1coord_19, kfR1coord_20, kfR1coord_21, kfR1coord_22, kfR1coord_23, kfR1coord_24, kfR1coord_25, kfR1coord_26]
  refine Prod.ext ?_ ?_ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [kfGG, kfGH] <;> apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, kf_omega_re, kf_omega_im, kf_omega_sq_re,
      kf_omega_sq_im] <;> ring

end CKM.NativeFirstOrder

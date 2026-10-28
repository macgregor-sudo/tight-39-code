module

public import A3ElimFixed

@[expose] public section

/-!
# Elimination helpers IV: the native rows read in Tits coordinates

Row-by-row translations used by both directions of the elimination: quartet rows, the
hidden-hidden cross-pair rows, the automatic quartet-hidden rows, and the cube-root shift.
-/

noncomputable section

namespace CKM.NativeFirstOrder.Elim

open CompactAlbert

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega
local notation "πp" => CompactAlbert.nativeTitsMatrixPair

/-- `R0` with the hidden outcome shift `t ↦ t + 2` acts trivially on `ω^t M / 3`. -/
theorem omega_shift (a : Fin 3) (M : TitsComplexMatrix) :
    ω • ((1 / 3 : ℂ) • ((ω ^ (a + 2).val) • M)) = (1 / 3 : ℂ) • ((ω ^ a.val) • M) := by
  have hs : ω * ω ^ (a + 2).val = ω ^ a.val := by
    obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
    · show ω * ω ^ 2 = ω ^ 0
      rw [← pow_succ', UnitaryErrorBases.ThreeCycleFourier.omega_cube, pow_zero]
    · show ω * ω ^ 0 = ω ^ 1
      rw [pow_zero, mul_one, pow_one]
    · show ω * ω ^ 1 = ω ^ 2
      rw [pow_one, pow_two]
  rw [← hs, ← smul_smul]
  exact smul_comm _ _ _

/-- The trace of a tangent variation of an idempotent vanishes. -/
theorem trace_eq_zero_of_tangent {q d : TitsComplexMatrix} (hq : q * q = q)
    (hd : q * d + d * q = d) : d.trace = 0 := by
  have e1 : q * (d * q) = 0 := by
    have h := congrArg (· * q) hd
    simp only [Matrix.add_mul, Matrix.mul_assoc, hq] at h
    rwa [add_eq_right] at h
  have e2 : (q * d).trace = 0 := by
    calc (q * d).trace = ((q * q) * d).trace := by rw [hq]
      _ = (q * (q * d)).trace := by rw [Matrix.mul_assoc]
      _ = ((q * d) * q).trace := Matrix.trace_mul_comm _ _
      _ = 0 := by rw [Matrix.mul_assoc, e1, Matrix.trace_zero]
  calc d.trace = (q * d + d * q).trace := by rw [hd]
    _ = (q * d).trace + (q * d).trace := by rw [Matrix.trace_add, Matrix.trace_mul_comm d q]
    _ = 0 := by rw [e2, add_zero]

theorem quartet_idem_iff {x u : Glennie.Albert} {qm dm : TitsComplexMatrix}
    (hx : πp x = (qm, 0)) (hu : πp u = (dm, 0)) :
    (2 : ℝ) • Glennie.jordan x u = u ↔ qm * dm + dm * qm = dm := by
  rw [← pair_inj, map_smul, jordan_pair_visible x u hx hu, hu, Prod.smul_mk, smul_zero,
    two_smul_half, Prod.mk.injEq]
  exact and_iff_left rfl

theorem quartet_within_iff {x1 x2 u1 u2 : Glennie.Albert} {q1 q2 d1 d2 : TitsComplexMatrix}
    (hx1 : πp x1 = (q1, 0)) (hx2 : πp x2 = (q2, 0)) (hu1 : πp u1 = (d1, 0))
    (hu2 : πp u2 = (d2, 0)) :
    Glennie.jordan x1 u2 + Glennie.jordan u1 x2 = 0 ↔
      q1 * d2 + d2 * q1 + d1 * q2 + q2 * d1 = 0 := by
  rw [← pair_eq_zero, map_add, jordan_pair_visible x1 u2 hx1 hu2,
    jordan_pair_visible u1 x2 hu1 hx2, Prod.mk_add_mk, add_zero, Prod.mk_eq_zero, and_iff_left rfl,
    ← smul_add, smul_eq_zero, or_iff_right (by norm_num)]
  simp only [add_assoc]

theorem quartet_cross_eq {x u y v : Glennie.Albert} {q1 d1 q2 d2 : TitsComplexMatrix}
    (hx : πp x = (q1, 0)) (hu : πp u = (d1, 0)) (hy : πp y = (q2, 0)) (hv : πp v = (d2, 0)) :
    Glennie.trace (Glennie.jordan x v) + Glennie.trace (Glennie.jordan u y) =
      (q1 * d2 + d1 * q2).trace.re := by
  rw [trace_jordan_pair, trace_jordan_pair, hx, hu, hy, hv]
  simp [Matrix.trace_add]

theorem quartet_hidden_cross_eq_zero {x u y v : Glennie.Albert} {qm dm B D : TitsComplexMatrix}
    (hx : πp x = (qm, 0)) (hu : πp u = (dm, 0))
    (hy : πp y = ((1 / 3 : ℂ) • (1 : TitsComplexMatrix), B)) (hv : πp v = (0, D))
    (hd : dm.trace = 0) :
    Glennie.trace (Glennie.jordan x v) + Glennie.trace (Glennie.jordan u y) = 0 := by
  rw [trace_jordan_pair, trace_jordan_pair, hx, hu, hy, hv]
  simp [Matrix.trace_smul, hd]

theorem scaled_mul_conjTranspose (c e : ℂ) (A D : TitsComplexMatrix) :
    ((1 / 3 : ℂ) • (c • A)) * ((1 / 3 : ℂ) • (e • D)).conjTranspose =
      ((1 / 9 : ℂ) * (c * star e)) • (A * D.conjTranspose) := by
  have hstar3 : star (1 / 3 : ℂ) = 1 / 3 := by
    apply Complex.ext <;> simp
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_mul,
    hstar3]
  congr 1
  ring

theorem hidden_cross_eq {x u y v : Glennie.Albert} {c e : ℂ} {A C B D : TitsComplexMatrix}
    (hx : πp x = ((1 / 3 : ℂ) • (1 : TitsComplexMatrix), (1 / 3 : ℂ) • (c • A)))
    (hu : πp u = (0, (1 / 3 : ℂ) • (c • C)))
    (hy : πp y = ((1 / 3 : ℂ) • (1 : TitsComplexMatrix), (1 / 3 : ℂ) • (e • B)))
    (hv : πp v = (0, (1 / 3 : ℂ) • (e • D))) :
    Glennie.trace (Glennie.jordan x v) + Glennie.trace (Glennie.jordan u y) =
      2 * (((1 / 9 : ℂ) * (c * star e)) * (A * D.conjTranspose + C * B.conjTranspose).trace).re := by
  rw [trace_jordan_pair, trace_jordan_pair, hx, hu, hy, hv]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re, zero_add,
    scaled_mul_conjTranspose, Matrix.trace_smul, smul_eq_mul, Matrix.trace_add, mul_add,
    Complex.add_re]

/-- The complex pair row of `SatisfiesFirstOrder`, as the conjugate of the native cross quantity. -/
theorem pair_row_eq_star (A C B D : TitsComplexMatrix) :
    (C.conjTranspose * B + A.conjTranspose * D).trace =
      star (A * D.conjTranspose + C * B.conjTranspose).trace := by
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_mul_comm D, Matrix.trace_mul_comm B, add_comm]

/-- The same row, read from the other ordering of the two frames. -/
theorem pair_row_eq_swap (A C B D : TitsComplexMatrix) :
    (C.conjTranspose * B + A.conjTranspose * D).trace =
      (B * C.conjTranspose + D * A.conjTranspose).trace := by
  rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_mul_comm B, Matrix.trace_mul_comm D]

end CKM.NativeFirstOrder.Elim

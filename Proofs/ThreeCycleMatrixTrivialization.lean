module

public import ThreeCycleMatrixSupport
public import Mathlib.Tactic.Abel
import all FourierTransport

/-!
# Unrestricted variation coordinates for the original monomial matrices

Actual factors L_b = X^b D_b and R_a = Z^a, not assumed unitary witnesses.
The inverse coordinate maps are defined on every matrix family. The original
Gram differential forces anti-Hermiticity only after this invertible change
of coordinates. MASTER.md §6.4 supplies the mathematical convention.
Original first-party proofs; mathlib is imported at the recorded project pin.
No upstream implementation is copied and no release license is assigned.
-/

@[expose] public section
noncomputable section

namespace UnitaryErrorBases.ThreeCycleMatrix

lemma omega_star : star UnitaryErrorBases.omega = UnitaryErrorBases.omega ^ 2 := by
  change star ThreeCycleFourier.omega = ThreeCycleFourier.omega ^ 2
  rw [ThreeCycleFourier.omega_sq]
  apply Complex.ext <;> norm_num [ThreeCycleFourier.omega, Complex.star_def] <;> ring

lemma omega_cube : UnitaryErrorBases.omega ^ 3 = 1 :=
  ThreeCycleFourier.omega_cube

/-- The actual clock powers produce the exact Fourier character and sign. -/
theorem rightFactor_character (a a' : Index) :
    rightFactor a' * (rightFactor a).conjTranspose =
      Matrix.diagonal (fun k => ThreeCycleFourier.character ((a' - a) * k)) := by
  unfold rightFactor clock
  rw [Matrix.diagonal_pow, Matrix.diagonal_pow, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  change (omega ^ k.val) ^ a'.val * star ((omega ^ k.val) ^ a.val) =
    ThreeCycleFourier.omega ^ ((a' - a) * k).val
  have hw : ThreeCycleFourier.omega = UnitaryErrorBases.omega := rfl
  rw [hw, star_pow, star_pow, omega_star]
  simp only [← pow_mul, ← pow_add]
  rw [pow_eq_pow_mod _ omega_cube]
  congr 1
  exact (by decide : ∀ a a' k : Index,
    (k.val * a'.val + 2 * k.val * a.val) % 3 = ((a' - a) * k).val) a a' k

@[simp] theorem rightFactor_mul_star (a : Index) :
    rightFactor a * (rightFactor a).conjTranspose = 1 := by
  simpa [ThreeCycleFourier.character] using rightFactor_character a a

@[simp] theorem rightFactor_star_mul (a : Index) :
    (rightFactor a).conjTranspose * rightFactor a = 1 :=
  mul_eq_one_comm.mp (rightFactor_mul_star a)

private lemma unitary_mul (A B : Mat)
    (hA : A.conjTranspose * A = 1) (hB : B.conjTranspose * B = 1) :
    (A * B).conjTranspose * (A * B) = 1 := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc A.conjTranspose A B, hA, Matrix.one_mul, hB]

private lemma unitary_pow (A : Mat) (hA : A.conjTranspose * A = 1) (n : ℕ) :
    (A ^ n).conjTranspose * A ^ n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    exact unitary_mul (A ^ n) A ih hA

private lemma unitary_diagonal (f : Index → ℂ) (hf : ∀ k, star (f k) * f k = 1) :
    (Matrix.diagonal f).conjTranspose * Matrix.diagonal f = 1 := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  simp only [Pi.star_apply, hf]
  exact Matrix.diagonal_one

lemma shift_star_mul : shift.conjTranspose * shift = 1 := by
  ext i j
  rw [mul_shift_apply]
  simp [Matrix.conjTranspose_apply, shift, Matrix.one_apply, eq_comm]

lemma phaseMatrix_star_mul (d : PhaseTriple) (b : Index) :
    (phaseMatrix d b).conjTranspose * phaseMatrix d b = 1 := by
  apply unitary_diagonal
  intro k
  by_cases hb : b = 2
  · simp only [hb, ite_true]
    calc
      star (d.val k) * d.val k = (Complex.normSq (d.val k) : ℂ) :=
        Complex.normSq_eq_conj_mul_self.symm
      _ = 1 := by rw [d.property.1 k]; rfl
  · simp [hb]

@[simp] theorem leftFactor_star_mul (d : PhaseTriple) (b : Index) :
    (leftFactor d b).conjTranspose * leftFactor d b = 1 :=
  unitary_mul _ _ (unitary_pow shift shift_star_mul b.val) (phaseMatrix_star_mul d b)

@[simp] theorem leftFactor_mul_star (d : PhaseTriple) (b : Index) :
    leftFactor d b * (leftFactor d b).conjTranspose = 1 :=
  mul_eq_one_comm.mp (leftFactor_star_mul d b)

/-- V_ab = L_b M_ab R_a on the entire ambient matrix family. -/
def fromCoordinates (d : PhaseTriple) (M : Family) : Family :=
  fun p => leftFactor d p.2 * M p * rightFactor p.1

/-- M_ab = L_b* V_ab R_a* on the entire ambient matrix family. -/
def toCoordinates (d : PhaseTriple) (V : Family) : Family :=
  fun p => (leftFactor d p.2).conjTranspose * V p * (rightFactor p.1).conjTranspose

theorem toCoordinates_fromCoordinates (d : PhaseTriple) (M : Family) :
    toCoordinates d (fromCoordinates d M) = M := by
  funext p
  unfold toCoordinates fromCoordinates
  calc
    _ = ((leftFactor d p.2).conjTranspose * leftFactor d p.2) *
        M p * (rightFactor p.1 * (rightFactor p.1).conjTranspose) := by
      simp only [Matrix.mul_assoc]
    _ = M p := by simp

theorem fromCoordinates_toCoordinates (d : PhaseTriple) (V : Family) :
    fromCoordinates d (toCoordinates d V) = V := by
  funext p
  unfold toCoordinates fromCoordinates
  calc
    _ = (leftFactor d p.2 * (leftFactor d p.2).conjTranspose) *
        V p * ((rightFactor p.1).conjTranspose * rightFactor p.1) := by
      simp only [Matrix.mul_assoc]
    _ = V p := by simp

/-- Literal Gram differential, before imposing any tangent equation. -/
theorem gram_fromCoordinates (d : PhaseTriple) (M : Family) (p : Label) :
    (monomialFamily d p).conjTranspose * fromCoordinates d M p +
      (fromCoordinates d M p).conjTranspose * monomialFamily d p =
        (rightFactor p.1).conjTranspose * (M p + (M p).conjTranspose) *
          rightFactor p.1 := by
  change (leftFactor d p.2 * rightFactor p.1).conjTranspose *
      (leftFactor d p.2 * M p * rightFactor p.1) +
    (leftFactor d p.2 * M p * rightFactor p.1).conjTranspose *
      (leftFactor d p.2 * rightFactor p.1) = _
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (leftFactor d p.2).conjTranspose (leftFactor d p.2),
    leftFactor_star_mul, Matrix.one_mul]
  rw [← Matrix.mul_assoc (leftFactor d p.2).conjTranspose (leftFactor d p.2),
    leftFactor_star_mul, Matrix.one_mul]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem antiHermitian_of_gram (d : PhaseTriple) (M : Family) (p : Label)
    (h : (monomialFamily d p).conjTranspose * fromCoordinates d M p +
      (fromCoordinates d M p).conjTranspose * monomialFamily d p = 0) :
    (M p).conjTranspose = -M p := by
  rw [gram_fromCoordinates] at h
  have hc := congrArg (fun A : Mat =>
    rightFactor p.1 * A * (rightFactor p.1).conjTranspose) h
  have hid :
      rightFactor p.1 *
        ((rightFactor p.1).conjTranspose * (M p + (M p).conjTranspose) *
          rightFactor p.1) * (rightFactor p.1).conjTranspose =
        M p + (M p).conjTranspose := by
    calc
      _ = (rightFactor p.1 * (rightFactor p.1).conjTranspose) *
          (M p + (M p).conjTranspose) *
          (rightFactor p.1 * (rightFactor p.1).conjTranspose) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by simp
  rw [hid, Matrix.mul_zero, Matrix.zero_mul] at hc
  exact eq_neg_of_add_eq_zero_right hc

/-- Exact equality to the existing scalar pairEquation. Only the first matrix's
anti-Hermiticity is used; it is obtained from the original Gram differential. -/
theorem pair_trace_eq_scalar (d : PhaseTriple) (M : Family) (b a a' : Index)
    (hM : (M (a, b)).conjTranspose = -M (a, b)) :
    Matrix.trace
      ((fromCoordinates d M (a, b)).conjTranspose * monomialFamily d (a', b + 1) +
        (monomialFamily d (a, b)).conjTranspose * fromCoordinates d M (a', b + 1)) =
      ThreeCycleFourier.pairEquation (ThreeCycleFourier.phaseWeight d.val)
        (offDiagonalCoordinates M) b a a' := by
  have hm :
      (fromCoordinates d M (a, b)).conjTranspose * monomialFamily d (a', b + 1) +
        (monomialFamily d (a, b)).conjTranspose * fromCoordinates d M (a', b + 1) =
      (rightFactor a).conjTranspose *
        (((leftFactor d b).conjTranspose * leftFactor d (b + 1)) * M (a', b + 1) -
          M (a, b) * ((leftFactor d b).conjTranspose * leftFactor d (b + 1))) *
        rightFactor a' := by
    simp only [fromCoordinates, monomialFamily_eq, Matrix.conjTranspose_mul,
      hM, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc]
    abel
  rw [hm, Matrix.trace_mul_cycle, rightFactor_character, leftFactor_adjacent]
  exact cyclic_pair_trace _ M b a a'

end UnitaryErrorBases.ThreeCycleMatrix

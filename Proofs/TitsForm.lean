module

public import Q12
public import NativeSparse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

/-!
# The complexified Tits form of the native Albert coordinates, over a generic ring

Everything is generic in a commutative ring `S` together with an explicit ring
homomorphism `ι : Q12 →+* S` (Q12 = ℚ(i, √3), brief R0).  Only `ι Q12.I`
(with `I * I = -1`) and the scalar `h = ι half` (with `2 * h = 1`) are used here.

* `titsOfNative ι x` : native coordinates `Fin 27 → S` ↦ `(a, B, Bt)` (the
  complexification of `toTitsCoordinates`/`hermitianMatrix`; `Bt` is the partner
  of `B`, equal to `conj B` at real points over ℂ).
* `titsToNative ι h p` : the inverse (needs `2 * h = 1`).
* `titsProduct h p q` : the complexified second Tits product, a pure matrix formula.

The product identity itself (27 components) is in `TitsProdA/B/Bt.lean`.
First-party composition over the imported native definitions.
-/

namespace TitsS

open NativePolynomial.CoordinateMaps Matrix

/-- Exact one half in Q12. -/
def half : Q12 := ⟨1/2, 0, 0, 0⟩
/-- Exact one third in Q12. -/
def third : Q12 := ⟨1/3, 0, 0, 0⟩

theorem Q12_two_half : (2 : Q12) * half = 1 := by decide +kernel
theorem Q12_three_third : (3 : Q12) * third = 1 := by decide +kernel
theorem Q12_I_mul_I : Q12.I * Q12.I = -1 := by decide +kernel

abbrev M3 (S : Type*) := Matrix (Fin 3) (Fin 3) S
/-- A Tits triple `(a, B, Bt)`. -/
abbrev Tits (S : Type*) := M3 S × M3 S × M3 S

variable {S : Type*} [CommRing S] (ι : Q12 →+* S)

local notation "𝕚" => ι Q12.I

theorem I_mul_I : 𝕚 * 𝕚 = -1 := by
  rw [← map_mul, Q12_I_mul_I, map_neg, map_one]

theorem two_half : (2 : S) * ι half = 1 := by
  have := congrArg ι Q12_two_half
  rwa [map_mul, map_ofNat, map_one] at this

theorem three_third : (3 : S) * ι third = 1 := by
  have := congrArg ι Q12_three_third
  rwa [map_mul, map_ofNat, map_one] at this

/-- Native coordinates to the Tits triple (complexified `toTitsCoordinates`). -/
def titsOfNative (x : Fin 27 → S) : Tits S :=
  (!![x 0, x 3 + 𝕚 * x 4, x 11 + 𝕚 * x 12;
      x 3 - 𝕚 * x 4, x 1, x 19 + 𝕚 * x 20;
      x 11 - 𝕚 * x 12, x 19 - 𝕚 * x 20, x 2],
   !![-x 21 + 𝕚 * x 22, -x 23 + 𝕚 * x 24, -x 25 - 𝕚 * x 26;
      x 13 - 𝕚 * x 14, x 15 - 𝕚 * x 16, x 17 + 𝕚 * x 18;
      -x 5 + 𝕚 * x 6, -x 7 + 𝕚 * x 8, -x 9 - 𝕚 * x 10],
   !![-x 21 - 𝕚 * x 22, -x 23 - 𝕚 * x 24, -x 25 + 𝕚 * x 26;
      x 13 + 𝕚 * x 14, x 15 + 𝕚 * x 16, x 17 - 𝕚 * x 18;
      -x 5 - 𝕚 * x 6, -x 7 - 𝕚 * x 8, -x 9 + 𝕚 * x 10])

/-- Tits triple to native coordinates (complexified `fromTitsCoordinates`); `h = 1/2`. -/
def titsToNative (h : S) (p : Tits S) : Fin 27 → S :=
  ![p.1 0 0, p.1 1 1, p.1 2 2,
    h * (p.1 0 1 + p.1 1 0), -𝕚 * h * (p.1 0 1 - p.1 1 0),
    -(h * (p.2.1 2 0 + p.2.2 2 0)), -𝕚 * h * (p.2.1 2 0 - p.2.2 2 0),
    -(h * (p.2.1 2 1 + p.2.2 2 1)), -𝕚 * h * (p.2.1 2 1 - p.2.2 2 1),
    -(h * (p.2.1 2 2 + p.2.2 2 2)), 𝕚 * h * (p.2.1 2 2 - p.2.2 2 2),
    h * (p.1 0 2 + p.1 2 0), -𝕚 * h * (p.1 0 2 - p.1 2 0),
    h * (p.2.1 1 0 + p.2.2 1 0), 𝕚 * h * (p.2.1 1 0 - p.2.2 1 0),
    h * (p.2.1 1 1 + p.2.2 1 1), 𝕚 * h * (p.2.1 1 1 - p.2.2 1 1),
    h * (p.2.1 1 2 + p.2.2 1 2), -𝕚 * h * (p.2.1 1 2 - p.2.2 1 2),
    h * (p.1 1 2 + p.1 2 1), -𝕚 * h * (p.1 1 2 - p.1 2 1),
    -(h * (p.2.1 0 0 + p.2.2 0 0)), -𝕚 * h * (p.2.1 0 0 - p.2.2 0 0),
    -(h * (p.2.1 0 1 + p.2.2 0 1)), -𝕚 * h * (p.2.1 0 1 - p.2.2 0 1),
    -(h * (p.2.1 0 2 + p.2.2 0 2)), 𝕚 * h * (p.2.1 0 2 - p.2.2 0 2)]

/-- Transposed polarized adjugate `(adj (X + Y) - adj X - adj Y)ᵀ`. -/
def crossT (X Y : M3 S) : M3 S := (adjugate (X + Y) - adjugate X - adjugate Y)ᵀ

/-- The complexified second Tits product (`h = 1/2`). -/
def titsProduct (h : S) (p q : Tits S) : Tits S :=
  (h • (p.1 * q.1 + q.1 * p.1 - p.2.1 * q.2.2ᵀ - q.2.1 * p.2.2ᵀ) +
      (h * (trace (p.2.1 * q.2.2ᵀ) + trace (q.2.1 * p.2.2ᵀ))) • (1 : M3 S),
   h • ((trace q.1 • (1 : M3 S) - q.1) * p.2.1 + (trace p.1 • (1 : M3 S) - p.1) * q.2.1 +
      crossT p.2.2 q.2.2),
   h • ((trace q.1 • (1 : M3 S) - q.1ᵀ) * p.2.2 + (trace p.1 • (1 : M3 S) - p.1ᵀ) * q.2.2 +
      crossT p.2.1 q.2.1))

/-! ### Entry evaluation -/

theorem cons_val_two {α : Type*} {m : ℕ} (a b c : α) (u : Fin m → α) :
    Matrix.vecCons a (Matrix.vecCons b (Matrix.vecCons c u)) 2 = c := rfl

/-! ### Round trips -/

theorem toNative_ofNative (h : S) (h2 : (2 : S) * h = 1) (x : Fin 27 → S) :
    titsToNative ι h (titsOfNative ι x) = x := by
  have hI := I_mul_I ι
  funext k
  fin_cases k
  all_goals simp only [titsToNative, titsOfNative, Matrix.of_apply, Matrix.cons_val, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  case «3» => linear_combination (x 3) * h2
  case «4» => linear_combination (-2*h*x 4) * hI + (x 4) * h2
  case «5» => linear_combination (x 5) * h2
  case «6» => linear_combination (-2*h*x 6) * hI + (x 6) * h2
  case «7» => linear_combination (x 7) * h2
  case «8» => linear_combination (-2*h*x 8) * hI + (x 8) * h2
  case «9» => linear_combination (x 9) * h2
  case «10» => linear_combination (-2*h*x 10) * hI + (x 10) * h2
  case «11» => linear_combination (x 11) * h2
  case «12» => linear_combination (-2*h*x 12) * hI + (x 12) * h2
  case «13» => linear_combination (x 13) * h2
  case «14» => linear_combination (-2*h*x 14) * hI + (x 14) * h2
  case «15» => linear_combination (x 15) * h2
  case «16» => linear_combination (-2*h*x 16) * hI + (x 16) * h2
  case «17» => linear_combination (x 17) * h2
  case «18» => linear_combination (-2*h*x 18) * hI + (x 18) * h2
  case «19» => linear_combination (x 19) * h2
  case «20» => linear_combination (-2*h*x 20) * hI + (x 20) * h2
  case «21» => linear_combination (x 21) * h2
  case «22» => linear_combination (-2*h*x 22) * hI + (x 22) * h2
  case «23» => linear_combination (x 23) * h2
  case «24» => linear_combination (-2*h*x 24) * hI + (x 24) * h2
  case «25» => linear_combination (x 25) * h2
  case «26» => linear_combination (-2*h*x 26) * hI + (x 26) * h2

set_option maxHeartbeats 1000000 in
theorem ofNative_toNative_a (h : S) (h2 : (2 : S) * h = 1) (p : Tits S) :
    (titsOfNative ι (titsToNative ι h p)).1 = p.1 := by
  have hI := I_mul_I ι
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [titsToNative, titsOfNative, Matrix.of_apply, Matrix.cons_val, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  all_goals first
    | linear_combination (-p.1 0 1*h + p.1 1 0*h) * hI + (p.1 0 1) * h2
    | linear_combination (-p.1 0 2*h + p.1 2 0*h) * hI + (p.1 0 2) * h2
    | linear_combination (p.1 0 1*h - p.1 1 0*h) * hI + (p.1 1 0) * h2
    | linear_combination (-p.1 1 2*h + p.1 2 1*h) * hI + (p.1 1 2) * h2
    | linear_combination (p.1 0 2*h - p.1 2 0*h) * hI + (p.1 2 0) * h2
    | linear_combination (p.1 1 2*h - p.1 2 1*h) * hI + (p.1 2 1) * h2

set_option maxHeartbeats 1000000 in
theorem ofNative_toNative_B (h : S) (h2 : (2 : S) * h = 1) (p : Tits S) :
    (titsOfNative ι (titsToNative ι h p)).2.1 = p.2.1 := by
  have hI := I_mul_I ι
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [titsToNative, titsOfNative, Matrix.of_apply, Matrix.cons_val, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  all_goals first
    | linear_combination (-p.2.1 0 0*h + p.2.2 0 0*h) * hI + (p.2.1 0 0) * h2
    | linear_combination (-p.2.1 0 1*h + p.2.2 0 1*h) * hI + (p.2.1 0 1) * h2
    | linear_combination (-p.2.1 0 2*h + p.2.2 0 2*h) * hI + (p.2.1 0 2) * h2
    | linear_combination (-p.2.1 1 0*h + p.2.2 1 0*h) * hI + (p.2.1 1 0) * h2
    | linear_combination (-p.2.1 1 1*h + p.2.2 1 1*h) * hI + (p.2.1 1 1) * h2
    | linear_combination (-p.2.1 1 2*h + p.2.2 1 2*h) * hI + (p.2.1 1 2) * h2
    | linear_combination (-p.2.1 2 0*h + p.2.2 2 0*h) * hI + (p.2.1 2 0) * h2
    | linear_combination (-p.2.1 2 1*h + p.2.2 2 1*h) * hI + (p.2.1 2 1) * h2
    | linear_combination (-p.2.1 2 2*h + p.2.2 2 2*h) * hI + (p.2.1 2 2) * h2

set_option maxHeartbeats 1000000 in
theorem ofNative_toNative_Bt (h : S) (h2 : (2 : S) * h = 1) (p : Tits S) :
    (titsOfNative ι (titsToNative ι h p)).2.2 = p.2.2 := by
  have hI := I_mul_I ι
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [titsToNative, titsOfNative, Matrix.of_apply, Matrix.cons_val, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  all_goals first
    | linear_combination (p.2.1 0 0*h - p.2.2 0 0*h) * hI + (p.2.2 0 0) * h2
    | linear_combination (p.2.1 0 1*h - p.2.2 0 1*h) * hI + (p.2.2 0 1) * h2
    | linear_combination (p.2.1 0 2*h - p.2.2 0 2*h) * hI + (p.2.2 0 2) * h2
    | linear_combination (p.2.1 1 0*h - p.2.2 1 0*h) * hI + (p.2.2 1 0) * h2
    | linear_combination (p.2.1 1 1*h - p.2.2 1 1*h) * hI + (p.2.2 1 1) * h2
    | linear_combination (p.2.1 1 2*h - p.2.2 1 2*h) * hI + (p.2.2 1 2) * h2
    | linear_combination (p.2.1 2 0*h - p.2.2 2 0*h) * hI + (p.2.2 2 0) * h2
    | linear_combination (p.2.1 2 1*h - p.2.2 2 1*h) * hI + (p.2.2 2 1) * h2
    | linear_combination (p.2.1 2 2*h - p.2.2 2 2*h) * hI + (p.2.2 2 2) * h2

theorem ofNative_toNative (h : S) (h2 : (2 : S) * h = 1) (p : Tits S) :
    titsOfNative ι (titsToNative ι h p) = p :=
  Prod.ext (ofNative_toNative_a ι h h2 p)
    (Prod.ext (ofNative_toNative_B ι h h2 p) (ofNative_toNative_Bt ι h h2 p))

theorem titsOfNative_injective (h : S) (h2 : (2 : S) * h = 1) :
    Function.Injective (titsOfNative ι) := by
  intro x y hxy
  rw [← toNative_ofNative ι h h2 x, hxy, toNative_ofNative ι h h2]

/-! ### Trace, unit, pairing -/

theorem trace_titsOfNative (x : Fin 27 → S) :
    Matrix.trace (titsOfNative ι x).1 = coordinateTrace x := by
  rw [coordinateTrace_apply]
  simp [titsOfNative, Matrix.trace, Fin.sum_univ_three]

theorem titsOfNative_unit : titsOfNative ι coordinateUnit = (1, 0, 0) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  all_goals ext i j
  all_goals fin_cases i <;> fin_cases j
  all_goals simp [titsOfNative, coordinateUnit, Matrix.one_apply]

theorem titsToNative_unit (h : S) (h2 : (2 : S) * h = 1) :
    titsToNative ι h (1, 0, 0) = coordinateUnit := by
  rw [← titsOfNative_unit ι, toNative_ofNative ι h h2]

theorem pairing_flat (x y : Fin 27 → S) : coordinatePairing x y =
    x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + 2 * (x 3 * y 3 + x 4 * y 4 + x 5 * y 5 + x 6 * y 6 + x 7 * y 7 +
      x 8 * y 8 + x 9 * y 9 + x 10 * y 10 + x 11 * y 11 + x 12 * y 12 + x 13 * y 13 + x 14 * y 14 +
      x 15 * y 15 + x 16 * y 16 + x 17 * y 17 + x 18 * y 18 + x 19 * y 19 + x 20 * y 20 + x 21 * y 21 +
      x 22 * y 22 + x 23 * y 23 + x 24 * y 24 + x 25 * y 25 + x 26 * y 26) := by
  simp [coordinatePairing, Fin.sum_univ_succ,
    NativePolynomial.IntegralStructureConstants.coordinateTraceWeight]
  ring

/-- The native weighted pairing in Tits coordinates. -/
theorem pairing_titsOfNative (x y : Fin 27 → S) :
    coordinatePairing x y =
      Matrix.trace ((titsOfNative ι x).1 * (titsOfNative ι y).1) +
      Matrix.trace ((titsOfNative ι x).2.1 * (titsOfNative ι y).2.2ᵀ) +
      Matrix.trace ((titsOfNative ι y).2.1 * (titsOfNative ι x).2.2ᵀ) := by
  have hI := I_mul_I ι
  rw [pairing_flat]
  simp only [titsOfNative, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val, Fin.isValue]
  linear_combination (2*x 10*y 10 + 2*x 12*y 12 + 2*x 14*y 14 + 2*x 16*y 16 + 2*x 18*y 18 + 2*x 20*y 20 + 2*x 22*y 22 + 2*x 24*y 24 + 2*x 26*y 26 + 2*x 4*y 4 + 2*x 6*y 6 + 2*x 8*y 8) * hI

end TitsS

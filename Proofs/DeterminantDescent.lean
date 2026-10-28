module

public import IntegerQ12
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Determinant descent: nonvanishing transfers backwards along ring homomorphisms

The nonvanishing principle of the certificate route. If `φ : R →+* S` is any ring homomorphism,
then `φ (det M) = det (M.map φ)`, so a determinant that is nonzero *after* applying `φ` was
nonzero before. Applied to the reduction `Z12 → ZMod p` this turns one modular computation into
the statement `det ≠ 0` over `Z12`; applied forwards along the injective maps
`Z12 → Q12 → ℂ`, nonvanishing is carried up to `ℂ`.

Only nonvanishing is transferred backwards from `ZMod p`; equalities never are.

Main statements:
* `Matrix.det_ne_zero_of_map_det_ne_zero` — descent along an arbitrary ring homomorphism.
* `Matrix.map_det_ne_zero_of_injective` — ascent along an injective ring homomorphism.
* `Matrix.complex_det_ne_zero_of_mod_p` — the composite `ZMod p ⇐ Z12 ⇒ Q12 ⇒ ℂ`.
* `Matrix.complex_det_ne_zero_of_integer_scaling` — the global-denominator trick.
* `Matrix.rows_linearIndependent_of_det_ne_zero`, `Matrix.span_rows_eq_top_of_det_ne_zero` —
  rank consequences over a field.
-/

@[expose] public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Rings

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **Descent of nonvanishing.** If the determinant of `M.map φ` is nonzero for some ring
homomorphism `φ`, then `det M ≠ 0`. (Because `φ (det M) = det (M.map φ)` and `φ 0 = 0`.) -/
theorem det_ne_zero_of_map_det_ne_zero (φ : R →+* S) (M : Matrix n n R)
    (h : (M.map φ).det ≠ 0) : M.det ≠ 0 := by
  intro hM
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hM, map_zero]

/-- The same statement phrased with `RingHom.mapMatrix`. -/
theorem det_ne_zero_of_map_ne_zero (φ : R →+* S) (M : Matrix n n R)
    (h : (φ.mapMatrix M).det ≠ 0) : M.det ≠ 0 :=
  det_ne_zero_of_map_det_ne_zero φ M h

/-- **Ascent of nonvanishing.** An injective ring homomorphism preserves `det ≠ 0`. -/
theorem map_det_ne_zero_of_injective (φ : R →+* S) (hφ : Function.Injective φ)
    (M : Matrix n n R) (h : M.det ≠ 0) : (M.map φ).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero_iff φ hφ).2 h

/-- **Global-denominator trick, ring form.** Scaling a matrix by `D` multiplies its determinant
by `D ^ card n` (`Matrix.det_smul`). -/
theorem scaled_det (D : R) (M : Matrix n n R) :
    (D • M).det = D ^ Fintype.card n * M.det :=
  det_smul M D

/-- If the scaled matrix `D • M` has nonzero determinant then so does `M`; no hypothesis on `D`
is needed in this direction. -/
theorem det_ne_zero_of_scaled_det_ne_zero (D : R) (M : Matrix n n R)
    (h : (D • M).det ≠ 0) : M.det ≠ 0 := by
  intro hM
  apply h
  rw [scaled_det, hM, mul_zero]

end Rings

/-! ## The chain `ZMod p ⇐ Z12 ⇒ Q12 ⇒ ℂ` -/

/-- An integer matrix over `Z12` with nonzero determinant stays nonsingular over `Q12`. -/
theorem Q12_det_ne_zero_of_Z12 (M : Matrix n n Z12) (h : M.det ≠ 0) :
    (M.map Z12.toQ12).det ≠ 0 :=
  map_det_ne_zero_of_injective Z12.toQ12 Z12.toQ12_injective M h

/-- A matrix over `Q12` with nonzero determinant stays nonsingular over `ℂ`. -/
theorem complex_det_ne_zero_of_Q12 (M : Matrix n n Q12) (h : M.det ≠ 0) :
    (M.map Q12.toComplex).det ≠ 0 :=
  map_det_ne_zero_of_injective Q12.toComplex Q12.toComplex_injective M h

/-- **Modular certificate ⇒ complex nonsingularity.** If the reduction of an integer matrix
`M` over `Z12` modulo `p` (for any admissible square roots `ri`, `rs`) has nonzero determinant,
then the corresponding complex matrix has nonzero determinant. -/
theorem complex_det_ne_zero_of_mod_p (p : ℕ) (ri rs : ZMod p) (hi : ri * ri = -1)
    (hs : rs * rs = 3) (M : Matrix n n Z12)
    (h : (M.map (Z12.toZMod p ri rs hi hs)).det ≠ 0) :
    ((M.map Z12.toQ12).map Q12.toComplex).det ≠ 0 :=
  complex_det_ne_zero_of_Q12 _ <| Q12_det_ne_zero_of_Z12 _ <|
    det_ne_zero_of_map_det_ne_zero _ M h

/-- **Global-denominator trick.** Exact data `M` over `Q12` with denominators is cleared by one
integer `D`: `N` over `Z12` with `N.map toQ12 = D • M`. If `N` is nonsingular modulo `p`, then
`M` is nonsingular over `ℂ`. (No hypothesis on `D` is needed: `D ^ n · det M ≠ 0` already forces
`det M ≠ 0`.) -/
theorem complex_det_ne_zero_of_integer_scaling (p : ℕ) (ri rs : ZMod p) (hi : ri * ri = -1)
    (hs : rs * rs = 3) (N : Matrix n n Z12) (M : Matrix n n Q12) (D : ℤ)
    (hN : N.map Z12.toQ12 = (D : Q12) • M)
    (h : (N.map (Z12.toZMod p ri rs hi hs)).det ≠ 0) :
    (M.map Q12.toComplex).det ≠ 0 := by
  apply complex_det_ne_zero_of_Q12
  apply det_ne_zero_of_scaled_det_ne_zero (D : Q12)
  rw [← hN]
  exact Q12_det_ne_zero_of_Z12 N (det_ne_zero_of_map_det_ne_zero _ N h)

/-! ## Rank consequences over a field -/

section Field

variable {K : Type*} [Field K]

/-- The rows of a square matrix with nonzero determinant are linearly independent
(Mathlib's `Matrix.linearIndependent_rows_of_det_ne_zero`, restated for the certificate API). -/
theorem rows_linearIndependent_of_det_ne_zero (M : Matrix n n K) (h : M.det ≠ 0) :
    LinearIndependent K (fun i => M i) :=
  linearIndependent_rows_of_det_ne_zero h

/-- The rows of a square matrix with nonzero determinant span the whole space `n → K`. -/
theorem span_rows_eq_top_of_det_ne_zero (M : Matrix n n K) (h : M.det ≠ 0) :
    Submodule.span K (Set.range fun i => M i) = ⊤ :=
  (rows_linearIndependent_of_det_ne_zero M h).span_eq_top_of_card_eq_finrank'
    (Module.finrank_fintype_fun_eq_card K).symm

end Field

end Matrix

end

#print axioms Matrix.det_ne_zero_of_map_det_ne_zero
#print axioms Matrix.det_ne_zero_of_map_ne_zero
#print axioms Matrix.map_det_ne_zero_of_injective
#print axioms Matrix.scaled_det
#print axioms Matrix.det_ne_zero_of_scaled_det_ne_zero
#print axioms Matrix.Q12_det_ne_zero_of_Z12
#print axioms Matrix.complex_det_ne_zero_of_Q12
#print axioms Matrix.complex_det_ne_zero_of_mod_p
#print axioms Matrix.complex_det_ne_zero_of_integer_scaling
#print axioms Matrix.rows_linearIndependent_of_det_ne_zero
#print axioms Matrix.span_rows_eq_top_of_det_ne_zero

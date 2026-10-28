module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Abel

/-!
# Central roots from a three-by-three quadratic relation

The universal adjugate identity reduces a determinant-one complex matrix
satisfying `R² + R + I = 0` to a scalar matrix. Its scalar is one of the two
specified cube roots. The core uses no unitarity, spectral decomposition or
matrix inverse. The final wrapper derives its quadratic from the displayed
unitary and conjugate-transpose equations.

Mathematical source: MASTER.md §6.2 and the prior source review
`../jet-budget/CENTRAL-TRIPLES-SOURCE-REVIEW.md`. The adjugate route was suggested
in the Gemini review identified there. These are independently written proofs;
no upstream implementation body is copied or adapted.

Imported source: https://github.com/leanprover-community/mathlib4,
commit 065356127b1dc0016f66b7283ce0ce2c4055aa55, Apache-2.0.
Principal APIs: Mathlib/LinearAlgebra/Matrix/Adjugate.lean,
`Matrix.adjugate_fin_three` and `Matrix.adjugate_mul` (file author Anne Baanen);
Mathlib/LinearAlgebra/Matrix/Trace.lean, trace operations (file authors
Johannes Hölzl, Patrick Massot, Casper Putz and Anne Baanen).
The ordered wrapper uses Mathlib/LinearAlgebra/UnitaryGroup.lean,
`Matrix.mem_specialUnitaryGroup_iff` and both unitary membership equations
(file author Shing Tak Lam). These declarations are imported, not copied.
No upstream declaration is modified. Thanks to these authors and the Lean
and mathlib contributors for the imported matrix and tactic infrastructure.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

public section
noncomputable section

namespace UnitaryErrorBases

/-- The universal three-by-three adjugate identity, including singular matrices. -/
theorem adjugate_eq_square_sub_trace_smul
    {K : Type*} [CommRing K] (R : Matrix (Fin 3) (Fin 3) K) :
    R.adjugate = R * R - Matrix.trace R • R +
      Matrix.trace R.adjugate • (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_three, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_three] <;> ring

/-- Determinant one and the quadratic alone force a complex scalar matrix.
Characteristic zero is used when the trace-zero case would force `3 = 0`. -/
theorem exists_scalar_of_det_eq_one_of_quadratic
    (R : Matrix (Fin 3) (Fin 3) ℂ)
    (hdet : R.det = 1) (hquad : R * R + R + 1 = 0) :
    ∃ c : ℂ, R = c • (1 : Matrix (Fin 3) (Fin 3) ℂ) ∧
      c * c + c + 1 = 0 := by
  let t : ℂ := Matrix.trace R
  have hquadratic : R * R + R = -1 := eq_neg_of_add_eq_zero_left hquad
  have hright : R * (-1 - R) = 1 := by
    calc
      R * (-1 - R) = -(R * R + R) := by
        simp only [mul_sub, mul_add, mul_neg, mul_one, neg_add_rev, sub_eq_add_neg]
      _ = 1 := by rw [hquadratic]; simp
  have hadjugate : R.adjugate = -1 - R := by
    calc
      R.adjugate = R.adjugate * 1 := (mul_one _).symm
      _ = R.adjugate * (R * (-1 - R)) := by rw [hright]
      _ = (R.adjugate * R) * (-1 - R) := (mul_assoc _ _ _).symm
      _ = -1 - R := by rw [Matrix.adjugate_mul, hdet]; simp
  have htrace : Matrix.trace R.adjugate = -3 - t := by
    rw [hadjugate, Matrix.trace_sub, Matrix.trace_neg, Matrix.trace_one]
    norm_num [t]
  have huniversal := adjugate_eq_square_sub_trace_smul R
  rw [htrace, hadjugate] at huniversal
  have hcoefficient (i j : Fin 3) :
      t * R i j = -(t + 3) * (1 : Matrix (Fin 3) (Fin 3) ℂ) i j := by
    have ha := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A i j) huniversal
    have hq := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A i j) hquad
    change (-1 - R) i j = (R * R - t • R + (-3 - t) • 1) i j at ha
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at ha hq
    linear_combination ha + hq
  have ht : t ≠ 0 := by
    intro ht
    have h := hcoefficient 0 0
    norm_num [ht] at h
  let c : ℂ := -(t + 3) / t
  have hscalar : R = c • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    apply mul_left_cancel₀ ht
    calc
      t * R i j = -(t + 3) * (1 : Matrix (Fin 3) (Fin 3) ℂ) i j :=
        hcoefficient i j
      _ = t * (c * (1 : Matrix (Fin 3) (Fin 3) ℂ) i j) := by
        dsimp [c]
        field_simp [ht] <;> ring
  refine ⟨c, hscalar, ?_⟩
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A 0 0) hquad
  rw [hscalar] at h
  simpa [Matrix.mul_apply, Fin.sum_univ_three] using h

/-- The scalar quadratic factors at the specified root and its square.
The project's fixed root can be supplied without defining another omega. -/
theorem eq_central_root_of_det_eq_one_of_quadratic
    (R : Matrix (Fin 3) (Fin 3) ℂ) (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0)
    (hdet : R.det = 1) (hquad : R * R + R + 1 = 0) :
    R = ω • (1 : Matrix (Fin 3) (Fin 3) ℂ) ∨
      R = ω ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  obtain ⟨c, hscalar, hc⟩ := exists_scalar_of_det_eq_one_of_quadratic R hdet hquad
  have hsum : ω + ω ^ 2 = -1 := by linear_combination hω
  have hcube : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hfactor : (c - ω) * (c - ω ^ 2) = 0 := by
    calc
      (c - ω) * (c - ω ^ 2) = c * c - c * (ω + ω ^ 2) + ω ^ 3 := by ring
      _ = c * c + c + 1 := by rw [hsum, hcube]; ring
      _ = 0 := hc
  rcases mul_eq_zero.mp hfactor with hroot | hroot
  · left
    simpa [sub_eq_zero.mp hroot] using hscalar
  · right
    simpa [sub_eq_zero.mp hroot] using hscalar

/-- One side of unitarity and the conjugate-transpose sum imply the quadratic. -/
theorem eq_central_root_of_unitary_sum_conjTranspose
    (R : Matrix (Fin 3) (Fin 3) ℂ) (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0)
    (hunit : R * R.conjTranspose = 1) (hdet : R.det = 1)
    (hsum : R + R.conjTranspose = -1) :
    R = ω • (1 : Matrix (Fin 3) (Fin 3) ℂ) ∨
      R = ω ^ 2 • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => R * A) hsum
  simp only [mul_add, hunit, mul_neg, mul_one] at h
  apply eq_central_root_of_det_eq_one_of_quadratic R ω hω hdet
  calc
    R * R + R + 1 = (R * R + 1) + R := by abel
    _ = -R + R := by rw [h]
    _ = 0 := neg_add_cancel R

/-- An ordered special-unitary triple with zero sum consists of the three
central multiples of its first member. The alternatives retain the order. -/
theorem specialUnitary_triple_sum_zero
    (U V W : Matrix (Fin 3) (Fin 3) ℂ) (ω : ℂ)
    (hω : ω ^ 2 + ω + 1 = 0)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (hV : V ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (hW : W ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ)
    (hsum : U + V + W = 0) :
    (V = ω • U ∧ W = ω ^ 2 • U) ∨
      (V = ω ^ 2 • U ∧ W = ω • U) := by
  obtain ⟨hUunit, hUdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hU
  obtain ⟨hVunit, hVdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hV
  have hWunit := (Matrix.mem_specialUnitaryGroup_iff.mp hW).1
  have hUleft : U.conjTranspose * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp hUunit
  have hUright : U * U.conjTranspose = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff.mp hUunit
  have hVright : V * V.conjTranspose = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff.mp hVunit
  have hWright : W * W.conjTranspose = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff.mp hWunit
  let R := U.conjTranspose * V
  let S := U.conjTranspose * W
  have normalized_unitary (A : Matrix (Fin 3) (Fin 3) ℂ)
      (hA : A * A.conjTranspose = 1) :
      (U.conjTranspose * A) * (U.conjTranspose * A).conjTranspose = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      (U.conjTranspose * A) * (A.conjTranspose * U) =
          (U.conjTranspose * (A * A.conjTranspose)) * U := by
            simp only [mul_assoc]
      _ = 1 := by rw [hA, mul_one, hUleft]
  have hRunit : R * R.conjTranspose = 1 := normalized_unitary V hVright
  have hSunit : S * S.conjTranspose = 1 := normalized_unitary W hWright
  have hRdet : R.det = 1 := by
    simp [R, Matrix.det_mul, Matrix.det_conjTranspose, hUdet, hVdet]
  have hnormalized : 1 + R + S = 0 := by
    have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => U.conjTranspose * A) hsum
    simpa only [mul_add, hUleft, mul_zero] using h
  have hS : S = -1 - R := by
    calc
      S = -(1 + R) := eq_neg_of_add_eq_zero_right hnormalized
      _ = -1 - R := by abel
  have hproduct : (-1 - R) * (-1 - R.conjTranspose) = 1 := by
    rw [hS] at hSunit
    simpa only [Matrix.conjTranspose_sub, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_one] using hSunit
  have hRsum : R + R.conjTranspose = -1 := by
    calc
      R + R.conjTranspose =
          (-1 - R) * (-1 - R.conjTranspose) - R * R.conjTranspose - 1 := by
        simp only [sub_mul, mul_sub, neg_mul, mul_neg, one_mul, mul_one, neg_neg]
        abel
      _ = -1 := by rw [hproduct, hRunit]; abel
  have recover (c : ℂ) (hc : R = c • (1 : Matrix (Fin 3) (Fin 3) ℂ)) :
      V = c • U := by
    calc
      V = U * R := by simp only [R, ← mul_assoc, hUright, one_mul]
      _ = U * (c • (1 : Matrix (Fin 3) (Fin 3) ℂ)) := by rw [hc]
      _ = c • U := by rw [Matrix.mul_smul, mul_one]
  have complement (c d : ℂ) (hcd : 1 + c + d = 0) (hc : V = c • U) :
      W = d • U := by
    apply add_left_cancel (a := U + V)
    calc
      U + V + W = 0 := hsum
      _ = (1 + c + d) • U := by rw [hcd, zero_smul]
      _ = U + V + d • U := by simp only [hc, add_smul, one_smul]
  rcases eq_central_root_of_unitary_sum_conjTranspose R ω hω hRunit hRdet hRsum
    with hR | hR
  · have hVroot := recover ω hR
    exact Or.inl ⟨hVroot, complement ω (ω ^ 2) (by linear_combination hω) hVroot⟩
  · have hVroot := recover (ω ^ 2) hR
    exact Or.inr ⟨hVroot, complement (ω ^ 2) ω (by linear_combination hω) hVroot⟩

#print axioms adjugate_eq_square_sub_trace_smul
#print axioms exists_scalar_of_det_eq_one_of_quadratic
#print axioms eq_central_root_of_det_eq_one_of_quadratic
#print axioms eq_central_root_of_unitary_sum_conjTranspose
#print axioms specialUnitary_triple_sum_zero

end UnitaryErrorBases

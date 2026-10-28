module

public import BookHTQuartic
public import NativeHWeights

@[expose] public section

/-!
The literal quads.json trinomials interpreted in characteristic zero, and
their dictionary on the real form specified by realstruct.json. The JSON's
prime metadata is not used. This proves no native covector cancellation,
quadratic reproduction through the native eigenbasis V, or metric binding.
-/

noncomputable section

namespace Option2.NativeStress.BookHT.Dictionary

open scoped BigOperators ComplexConjugate
open MvPolynomial

/-- `(first variable, second variable, integer coefficient)`, exactly as supplied. -/
abbrev Term := Fin 24 × Fin 24 × ℤ

/-- All48 ordered rows of quads.json; each coefficient is the literal integer ±1. -/
def terms : Fin 48 → Fin 3 → Term :=
  ![![(7,16,1),(9,23,1),(14,18,-1)],
    ![(8,15,1),(10,22,1),(12,20,1)],
    ![(6,17,1),(11,21,1),(13,19,-1)],
    ![(0,6,1),(5,8,-1),(19,21,-1)],
    ![(0,7,1),(4,6,1),(20,21,1)],
    ![(0,9,1),(4,11,1),(15,19,-1)],
    ![(0,11,1),(5,10,-1),(17,19,-1)],
    ![(0,13,1),(5,12,-1),(17,21,1)],
    ![(0,14,1),(4,13,-1),(17,22,-1)],
    ![(0,15,1),(4,17,1),(10,12,-1)],
    ![(0,16,1),(5,15,-1),(11,12,-1)],
    ![(0,18,1),(5,20,-1),(6,10,-1)],
    ![(0,20,1),(4,19,-1),(8,10,-1)],
    ![(0,22,1),(4,21,1),(8,12,-1)],
    ![(0,23,1),(5,22,-1),(8,13,-1)],
    ![(1,6,1),(3,8,-1),(18,22,1)],
    ![(1,8,1),(4,7,1),(20,22,1)],
    ![(1,10,1),(4,9,1),(15,20,1)],
    ![(1,11,1),(3,10,-1),(16,20,1)],
    ![(1,12,1),(4,14,-1),(15,22,1)],
    ![(1,13,1),(3,12,-1),(15,23,1)],
    ![(1,16,1),(3,15,-1),(9,14,1)],
    ![(1,17,1),(4,16,1),(10,14,1)],
    ![(1,18,1),(3,20,-1),(7,9,-1)],
    ![(1,19,1),(4,18,-1),(8,9,1)],
    ![(1,21,1),(4,23,1),(7,12,-1)],
    ![(1,23,1),(3,22,-1),(7,14,1)],
    ![(2,7,1),(3,6,1),(18,23,-1)],
    ![(2,8,1),(5,7,1),(19,23,1)],
    ![(2,9,1),(3,11,1),(16,18,-1)],
    ![(2,10,1),(5,9,1),(17,18,-1)],
    ![(2,12,1),(5,14,-1),(16,21,-1)],
    ![(2,14,1),(3,13,-1),(16,23,1)],
    ![(2,15,1),(3,17,1),(9,13,1)],
    ![(2,17,1),(5,16,1),(11,13,1)],
    ![(2,19,1),(5,18,-1),(6,11,-1)],
    ![(2,20,1),(3,19,-1),(7,11,1)],
    ![(2,21,1),(5,23,1),(6,13,1)],
    ![(2,22,1),(3,21,1),(6,14,-1)],
    ![(8,17,1),(10,21,1),(12,19,-1)],
    ![(7,15,1),(9,22,1),(14,20,-1)],
    ![(6,16,1),(11,23,1),(13,18,1)],
    ![(6,20,1),(7,19,-1),(8,18,1)],
    ![(6,22,1),(7,21,1),(8,23,1)],
    ![(9,17,1),(10,16,1),(11,15,1)],
    ![(9,19,1),(10,18,-1),(11,20,-1)],
    ![(12,16,1),(13,15,1),(14,17,-1)],
    ![(12,23,1),(13,22,1),(14,21,-1)]]

def termPolynomial (t : Term) : MvPolynomial (Fin 24) ℂ :=
  C (t.2.2 : ℂ) * X t.1 * X t.2.1

/-- An actual characteristic-zero polynomial, not a modular equality. -/
def quadric (j : Fin 48) : MvPolynomial (Fin 24) ℂ :=
  termPolynomial (terms j 0) + termPolynomial (terms j 1) + termPolynomial (terms j 2)

/-- The24 involution targets in realstruct.json; each multiplier there is -1. -/
def coordinateBar : Fin 24 → Fin 24 :=
  ![3,5,4,0,2,1,15,17,16,21,23,22,18,20,19,6,8,7,12,14,13,9,11,10]

theorem coordinateBar_involutive : Function.Involutive coordinateBar := by
  intro j
  fin_cases j <;> rfl

/-- The twelve independent coordinates, in the Book's four-triple order. -/
def independentIndex : Fin 4 → Fin 3 → Fin 24 :=
  ![![0,1,2], ![6,9,12], ![8,11,14], ![7,10,13]]

/-- The literal real form: the partner coordinate is negative complex conjugate. -/
def realCoordinates (z : Blocks) : Fin 24 → ℂ :=
  ![z 0 0,z 0 1,z 0 2,-conj (z 0 0),-conj (z 0 2),-conj (z 0 1),
    z 1 0,z 3 0,z 2 0,z 1 1,z 3 1,z 2 1,z 1 2,z 3 2,z 2 2,
    -conj (z 1 0),-conj (z 2 0),-conj (z 3 0),-conj (z 1 2),
    -conj (z 2 2),-conj (z 3 2),-conj (z 1 1),-conj (z 2 1),-conj (z 3 1)]

theorem realCoordinates_independent (z : Blocks) (i : Fin 4) (a : Fin 3) :
    realCoordinates z (independentIndex i a) = z i a := by
  fin_cases i <;> fin_cases a <;> rfl

theorem realCoordinates_bar (z : Blocks) (j : Fin 24) :
    realCoordinates z (coordinateBar j) = -conj (realCoordinates z j) := by
  fin_cases j <;> simp [realCoordinates, coordinateBar]

/-- Explicit conjugate-row/sign candidates for the quadratic system.
The following polynomial theorem proves these candidates independently in Lean. -/
def quadricBar : Fin 48 → Fin 48 × ℤ :=
  ![(39,1),(41,1),(40,1),(21,-1),(33,1),(38,1),(26,-1),(23,-1),
    (36,-1),(27,1),(15,-1),(20,-1),(32,-1),(29,1),(18,-1),(10,-1),
    (34,1),(37,1),(14,-1),(35,-1),(11,-1),(3,-1),(28,1),(7,-1),
    (31,-1),(30,1),(6,-1),(9,1),(22,1),(13,1),(25,1),(24,-1),
    (12,-1),(4,1),(16,1),(19,-1),(8,-1),(17,1),(5,1),(0,1),
    (2,1),(1,1),(46,1),(44,1),(43,1),(47,-1),(42,1),(45,-1)]

private theorem conjugate_block0 (a : Fin 12) :
    let j : Fin 48 := ⟨a.val + 0, by omega⟩
    rename coordinateBar (quadric j) =
      C ((quadricBar j).2 : ℂ) * quadric (quadricBar j).1 := by
  fin_cases a <;> simp [quadric, termPolynomial, terms, quadricBar, coordinateBar] <;> ring

private theorem conjugate_block1 (a : Fin 12) :
    let j : Fin 48 := ⟨a.val + 12, by omega⟩
    rename coordinateBar (quadric j) =
      C ((quadricBar j).2 : ℂ) * quadric (quadricBar j).1 := by
  fin_cases a <;> simp [quadric, termPolynomial, terms, quadricBar, coordinateBar] <;> ring

private theorem conjugate_block2 (a : Fin 12) :
    let j : Fin 48 := ⟨a.val + 24, by omega⟩
    rename coordinateBar (quadric j) =
      C ((quadricBar j).2 : ℂ) * quadric (quadricBar j).1 := by
  fin_cases a <;> simp [quadric, termPolynomial, terms, quadricBar, coordinateBar] <;> ring

private theorem conjugate_block3 (a : Fin 12) :
    let j : Fin 48 := ⟨a.val + 36, by omega⟩
    rename coordinateBar (quadric j) =
      C ((quadricBar j).2 : ℂ) * quadric (quadricBar j).1 := by
  fin_cases a <;> simp [quadric, termPolynomial, terms, quadricBar, coordinateBar] <;> ring

/-- Formal conjugation of a quadratic has two minus signs, hence this renaming. -/
theorem quadric_conjugate_polynomial (j : Fin 48) :
    rename coordinateBar (quadric j) =
      C ((quadricBar j).2 : ℂ) * quadric (quadricBar j).1 := by
  rcases j with ⟨j, hj⟩
  by_cases h0 : j < 12
  · exact conjugate_block0 ⟨j, h0⟩
  by_cases h1 : j < 24
  · have h := conjugate_block1 ⟨j - 12, by omega⟩
    simpa only [Nat.sub_add_cancel (by omega : 12 ≤ j)] using h
  by_cases h2 : j < 36
  · have h := conjugate_block2 ⟨j - 24, by omega⟩
    simpa only [Nat.sub_add_cancel (by omega : 24 ≤ j)] using h
  · have h := conjugate_block3 ⟨j - 36, by omega⟩
    simpa only [Nat.sub_add_cancel (by omega : 36 ≤ j)] using h

/-- Conjugation holds for precisely the stated real structure, not arbitrary y. -/
theorem conjugate_eval_quadric (y : Fin 24 → ℂ)
    (hy : ∀ j, y (coordinateBar j) = -conj (y j)) (j : Fin 48) :
    conj (eval y (quadric j)) = ((quadricBar j).2 : ℂ) * eval y (quadric (quadricBar j).1) := by
  have h : eval y (rename coordinateBar (quadric j)) = conj (eval y (quadric j)) := by
    simp [quadric, termPolynomial, hy]
  rw [quadric_conjugate_polynomial] at h
  simpa using h.symm

theorem realCoordinates_conjugate_quadric (z : Blocks) (j : Fin 48) :
    conj (eval (realCoordinates z) (quadric j)) =
      ((quadricBar j).2 : ℂ) * eval (realCoordinates z) (quadric (quadricBar j).1) :=
  conjugate_eval_quadric (realCoordinates z) (realCoordinates_bar z) j

/-- Reuse the already accepted native H selector/sign/conjugation convention. -/
def selectedH (y : Fin 24 → ℂ) (i : Fin 4) (a : Fin 3) : ℂ :=
  let s := NativeH.hSpec i a
  let q := eval y (quadric s.quadricIndex)
  let v := if s.conjugated then conj q else q
  if s.negated then -v else v

/-- The twelve supplied T representatives, in the Book's four-triple order. -/
def tIndex : Fin 4 → Fin 3 → Fin 48 :=
  ![![42,43,45], ![6,12,16], ![7,9,17], ![3,13,19]]

theorem selectedH_eq_Book (z : Blocks) (i : Fin 4) (a : Fin 3) :
    selectedH (realCoordinates z) i a = H z i a := by
  fin_cases i <;> fin_cases a <;>
    simp [selectedH, NativeH.hSpec, quadric, termPolynomial, terms, realCoordinates,
      H_apply, HValue] <;> ring

theorem selectedT_eq_Book (z : Blocks) (i : Fin 4) (a : Fin 3) :
    eval (realCoordinates z) (quadric (tIndex i a)) = T z i a := by
  fin_cases i <;> fin_cases a <;>
    simp [tIndex, quadric, termPolynomial, terms, realCoordinates, T_apply, TValue] <;> ring

/-- All48 numbered rows occur among the24 representatives and their proved partners. -/
theorem representatives_cover (j : Fin 48) :
    ∃ (i : Fin 4) (a : Fin 3),
      j = (NativeH.hSpec i a).quadricIndex ∨
      j = (quadricBar (NativeH.hSpec i a).quadricIndex).1 ∨
      j = tIndex i a ∨ j = (quadricBar (tIndex i a)).1 := by
  revert j
  decide

end Option2.NativeStress.BookHT.Dictionary

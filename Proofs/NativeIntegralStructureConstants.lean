module

public import NativeOctonionBasisProducts

@[expose] public section

/-!
# Sparse integer native numerator: the first whole-output block

The complete integer tensor N is defined once below in the frozen upper order.
This module proves N=2T for the ordered 01×12 block and its reverse, for
all octonion input indices and all 27 outputs. Other native blocks and the
global doubled-idempotency correspondence are not asserted here.

Coordinate labels are index bookkeeping for the exported tensor, not another algebra model.
The actual carrier, product and basis are the imported native ones. Classical
coordinate/bilinear arithmetic is background; the sparse N/native equality
is the specific project binding. There is no table-correspondence premise.

Imported model: compact-albert-recognition,
https://github.com/macgregor-sudo/compact-albert-recognition, commit
40d3b344180d9ddb78aaa2876873377c1e631515. Existing upstream rights/notices and
the exact prior extraction are recorded in THIRD_PARTY_NOTICES.md#native-albert-code.
No upstream proof body is copied here and no outbound license is chosen.
The tensor/evaluation adapter is first-party NativePolynomialEvaluationStaged;
its imported Mathlib APIs are at 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Thanks to the native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace NativePolynomial.IntegralStructureConstants

def diagonalCoordinateIndex (r : Fin 3) : Fin 27 :=
  ⟨r.val, lt_trans r.isLt (by decide)⟩

/-- Physical slots0,1,2 mean01,02,12; the index is ordinary, not modular. -/
def upperCoordinateIndex (s : Fin 3) (a : Fin 8) : Fin 27 :=
  ⟨3 + 8 * s.val + a.val, by
    have hs : 8 * s.val ≤ 16 := Nat.mul_le_mul_left 8 (Nat.le_of_lt_succ s.isLt)
    have ha : a.val ≤ 7 := Nat.le_of_lt_succ a.isLt
    exact lt_of_le_of_lt (Nat.add_le_add (Nat.add_le_add_left hs 3) ha) (by decide)⟩

abbrev CoordinateLabel := Fin 3 ⊕ (Fin 3 × Fin 8)

def coordinateLabel : Fin 27 → CoordinateLabel :=
  ![.inl 0, .inl 1, .inl 2,
    .inr (0, 0), .inr (0, 1), .inr (0, 2), .inr (0, 3),
    .inr (0, 4), .inr (0, 5), .inr (0, 6), .inr (0, 7),
    .inr (1, 0), .inr (1, 1), .inr (1, 2), .inr (1, 3),
    .inr (1, 4), .inr (1, 5), .inr (1, 6), .inr (1, 7),
    .inr (2, 0), .inr (2, 1), .inr (2, 2), .inr (2, 3),
    .inr (2, 4), .inr (2, 5), .inr (2, 6), .inr (2, 7)]

private def labelCoordinate : CoordinateLabel → Fin 27
  | .inl r => diagonalCoordinateIndex r
  | .inr (s, a) => upperCoordinateIndex s a

private theorem labelCoordinate_coordinateLabel (i : Fin 27) :
    labelCoordinate (coordinateLabel i) = i := by
  fin_cases i <;> rfl

private theorem coordinateLabel_diagonal (r : Fin 3) :
    coordinateLabel (diagonalCoordinateIndex r) = .inl r := by
  fin_cases r <;> rfl

private theorem coordinateLabel_upper (s : Fin 3) (a : Fin 8) :
    coordinateLabel (upperCoordinateIndex s a) = .inr (s, a) := by
  fin_cases s <;> fin_cases a <;> rfl

/-- Exhaustion in the existing Fin27 coordinates. The labels carry index
data only, with no algebra structure. -/
theorem coordinate_cases (i : Fin 27) :
    (∃ r : Fin 3, i = diagonalCoordinateIndex r) ∨
      ∃ s : Fin 3, ∃ a : Fin 8, i = upperCoordinateIndex s a := by
  have h := labelCoordinate_coordinateLabel i
  cases hLabel : coordinateLabel i with
  | inl r =>
      left
      exact ⟨r, by simpa [hLabel, labelCoordinate] using h.symm⟩
  | inr sa =>
      right
      exact ⟨sa.1, sa.2, by simpa [hLabel, labelCoordinate] using h.symm⟩

def slotEndpoints : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (0, 2), (1, 2)]

def integerCoordinate (i : Fin 27) (z : ℤ) (k : Fin 27) : ℤ :=
  if k = i then z else 0

def conjugationSign (a : Fin 8) : ℤ := if a = 0 then 1 else -1

def mixedUpperNumerator (s : Fin 3) (a b : Fin 8) (factor : ℤ)
    (k : Fin 27) : ℤ :=
  integerCoordinate (upperCoordinateIndex s (octonionBasisProductTable a b).1)
    (factor * (octonionBasisProductTable a b).2) k

/-- All physical upper-slot cases. Reverse inputs retain physical octonion
order, including the conjugated physical01/12 component. -/
def upperUpperNumerator (s t : Fin 3) (a b : Fin 8) (k : Fin 27) : ℤ :=
  if s = t then
    if a = b then
      integerCoordinate (diagonalCoordinateIndex (slotEndpoints s).1) 2 k +
        integerCoordinate (diagonalCoordinateIndex (slotEndpoints s).2) 2 k
    else 0
  else
    match s.val, t.val with
    | 0, 1 => mixedUpperNumerator 2 a b (conjugationSign a) k
    | 1, 0 => mixedUpperNumerator 2 b a (conjugationSign b) k
    | 0, 2 => mixedUpperNumerator 1 a b 1 k
    | 2, 0 => mixedUpperNumerator 1 b a 1 k
    | 1, 2 => mixedUpperNumerator 0 a b (conjugationSign b) k
    | 2, 1 => mixedUpperNumerator 0 b a (conjugationSign a) k
    | _, _ => 0

def numeratorFromLabels (i j : CoordinateLabel) (k : Fin 27) : ℤ :=
  match i, j with
  | .inl r, .inl t =>
      if r = t then integerCoordinate (diagonalCoordinateIndex r) 2 k else 0
  | .inl r, .inr (s, a) =>
      if r = (slotEndpoints s).1 ∨ r = (slotEndpoints s).2 then
        integerCoordinate (upperCoordinateIndex s a) 1 k else 0
  | .inr (s, a), .inl r =>
      if r = (slotEndpoints s).1 ∨ r = (slotEndpoints s).2 then
        integerCoordinate (upperCoordinateIndex s a) 1 k else 0
  | .inr (s, a), .inr (t, b) => upperUpperNumerator s t a b k

/-- The complete sparse integer tensor, fixed once for all later blocks.
Only the selected native block correspondence is proved here. -/
def numerator (i j k : Fin 27) : ℤ :=
  numeratorFromLabels (coordinateLabel i) (coordinateLabel j) k

theorem numerator_upper_upper (s t : Fin 3) (a b : Fin 8) (k : Fin 27) :
    numerator (upperCoordinateIndex s a) (upperCoordinateIndex t b) k =
      upperUpperNumerator s t a b k := by
  simp only [numerator, coordinateLabel_upper, numeratorFromLabels]

/-- Literal basis records in the one imported native Albert carrier. The 24
cases establish only the explicit coordinate index association. -/
theorem nativeCoordinateBasis_upper (s : Fin 3) (a : Fin 8) :
    nativeCoordinateBasis (upperCoordinateIndex s a) =
      ⟨0, 0, 0, if s = 0 then nativeOctonionBasis a else 0,
        if s = 1 then nativeOctonionBasis a else 0,
        if s = 2 then nativeOctonionBasis a else 0⟩ := by
  fin_cases s <;> fin_cases a <;> rfl

/-- All 64 products in this slot family, derived from the actual native
Jordan coordinate formulas and the passed actual octonion table theorem. -/
theorem jordan_upper01_upper12 (a b : Fin 8) :
    Glennie.jordan (nativeCoordinateBasis (upperCoordinateIndex 0 a))
        (nativeCoordinateBasis (upperCoordinateIndex 2 b)) =
      ((1 / 2 : ℝ) * (octonionBasisProductTable a b).2) •
        nativeCoordinateBasis (upperCoordinateIndex 1 (octonionBasisProductTable a b).1) := by
  rw [nativeCoordinateBasis_upper 0 a, nativeCoordinateBasis_upper 2 b,
    nativeCoordinateBasis_upper 1 (octonionBasisProductTable a b).1]
  have hZero : Glennie.octMul (0 : Glennie.Octonion) 0 = 0 := by
    simp [Glennie.octMul]
  apply Glennie.Albert.extExplicit
  · rw [Glennie.jordan_d0, Glennie.Albert.smul_d0]
    simp [Glennie.octDot_coordinates, Glennie.octNormSq, Quaternion.normSq_def']
  · rw [Glennie.jordan_d1, Glennie.Albert.smul_d1]
    simp [Glennie.octDot_coordinates, Glennie.octNormSq, Quaternion.normSq_def']
  · rw [Glennie.jordan_d2, Glennie.Albert.smul_d2]
    simp [Glennie.octDot_coordinates, Glennie.octNormSq, Quaternion.normSq_def']
  · rw [Glennie.jordan_o01, Glennie.Albert.smul_o01]
    simp [Glennie.octMul, Glennie.octConj]
  · rw [Glennie.jordan_o02, Glennie.Albert.smul_o02]
    simpa [hZero, smul_smul] using
      congrArg (fun z : Glennie.Octonion => (1 / 2 : ℝ) • z)
        (native_octonion_basis_product a b)
  · rw [Glennie.jordan_o12, Glennie.Albert.smul_o12]
    simp [Glennie.octMul, Glennie.octConj]

/-- The complete N definition agrees with 2T on every output of this whole
input-slot block; no missing-output condition is an input premise. -/
theorem numerator_eq_two_structureConstant_upper01_upper12
    (a b : Fin 8) (k : Fin 27) :
    (numerator (upperCoordinateIndex 0 a) (upperCoordinateIndex 2 b) k : ℝ) =
      2 * nativeStructureConstant (upperCoordinateIndex 0 a) (upperCoordinateIndex 2 b) k := by
  rw [numerator_upper_upper]
  have hBlock : upperUpperNumerator 0 2 a b k = mixedUpperNumerator 1 a b 1 k := rfl
  rw [hBlock]
  rw [nativeStructureConstant, jordan_upper01_upper12, upperCoordinates_smul]
  simp only [mixedUpperNumerator, one_mul, nativeCoordinateBasis,
    upperCoordinates_fromUpperCoordinates, Pi.smul_apply, smul_eq_mul]
  by_cases h : k = upperCoordinateIndex 1 (octonionBasisProductTable a b).1 <;>
    simp [integerCoordinate, h, eq_comm] <;> ring

/-- Reversing inputs uses the same physical table(a,b), not table(b,a). -/
theorem numerator_eq_two_structureConstant_upper12_upper01
    (a b : Fin 8) (k : Fin 27) :
    (numerator (upperCoordinateIndex 2 b) (upperCoordinateIndex 0 a) k : ℝ) =
      2 * nativeStructureConstant (upperCoordinateIndex 2 b) (upperCoordinateIndex 0 a) k := by
  have hNumerator :
      numerator (upperCoordinateIndex 2 b) (upperCoordinateIndex 0 a) k =
        numerator (upperCoordinateIndex 0 a) (upperCoordinateIndex 2 b) k := by
    rw [numerator_upper_upper, numerator_upper_upper]
    rfl
  have hProduct :
      nativeStructureConstant (upperCoordinateIndex 2 b) (upperCoordinateIndex 0 a) k =
        nativeStructureConstant (upperCoordinateIndex 0 a) (upperCoordinateIndex 2 b) k := by
    unfold nativeStructureConstant
    rw [Glennie.jordan_comm]
  rw [hNumerator, hProduct]
  exact numerator_eq_two_structureConstant_upper01_upper12 a b k

end NativePolynomial.IntegralStructureConstants



#check @NativePolynomial.IntegralStructureConstants.diagonalCoordinateIndex
#check @NativePolynomial.IntegralStructureConstants.upperCoordinateIndex
#check @NativePolynomial.IntegralStructureConstants.coordinate_cases
#check @NativePolynomial.IntegralStructureConstants.numerator
#check @NativePolynomial.IntegralStructureConstants.numerator_upper_upper
#check @NativePolynomial.IntegralStructureConstants.nativeCoordinateBasis_upper
#check @NativePolynomial.IntegralStructureConstants.jordan_upper01_upper12
#check @NativePolynomial.IntegralStructureConstants.numerator_eq_two_structureConstant_upper01_upper12
#check @NativePolynomial.IntegralStructureConstants.numerator_eq_two_structureConstant_upper12_upper01

#print axioms NativePolynomial.IntegralStructureConstants.coordinate_cases
#print axioms NativePolynomial.IntegralStructureConstants.nativeCoordinateBasis_upper
#print axioms NativePolynomial.IntegralStructureConstants.jordan_upper01_upper12
#print axioms NativePolynomial.IntegralStructureConstants.numerator_eq_two_structureConstant_upper01_upper12
#print axioms NativePolynomial.IntegralStructureConstants.numerator_eq_two_structureConstant_upper12_upper01

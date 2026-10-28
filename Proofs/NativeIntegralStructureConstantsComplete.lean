module

public import NativeIntegralStructureConstants

@[expose] public section

/-!
# Completing the actual native integer numerator binding

The integer tensor N and actual native model are imported unchanged. Small
basis conjugation/dot identities supply the remaining physical Jordan blocks;
coordinate_cases then proves N=2T for all indices. Octonion indices and output
coordinates remain symbolic in the Jordan-block proofs. No 27³ table check,
second carrier/product, or assumed coefficient correspondence is used.

Classical coordinate/bilinear arithmetic is background. The exact native
signs, slot order, factor 2 and coefficient binding are project-specific work.
The doubled polynomial residual is the next connected composition; full 3159
row/data binding is not asserted here.

Imported native source: compact-albert-recognition,
https://github.com/macgregor-sudo/compact-albert-recognition, commit
40d3b344180d9ddb78aaa2876873377c1e631515. Existing rights/notices and the exact
prior law extraction remain recorded in THIRD_PARTY_NOTICES.md#native-albert-code.
No upstream proof body is copied; three-line first-party label proofs are
re-established because their preceding-module helpers are private. No outbound
license is chosen. Imported Mathlib APIs are at 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Thanks to the native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace NativePolynomial.IntegralStructureConstants

private theorem label_diagonal (r : Fin 3) :
    coordinateLabel (diagonalCoordinateIndex r) = .inl r := by
  fin_cases r <;> rfl

private theorem label_upper (s : Fin 3) (a : Fin 8) :
    coordinateLabel (upperCoordinateIndex s a) = .inr (s, a) := by
  fin_cases s <;> fin_cases a <;> rfl

/-- Actual native conjugation in the same eight-element basis. -/
theorem native_octonion_basis_conjugate (a : Fin 8) :
    Glennie.octConj (nativeOctonionBasis a) =
      (conjugationSign a : ℝ) • nativeOctonionBasis a := by
  fin_cases a <;> apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [nativeOctonionBasis, firstUpperCoordinateIndex,
      nativeCoordinateBasis, fromUpperCoordinates, conjugationSign, Glennie.octConj]

private theorem dot_row_zero (b : Fin 8) :
    Glennie.octDot (nativeOctonionBasis 0) (nativeOctonionBasis b) =
      if (0 : Fin 8) = b then 1 else 0 := by
  fin_cases b <;> norm_num [Glennie.octDot_coordinates, Glennie.octNormSq,
    Quaternion.normSq_def', nativeOctonionBasis, firstUpperCoordinateIndex,
    nativeCoordinateBasis, fromUpperCoordinates]

private theorem dot_row_one (b : Fin 8) :
    Glennie.octDot (nativeOctonionBasis 1) (nativeOctonionBasis b) =
      if (1 : Fin 8) = b then 1 else 0 := by
  fin_cases b <;> norm_num [Glennie.octDot_coordinates, Glennie.octNormSq,
    Quaternion.normSq_def', nativeOctonionBasis, firstUpperCoordinateIndex,
    nativeCoordinateBasis, fromUpperCoordinates]

private theorem dot_row_two (b : Fin 8) :
    Glennie.octDot (nativeOctonionBasis 2) (nativeOctonionBasis b) =
      if (2 : Fin 8) = b then 1 else 0 := by
  fin_cases b <;> norm_num [Glennie.octDot_coordinates, Glennie.octNormSq,
    Quaternion.normSq_def', nativeOctonionBasis, firstUpperCoordinateIndex,
    nativeCoordinateBasis, fromUpperCoordinates]

private theorem dot_row_three (b : Fin 8) :
    Glennie.octDot (nativeOctonionBasis 3) (nativeOctonionBasis b) =
      if (3 : Fin 8) = b then 1 else 0 := by
  fin_cases b <;> norm_num [Glennie.octDot_coordinates, Glennie.octNormSq,
    Quaternion.normSq_def', nativeOctonionBasis, firstUpperCoordinateIndex,
    nativeCoordinateBasis, fromUpperCoordinates]

private theorem dot_row_four (b : Fin 8) :
    Glennie.octDot (nativeOctonionBasis 4) (nativeOctonionBasis b) =
      if (4 : Fin 8) = b then 1 else 0 := by
  fin_cases b <;> norm_num [Glennie.octDot_coordinates, Glennie.octNormSq,
    Quaternion.normSq_def', nativeOctonionBasis, firstUpperCoordinateIndex,
    nativeCoordinateBasis, fromUpperCoordinates]

private theorem dot_row_five (b : Fin 8) :
    Glennie.octDot (nativeOctonionBasis 5) (nativeOctonionBasis b) =
      if (5 : Fin 8) = b then 1 else 0 := by
  fin_cases b <;> norm_num [Glennie.octDot_coordinates, Glennie.octNormSq,
    Quaternion.normSq_def', nativeOctonionBasis, firstUpperCoordinateIndex,
    nativeCoordinateBasis, fromUpperCoordinates]

private theorem dot_row_six (b : Fin 8) :
    Glennie.octDot (nativeOctonionBasis 6) (nativeOctonionBasis b) =
      if (6 : Fin 8) = b then 1 else 0 := by
  fin_cases b <;> norm_num [Glennie.octDot_coordinates, Glennie.octNormSq,
    Quaternion.normSq_def', nativeOctonionBasis, firstUpperCoordinateIndex,
    nativeCoordinateBasis, fromUpperCoordinates]

private theorem dot_row_seven (b : Fin 8) :
    Glennie.octDot (nativeOctonionBasis 7) (nativeOctonionBasis b) =
      if (7 : Fin 8) = b then 1 else 0 := by
  fin_cases b <;> norm_num [Glennie.octDot_coordinates, Glennie.octNormSq,
    Quaternion.normSq_def', nativeOctonionBasis, firstUpperCoordinateIndex,
    nativeCoordinateBasis, fromUpperCoordinates]

/-- The actual positive octonion dot product, not Re(Ea*Eb). -/
theorem native_octonion_basis_dot (a b : Fin 8) :
    Glennie.octDot (nativeOctonionBasis a) (nativeOctonionBasis b) =
      if a = b then 1 else 0 := by
  fin_cases a
  · exact dot_row_zero b
  · exact dot_row_one b
  · exact dot_row_two b
  · exact dot_row_three b
  · exact dot_row_four b
  · exact dot_row_five b
  · exact dot_row_six b
  · exact dot_row_seven b

theorem nativeCoordinateBasis_diagonal (r : Fin 3) :
    nativeCoordinateBasis (diagonalCoordinateIndex r) =
      ⟨if r = 0 then 1 else 0, if r = 1 then 1 else 0,
        if r = 2 then 1 else 0, 0, 0, 0⟩ := by
  fin_cases r <;> rfl

private theorem coordinates_zero : upperCoordinates (0 : Glennie.Albert) = 0 :=
  map_zero upperCoordinateEquiv

private theorem octDot_zero_left (u : Glennie.Octonion) : Glennie.octDot 0 u = 0 := by
  simp [Glennie.octDot_coordinates]

private theorem octDot_zero_right (u : Glennie.Octonion) : Glennie.octDot u 0 = 0 := by
  simp [Glennie.octDot_coordinates]

private theorem basis_coordinates (i k : Fin 27) :
    upperCoordinates (nativeCoordinateBasis i) k = if k = i then 1 else 0 := by
  simp [nativeCoordinateBasis, eq_comm]

theorem jordan_diagonal_diagonal (r t : Fin 3) :
    Glennie.jordan (nativeCoordinateBasis (diagonalCoordinateIndex r))
        (nativeCoordinateBasis (diagonalCoordinateIndex t)) =
      if r = t then nativeCoordinateBasis (diagonalCoordinateIndex r) else 0 := by
  simp only [nativeCoordinateBasis_diagonal]
  fin_cases r <;> fin_cases t <;> apply Glennie.Albert.extExplicit <;>
    simp [Glennie.jordan_d0, Glennie.jordan_d1, Glennie.jordan_d2,
      Glennie.jordan_o01, Glennie.jordan_o02, Glennie.jordan_o12,
      Glennie.octDot_coordinates, Glennie.octNormSq, Quaternion.normSq_def',
      Glennie.octMul, Glennie.octConj]

theorem jordan_diagonal_upper (r s : Fin 3) (a : Fin 8) :
    Glennie.jordan (nativeCoordinateBasis (diagonalCoordinateIndex r))
        (nativeCoordinateBasis (upperCoordinateIndex s a)) =
      (if r = (slotEndpoints s).1 ∨ r = (slotEndpoints s).2 then (1 / 2 : ℝ) else 0) •
        nativeCoordinateBasis (upperCoordinateIndex s a) := by
  simp only [nativeCoordinateBasis_diagonal, nativeCoordinateBasis_upper]
  fin_cases r <;> fin_cases s <;> apply Glennie.Albert.extExplicit <;>
    simp [slotEndpoints, Glennie.jordan_d0, Glennie.jordan_d1, Glennie.jordan_d2,
      Glennie.jordan_o01, Glennie.jordan_o02, Glennie.jordan_o12,
      Glennie.octDot_coordinates, Glennie.octNormSq, Quaternion.normSq_def',
      Glennie.octMul, Glennie.octConj, Prod.mk_zero_zero]

theorem jordan_same_upper_slot (s : Fin 3) (a b : Fin 8) :
    Glennie.jordan (nativeCoordinateBasis (upperCoordinateIndex s a))
        (nativeCoordinateBasis (upperCoordinateIndex s b)) =
      (if a = b then (1 : ℝ) else 0) •
        (nativeCoordinateBasis (diagonalCoordinateIndex (slotEndpoints s).1) +
          nativeCoordinateBasis (diagonalCoordinateIndex (slotEndpoints s).2)) := by
  have hDot := native_octonion_basis_dot a b
  simp only [nativeCoordinateBasis_upper, nativeCoordinateBasis_diagonal]
  fin_cases s <;> apply Glennie.Albert.extExplicit <;>
    simp [slotEndpoints, hDot, octDot_zero_left, octDot_zero_right,
      Glennie.jordan_d0, Glennie.jordan_d1, Glennie.jordan_d2,
      Glennie.jordan_o01, Glennie.jordan_o02, Glennie.jordan_o12,
      Glennie.octNormSq, Quaternion.normSq_def',
      Glennie.octMul, Glennie.octConj]
  all_goals
    by_cases hEqual : a = b <;> simp [hEqual, Prod.mk_zero_zero]

theorem jordan_upper01_upper02 (a b : Fin 8) :
    Glennie.jordan (nativeCoordinateBasis (upperCoordinateIndex 0 a))
        (nativeCoordinateBasis (upperCoordinateIndex 1 b)) =
      ((1 / 2 : ℝ) * (conjugationSign a : ℝ) *
        (octonionBasisProductTable a b).2) •
        nativeCoordinateBasis (upperCoordinateIndex 2 (octonionBasisProductTable a b).1) := by
  have hProduct :
      Glennie.octMul (Glennie.octConj (nativeOctonionBasis a)) (nativeOctonionBasis b) =
        ((conjugationSign a : ℝ) * (octonionBasisProductTable a b).2) •
          nativeOctonionBasis (octonionBasisProductTable a b).1 := by
    rw [native_octonion_basis_conjugate, Glennie.octMul_smul_left,
      native_octonion_basis_product, smul_smul]
  rw [nativeCoordinateBasis_upper 0 a, nativeCoordinateBasis_upper 1 b,
    nativeCoordinateBasis_upper 2 (octonionBasisProductTable a b).1]
  have hZero : Glennie.octMul (0 : Glennie.Octonion) 0 = 0 := by simp [Glennie.octMul]
  have hConjZero : Glennie.octConj (0 : Glennie.Octonion) = 0 := by
    simp [Glennie.octConj]
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
    simp [Glennie.octMul, Glennie.octConj]
  · rw [Glennie.jordan_o12, Glennie.Albert.smul_o12]
    simpa [hConjZero, hZero, smul_smul, mul_assoc] using
      congrArg (fun z : Glennie.Octonion => (1 / 2 : ℝ) • z) hProduct

theorem jordan_upper02_upper12 (a b : Fin 8) :
    Glennie.jordan (nativeCoordinateBasis (upperCoordinateIndex 1 a))
        (nativeCoordinateBasis (upperCoordinateIndex 2 b)) =
      ((1 / 2 : ℝ) * (conjugationSign b : ℝ) *
        (octonionBasisProductTable a b).2) •
        nativeCoordinateBasis (upperCoordinateIndex 0 (octonionBasisProductTable a b).1) := by
  have hProduct :
      Glennie.octMul (nativeOctonionBasis a) (Glennie.octConj (nativeOctonionBasis b)) =
        ((conjugationSign b : ℝ) * (octonionBasisProductTable a b).2) •
          nativeOctonionBasis (octonionBasisProductTable a b).1 := by
    rw [native_octonion_basis_conjugate, Glennie.octMul_smul_right,
      native_octonion_basis_product, smul_smul]
  rw [nativeCoordinateBasis_upper 1 a, nativeCoordinateBasis_upper 2 b,
    nativeCoordinateBasis_upper 0 (octonionBasisProductTable a b).1]
  have hZero : Glennie.octMul (0 : Glennie.Octonion) 0 = 0 := by simp [Glennie.octMul]
  have hConjZero : Glennie.octConj (0 : Glennie.Octonion) = 0 := by
    simp [Glennie.octConj]
  apply Glennie.Albert.extExplicit
  · rw [Glennie.jordan_d0, Glennie.Albert.smul_d0]
    simp [Glennie.octDot_coordinates, Glennie.octNormSq, Quaternion.normSq_def']
  · rw [Glennie.jordan_d1, Glennie.Albert.smul_d1]
    simp [Glennie.octDot_coordinates, Glennie.octNormSq, Quaternion.normSq_def']
  · rw [Glennie.jordan_d2, Glennie.Albert.smul_d2]
    simp [Glennie.octDot_coordinates, Glennie.octNormSq, Quaternion.normSq_def']
  · rw [Glennie.jordan_o01, Glennie.Albert.smul_o01]
    simpa [hConjZero, hZero, smul_smul, mul_assoc] using
      congrArg (fun z : Glennie.Octonion => (1 / 2 : ℝ) • z) hProduct
  · rw [Glennie.jordan_o02, Glennie.Albert.smul_o02]
    simp [Glennie.octMul, Glennie.octConj]
  · rw [Glennie.jordan_o12, Glennie.Albert.smul_o12]
    simp [Glennie.octMul, Glennie.octConj]

/-- Symmetry of the fixed integer definition, retaining physical slot order. -/
theorem numerator_comm (i j k : Fin 27) : numerator i j k = numerator j i k := by
  rcases coordinate_cases i with ⟨r, rfl⟩ | ⟨s, a, rfl⟩
  · rcases coordinate_cases j with ⟨t, rfl⟩ | ⟨t, b, rfl⟩
    · fin_cases r <;> fin_cases t <;>
        simp [numerator, label_diagonal, numeratorFromLabels]
    · simp [numerator, label_diagonal, label_upper, numeratorFromLabels]
  · rcases coordinate_cases j with ⟨r, rfl⟩ | ⟨t, b, rfl⟩
    · simp [numerator, label_diagonal, label_upper, numeratorFromLabels]
    · fin_cases s <;> fin_cases t <;>
        simp [numerator_upper_upper, upperUpperNumerator, eq_comm]

private theorem structureConstant_comm (i j k : Fin 27) :
    nativeStructureConstant i j k = nativeStructureConstant j i k := by
  unfold nativeStructureConstant
  rw [Glennie.jordan_comm]

private theorem reverse_block {i j k : Fin 27}
    (h : (numerator j i k : ℝ) = 2 * nativeStructureConstant j i k) :
    (numerator i j k : ℝ) = 2 * nativeStructureConstant i j k := by
  rw [numerator_comm i j k, structureConstant_comm i j k]
  exact h

theorem numerator_eq_two_structureConstant_diagonal_diagonal (r t : Fin 3) (k : Fin 27) :
    (numerator (diagonalCoordinateIndex r) (diagonalCoordinateIndex t) k : ℝ) =
      2 * nativeStructureConstant (diagonalCoordinateIndex r) (diagonalCoordinateIndex t) k := by
  rw [nativeStructureConstant, jordan_diagonal_diagonal]
  by_cases h : r = t <;> by_cases hk : k = diagonalCoordinateIndex r <;>
    simp [numerator, label_diagonal, numeratorFromLabels, integerCoordinate,
      h, hk, basis_coordinates, coordinates_zero]

theorem numerator_eq_two_structureConstant_diagonal_upper
    (r s : Fin 3) (a : Fin 8) (k : Fin 27) :
    (numerator (diagonalCoordinateIndex r) (upperCoordinateIndex s a) k : ℝ) =
      2 * nativeStructureConstant (diagonalCoordinateIndex r) (upperCoordinateIndex s a) k := by
  rw [nativeStructureConstant, jordan_diagonal_upper, upperCoordinates_smul]
  simp only [Pi.smul_apply, smul_eq_mul, basis_coordinates]
  by_cases h : r = (slotEndpoints s).1 ∨ r = (slotEndpoints s).2 <;>
    by_cases hk : k = upperCoordinateIndex s a <;>
    norm_num [numerator, label_diagonal, label_upper, numeratorFromLabels,
      integerCoordinate, h, hk]

theorem numerator_eq_two_structureConstant_same_upper_slot
    (s : Fin 3) (a b : Fin 8) (k : Fin 27) :
    (numerator (upperCoordinateIndex s a) (upperCoordinateIndex s b) k : ℝ) =
      2 * nativeStructureConstant (upperCoordinateIndex s a) (upperCoordinateIndex s b) k := by
  rw [numerator_upper_upper, nativeStructureConstant, jordan_same_upper_slot,
    upperCoordinates_smul, upperCoordinates_add]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, basis_coordinates]
  by_cases h : a = b <;>
    by_cases hFirst : k = diagonalCoordinateIndex (slotEndpoints s).1 <;>
    by_cases hSecond : k = diagonalCoordinateIndex (slotEndpoints s).2 <;>
    norm_num [upperUpperNumerator, integerCoordinate, h, hFirst, hSecond]
  all_goals split_ifs <;> norm_num

theorem numerator_eq_two_structureConstant_upper01_upper02
    (a b : Fin 8) (k : Fin 27) :
    (numerator (upperCoordinateIndex 0 a) (upperCoordinateIndex 1 b) k : ℝ) =
      2 * nativeStructureConstant (upperCoordinateIndex 0 a) (upperCoordinateIndex 1 b) k := by
  rw [numerator_upper_upper]
  have hBlock : upperUpperNumerator 0 1 a b k =
      mixedUpperNumerator 2 a b (conjugationSign a) k := rfl
  rw [hBlock, nativeStructureConstant, jordan_upper01_upper02, upperCoordinates_smul]
  simp only [mixedUpperNumerator, Pi.smul_apply, smul_eq_mul, basis_coordinates]
  by_cases h : k = upperCoordinateIndex 2 (octonionBasisProductTable a b).1 <;>
    simp [integerCoordinate, h, eq_comm, Int.cast_mul] <;> ring

theorem numerator_eq_two_structureConstant_upper02_upper12
    (a b : Fin 8) (k : Fin 27) :
    (numerator (upperCoordinateIndex 1 a) (upperCoordinateIndex 2 b) k : ℝ) =
      2 * nativeStructureConstant (upperCoordinateIndex 1 a) (upperCoordinateIndex 2 b) k := by
  rw [numerator_upper_upper]
  have hBlock : upperUpperNumerator 1 2 a b k =
      mixedUpperNumerator 0 a b (conjugationSign b) k := rfl
  rw [hBlock, nativeStructureConstant, jordan_upper02_upper12, upperCoordinates_smul]
  simp only [mixedUpperNumerator, Pi.smul_apply, smul_eq_mul, basis_coordinates]
  by_cases h : k = upperCoordinateIndex 0 (octonionBasisProductTable a b).1 <;>
    simp [integerCoordinate, h, eq_comm, Int.cast_mul] <;> ring

/-- Full coefficient binding to the one imported native product. This proves
all indices by structural blocks, not by enumerating 27³ tensor cells. -/
theorem numerator_cast_eq_two_nativeStructureConstant (i j k : Fin 27) :
    (numerator i j k : ℝ) = 2 * nativeStructureConstant i j k := by
  rcases coordinate_cases i with ⟨r, rfl⟩ | ⟨s, a, rfl⟩
  · rcases coordinate_cases j with ⟨t, rfl⟩ | ⟨t, b, rfl⟩
    · exact numerator_eq_two_structureConstant_diagonal_diagonal r t k
    · exact numerator_eq_two_structureConstant_diagonal_upper r t b k
  · rcases coordinate_cases j with ⟨r, rfl⟩ | ⟨t, b, rfl⟩
    · exact reverse_block (numerator_eq_two_structureConstant_diagonal_upper r s a k)
    · fin_cases s <;> fin_cases t
      · exact numerator_eq_two_structureConstant_same_upper_slot 0 a b k
      · exact numerator_eq_two_structureConstant_upper01_upper02 a b k
      · exact numerator_eq_two_structureConstant_upper01_upper12 a b k
      · exact reverse_block (numerator_eq_two_structureConstant_upper01_upper02 b a k)
      · exact numerator_eq_two_structureConstant_same_upper_slot 1 a b k
      · exact numerator_eq_two_structureConstant_upper02_upper12 a b k
      · exact reverse_block (numerator_eq_two_structureConstant_upper01_upper12 b a k)
      · exact reverse_block (numerator_eq_two_structureConstant_upper02_upper12 b a k)
      · exact numerator_eq_two_structureConstant_same_upper_slot 2 a b k

end NativePolynomial.IntegralStructureConstants



#check @NativePolynomial.IntegralStructureConstants.native_octonion_basis_conjugate
#check @NativePolynomial.IntegralStructureConstants.native_octonion_basis_dot
#check @NativePolynomial.IntegralStructureConstants.nativeCoordinateBasis_diagonal
#check @NativePolynomial.IntegralStructureConstants.jordan_diagonal_diagonal
#check @NativePolynomial.IntegralStructureConstants.jordan_diagonal_upper
#check @NativePolynomial.IntegralStructureConstants.jordan_same_upper_slot
#check @NativePolynomial.IntegralStructureConstants.jordan_upper01_upper02
#check @NativePolynomial.IntegralStructureConstants.jordan_upper02_upper12
#check @NativePolynomial.IntegralStructureConstants.numerator_comm
#check @NativePolynomial.IntegralStructureConstants.numerator_eq_two_structureConstant_diagonal_diagonal
#check @NativePolynomial.IntegralStructureConstants.numerator_eq_two_structureConstant_diagonal_upper
#check @NativePolynomial.IntegralStructureConstants.numerator_eq_two_structureConstant_same_upper_slot
#check @NativePolynomial.IntegralStructureConstants.numerator_eq_two_structureConstant_upper01_upper02
#check @NativePolynomial.IntegralStructureConstants.numerator_eq_two_structureConstant_upper02_upper12
#check @NativePolynomial.IntegralStructureConstants.numerator_cast_eq_two_nativeStructureConstant

#print axioms NativePolynomial.IntegralStructureConstants.native_octonion_basis_conjugate
#print axioms NativePolynomial.IntegralStructureConstants.native_octonion_basis_dot
#print axioms NativePolynomial.IntegralStructureConstants.nativeCoordinateBasis_diagonal
#print axioms NativePolynomial.IntegralStructureConstants.jordan_diagonal_diagonal
#print axioms NativePolynomial.IntegralStructureConstants.jordan_diagonal_upper
#print axioms NativePolynomial.IntegralStructureConstants.jordan_same_upper_slot
#print axioms NativePolynomial.IntegralStructureConstants.jordan_upper01_upper02
#print axioms NativePolynomial.IntegralStructureConstants.jordan_upper02_upper12
#print axioms NativePolynomial.IntegralStructureConstants.numerator_comm
#print axioms NativePolynomial.IntegralStructureConstants.numerator_eq_two_structureConstant_diagonal_diagonal
#print axioms NativePolynomial.IntegralStructureConstants.numerator_eq_two_structureConstant_diagonal_upper
#print axioms NativePolynomial.IntegralStructureConstants.numerator_eq_two_structureConstant_same_upper_slot
#print axioms NativePolynomial.IntegralStructureConstants.numerator_eq_two_structureConstant_upper01_upper02
#print axioms NativePolynomial.IntegralStructureConstants.numerator_eq_two_structureConstant_upper02_upper12
#print axioms NativePolynomial.IntegralStructureConstants.numerator_cast_eq_two_nativeStructureConstant

module

public import NativePolynomialEvaluationStaged

@[expose] public section
set_option backward.proofsInPublic true

/-!
# Signed basis products in the actual native octonions

This first-party proof establishes the explicit 64-entry signed table against
Glennie.octMul. The basis is read from the existing native Albert coordinate
basis; there is no second octonion carrier, product or algebra structure.
The order is (1,i,j,k,ell,iell,n,kell), n=jell. In particular i*n=-kell,
whereas n*i=kell. An entry records (output index, integer sign).

Classical Cayley–Dickson basis arithmetic is mathematical background. The
proved equality to this exact native basis/table is the project convention
binding. It is a prerequisite, not the full N=2T numerator theorem, the full
integral residual family, or a finite certificate application.

The actual model and its coordinate formulas are imported from
compact-albert-recognition, https://github.com/macgregor-sudo/compact-albert-recognition,
commit 40d3b344180d9ddb78aaa2876873377c1e631515. Exact upstream rights/notices
remain as recorded in THIRD_PARTY_NOTICES.md#native-albert-code. No upstream proof body
is copied here; no outbound license is chosen. The first-party coordinate
adapter is NativePolynomialEvaluationStaged; its imported Mathlib APIs are
at 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Thanks to the native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace NativePolynomial

/-- Native upper slot 01, with an explicit ordinary index and bound. -/
def firstUpperCoordinateIndex (a : Fin 8) : Fin 27 :=
  ⟨3 + a.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left a.isLt 3) (Nat.le_of_ble_eq_true rfl)⟩

/-- Actual native octonion basis, extracted from the existing Albert basis. -/
def nativeOctonionBasis (a : Fin 8) : Glennie.Octonion :=
  (nativeCoordinateBasis (firstUpperCoordinateIndex a)).o01

/-- Each literal is (output basis index, integer sign). The table is input
data whose identity with actual native multiplication is proved below. -/
def octonionBasisProductTable : Fin 8 → Fin 8 → Fin 8 × ℤ :=
  ![![(0, 1), (1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (7, 1)],
    ![(1, 1), (0, -1), (3, 1), (2, -1), (5, 1), (4, -1), (7, -1), (6, 1)],
    ![(2, 1), (3, -1), (0, -1), (1, 1), (6, 1), (7, 1), (4, -1), (5, -1)],
    ![(3, 1), (2, 1), (1, -1), (0, -1), (7, 1), (6, -1), (5, 1), (4, -1)],
    ![(4, 1), (5, -1), (6, -1), (7, -1), (0, -1), (1, 1), (2, 1), (3, 1)],
    ![(5, 1), (4, 1), (7, -1), (6, 1), (1, -1), (0, -1), (3, -1), (2, 1)],
    ![(6, 1), (7, 1), (4, 1), (5, -1), (2, -1), (3, 1), (0, -1), (1, -1)],
    ![(7, 1), (6, -1), (5, 1), (4, 1), (3, -1), (2, -1), (1, 1), (0, -1)]]

private theorem basis_product_row_zero (b : Fin 8) :
    Glennie.octMul (nativeOctonionBasis 0) (nativeOctonionBasis b) =
      ((octonionBasisProductTable 0 b).2 : ℝ) •
        nativeOctonionBasis (octonionBasisProductTable 0 b).1 := by
  fin_cases b <;> apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [nativeOctonionBasis, firstUpperCoordinateIndex,
      octonionBasisProductTable, nativeCoordinateBasis, fromUpperCoordinates,
      Glennie.octMul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem basis_product_row_one (b : Fin 8) :
    Glennie.octMul (nativeOctonionBasis 1) (nativeOctonionBasis b) =
      ((octonionBasisProductTable 1 b).2 : ℝ) •
        nativeOctonionBasis (octonionBasisProductTable 1 b).1 := by
  fin_cases b <;> apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [nativeOctonionBasis, firstUpperCoordinateIndex,
      octonionBasisProductTable, nativeCoordinateBasis, fromUpperCoordinates,
      Glennie.octMul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem basis_product_row_two (b : Fin 8) :
    Glennie.octMul (nativeOctonionBasis 2) (nativeOctonionBasis b) =
      ((octonionBasisProductTable 2 b).2 : ℝ) •
        nativeOctonionBasis (octonionBasisProductTable 2 b).1 := by
  fin_cases b <;> apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [nativeOctonionBasis, firstUpperCoordinateIndex,
      octonionBasisProductTable, nativeCoordinateBasis, fromUpperCoordinates,
      Glennie.octMul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem basis_product_row_three (b : Fin 8) :
    Glennie.octMul (nativeOctonionBasis 3) (nativeOctonionBasis b) =
      ((octonionBasisProductTable 3 b).2 : ℝ) •
        nativeOctonionBasis (octonionBasisProductTable 3 b).1 := by
  fin_cases b <;> apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [nativeOctonionBasis, firstUpperCoordinateIndex,
      octonionBasisProductTable, nativeCoordinateBasis, fromUpperCoordinates,
      Glennie.octMul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem basis_product_row_four (b : Fin 8) :
    Glennie.octMul (nativeOctonionBasis 4) (nativeOctonionBasis b) =
      ((octonionBasisProductTable 4 b).2 : ℝ) •
        nativeOctonionBasis (octonionBasisProductTable 4 b).1 := by
  fin_cases b <;> apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [nativeOctonionBasis, firstUpperCoordinateIndex,
      octonionBasisProductTable, nativeCoordinateBasis, fromUpperCoordinates,
      Glennie.octMul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem basis_product_row_five (b : Fin 8) :
    Glennie.octMul (nativeOctonionBasis 5) (nativeOctonionBasis b) =
      ((octonionBasisProductTable 5 b).2 : ℝ) •
        nativeOctonionBasis (octonionBasisProductTable 5 b).1 := by
  fin_cases b <;> apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [nativeOctonionBasis, firstUpperCoordinateIndex,
      octonionBasisProductTable, nativeCoordinateBasis, fromUpperCoordinates,
      Glennie.octMul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem basis_product_row_six (b : Fin 8) :
    Glennie.octMul (nativeOctonionBasis 6) (nativeOctonionBasis b) =
      ((octonionBasisProductTable 6 b).2 : ℝ) •
        nativeOctonionBasis (octonionBasisProductTable 6 b).1 := by
  fin_cases b <;> apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [nativeOctonionBasis, firstUpperCoordinateIndex,
      octonionBasisProductTable, nativeCoordinateBasis, fromUpperCoordinates,
      Glennie.octMul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem basis_product_row_seven (b : Fin 8) :
    Glennie.octMul (nativeOctonionBasis 7) (nativeOctonionBasis b) =
      ((octonionBasisProductTable 7 b).2 : ℝ) •
        nativeOctonionBasis (octonionBasisProductTable 7 b).1 := by
  fin_cases b <;> apply Prod.ext <;> apply Quaternion.ext <;>
    norm_num [nativeOctonionBasis, firstUpperCoordinateIndex,
      octonionBasisProductTable, nativeCoordinateBasis, fromUpperCoordinates,
      Glennie.octMul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]

/-- All 64 actual native basis products, with no table-correspondence premise.
Eight row lemmas keep declaration-level cost bounded and visible. -/
theorem native_octonion_basis_product (a b : Fin 8) :
    Glennie.octMul (nativeOctonionBasis a) (nativeOctonionBasis b) =
      ((octonionBasisProductTable a b).2 : ℝ) •
        nativeOctonionBasis (octonionBasisProductTable a b).1 := by
  fin_cases a
  · exact basis_product_row_zero b
  · exact basis_product_row_one b
  · exact basis_product_row_two b
  · exact basis_product_row_three b
  · exact basis_product_row_four b
  · exact basis_product_row_five b
  · exact basis_product_row_six b
  · exact basis_product_row_seven b

end NativePolynomial



#check @NativePolynomial.firstUpperCoordinateIndex
#check @NativePolynomial.nativeOctonionBasis
#check @NativePolynomial.octonionBasisProductTable
#check @NativePolynomial.native_octonion_basis_product

#print axioms NativePolynomial.native_octonion_basis_product

/-
# Original native complex anchors and their coordinate binder

The selected phase points below use the original native vv*/3 field expansion
for v=(1,u,w), together with the three coordinate points. They do not call a
Tits map, inverse coordinates, or the included-point definitions.
The universal helper is a fixed-scale outer product, not a normalized
projector for arbitrary u,w: its norm-square diagonals are retained.
The packet2.2 definition assumes unit u,w and fixes denominator3; MASTER6.3
uses denominator 1+normSq(u)+normSq(w) for a general ray. The separate
character-unit-norm identity identifying those denominators is not asserted here.
The raw complex
points use a=t,b=s-t, exactly the original frame/outcome convention; the
finite raw-label table is checked separately from the point equalities.

The proof only uses binary complex multiplication/conjugation inside the
actual quaternion-pair octonions. No RingHom into all octonions, global
associativity, idempotency, orthogonality or MUB statement is asserted.
The literal formulas are original packet2.2/10.1 and CKM arXiv:1308.3188v4
Section8.2; the complex type's a+b=s grouping agrees with these labels.
These locally authored finite coordinate proofs make no novelty claim.
Inherited native-model and mathlib notices remain in the imported sources.
Thanks to the original mathematical authors and the Lean/mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/
module

public import NativeIncludedQuartetReadouts

@[expose] public section
set_option backward.proofsInPublic true
noncomputable section

namespace CompactAlbert

open UnitaryErrorBases.ComplexQuartet UnitaryErrorBases.ThreeCycleFourier

/-- The fixed complex scalar/i plane in the native quaternion-pair model. -/
def complexOctonion (z : ℂ) : Glennie.Octonion :=
  (⟨z.re, z.im, 0, 0⟩, 0)

/-- The fixed-scale vv*/3 field expansion for v=(1,u,w). For arbitrary u,w
this is not normalized by the ray's squared norm. -/
def nativeOuterProductThird (u w : Glennie.Octonion) : Glennie.Albert :=
  ⟨1 / 3, Glennie.octNormSq u / 3, Glennie.octNormSq w / 3,
    (1 / 3 : ℝ) • Glennie.octConj u,
    (1 / 3 : ℝ) • Glennie.octConj w,
    (1 / 3 : ℝ) • Glennie.octMul u (Glennie.octConj w)⟩

/-- The original coordinate anchor, defined directly in native fields. -/
def literalNativeCoordinatePoint (t : Fin 3) : Glennie.Albert :=
  ⟨if t = 0 then 1 else 0, if t = 1 then 1 else 0,
    if t = 2 then 1 else 0, 0, 0, 0⟩

/-- Raw type zero at the original independent exponent labels a,b. -/
def literalNativeRawComplexPoint (a b : PhaseIndex) : Glennie.Albert :=
  nativeOuterProductThird (complexOctonion (character a)) (complexOctonion (character b))

/-- Original frame 1+s, outcome t, through raw(0,t,s-t). -/
def literalNativePhasePoint (s t : PhaseIndex) : Glennie.Albert :=
  literalNativeRawComplexPoint t (s - t)

/-- The integer raw-type-zero index in the original thirty-nine-point order. -/
def literalNativeRawComplexIndex (a b : PhaseIndex) : ℕ := 3 + 3 * a.val + b.val

private theorem matrix_index_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  exact (by decide : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2) i

private theorem complexOctonion_conj (z : ℂ) :
    Glennie.octConj (complexOctonion z) = complexOctonion (star z) := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [complexOctonion, Glennie.octConj]

private theorem complexOctonion_mul (z w : ℂ) :
    Glennie.octMul (complexOctonion z) (complexOctonion w) = complexOctonion (z * w) := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [complexOctonion, Glennie.octMul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im] <;> ring1

private theorem complexOctonion_norm (z : ℂ) :
    Glennie.octNormSq (complexOctonion z) = Complex.normSq z := by
  simp [complexOctonion, Glennie.octNormSq, Quaternion.normSq_def',
    Complex.normSq_apply, pow_two]

private theorem complexOctonion_scalar (z : ℂ) :
    (octonionToTitsRow (complexOctonion z)).1 = z := by
  apply Complex.ext <;> rfl

private theorem complexOctonion_row (z : ℂ) :
    (octonionToTitsRow (complexOctonion z)).2 = 0 := by
  funext column
  rcases matrix_index_cases column with rfl | rfl | rfl <;>
    apply Complex.ext <;> simp [complexOctonion, octonionToTitsRow]

private theorem complex_norm_cast (z : ℂ) :
    (Complex.normSq z : ℂ) = z * star z := by
  simpa only [starRingEnd_apply, mul_comm] using
    (Complex.normSq_eq_conj_mul_self (z := z))

/-- A binary complex calculation: no unit-norm premise or phase arithmetic
is needed to compare the native field expansion to its literal outer product. -/
private theorem nativeOuterProductThird_complex_pair (u w : ℂ) :
    nativeTitsMatrixPair (nativeOuterProductThird (complexOctonion u) (complexOctonion w)) =
      ((1 / 3 : ℂ) • Matrix.vecMulVec ![1, u, w] (star ![1, u, w]), 0) := by
  apply Prod.ext
  · apply Matrix.ext
    intro row column
    change (hermitianMatrix (toTitsCoordinates
        (nativeOuterProductThird (complexOctonion u) (complexOctonion w)))) row column =
      (((1 / 3 : ℂ) • Matrix.vecMulVec ![1, u, w] (star ![1, u, w])) :
        TitsComplexMatrix) row column
    rw [Matrix.smul_apply, Matrix.vecMulVec_apply]
    simp only [Pi.star_apply, smul_eq_mul]
    rcases matrix_index_cases row with rfl | rfl | rfl <;>
      rcases matrix_index_cases column with rfl | rfl | rfl <;>
      simp [hermitianMatrix, toTitsCoordinates, nativeOuterProductThird,
        complexOctonion_conj, complexOctonion_mul, complexOctonion_norm,
        Glennie.octConj_smul, titsScalar_smul, complexOctonion_scalar,
        Complex.ofReal_div, Complex.real_smul, complex_norm_cast,
        starRingEnd_apply, -Complex.star_def, smul_eq_mul] <;> ring1
  · apply Matrix.ext
    intro row column
    change ((toTitsCoordinates
      (nativeOuterProductThird (complexOctonion u) (complexOctonion w))).2.2 :
        TitsComplexMatrix) row column = 0
    rcases matrix_index_cases row with rfl | rfl | rfl <;>
      rcases matrix_index_cases column with rfl | rfl | rfl <;>
      simp [toTitsCoordinates, nativeOuterProductThird, complexOctonion_conj,
        complexOctonion_mul, Glennie.octConj_smul, titsRow_smul, complexOctonion_row]

private theorem literalNativeCoordinatePoint_pair (t : Fin 3) :
    nativeTitsMatrixPair (literalNativeCoordinatePoint t) = (coordinateProjector t, 0) := by
  apply Prod.ext
  · apply Matrix.ext
    intro row column
    change (hermitianMatrix (toTitsCoordinates (literalNativeCoordinatePoint t))) row column =
      coordinateProjector t row column
    rcases matrix_index_cases t with rfl | rfl | rfl <;>
      rcases matrix_index_cases row with rfl | rfl | rfl <;>
      rcases matrix_index_cases column with rfl | rfl | rfl <;>
      simp [literalNativeCoordinatePoint, toTitsCoordinates, hermitianMatrix,
        coordinateProjector, Matrix.diagonal_apply, octonionToTitsRow, Glennie.octConj] <;>
        apply Complex.ext <;> rfl
  · apply Matrix.ext
    intro row column
    change ((toTitsCoordinates (literalNativeCoordinatePoint t)).2.2 :
      TitsComplexMatrix) row column = 0
    rcases matrix_index_cases row with rfl | rfl | rfl <;>
      rcases matrix_index_cases column with rfl | rfl | rfl <;>
      simp [literalNativeCoordinatePoint, toTitsCoordinates, octonionToTitsRow,
        Glennie.octConj] <;> apply Complex.ext <;> rfl

/-- The original native coordinate anchors agree with the included matrices. -/
theorem literalNativeCoordinatePoint_eq_included (t : Fin 3) :
    literalNativeCoordinatePoint t = includedCoordinatePoint t := by
  apply nativeTitsMatrixPair_injective
  rw [literalNativeCoordinatePoint_pair]
  exact (includeHermitianMatrix_pair
    ⟨coordinateProjector t, coordinateProjector_isHermitian t⟩).symm

/-- The original raw(t,s-t) native anchors agree with the included phase matrices. -/
theorem literalNativePhasePoint_eq_included (s t : PhaseIndex) :
    literalNativePhasePoint s t = includedPhasePoint s t := by
  apply nativeTitsMatrixPair_injective
  have h := nativeOuterProductThird_complex_pair (character t) (character (s - t))
  change nativeTitsMatrixPair (literalNativePhasePoint s t) = (phaseProjector s t, 0) at h
  rw [h]
  exact (includeHermitianMatrix_pair
    ⟨phaseProjector s t, phaseProjector_isHermitian s t⟩).symm

/-- The original complex raw labels in frame/outcome order, checked separately. -/
theorem literalNative_first_twelve_raw_labels :
    [0, 1, 2,
      literalNativeRawComplexIndex 0 0, literalNativeRawComplexIndex 1 (0 - 1),
      literalNativeRawComplexIndex 2 (0 - 2),
      literalNativeRawComplexIndex 0 1, literalNativeRawComplexIndex 1 (1 - 1),
      literalNativeRawComplexIndex 2 (1 - 2),
      literalNativeRawComplexIndex 0 2, literalNativeRawComplexIndex 1 (2 - 1),
      literalNativeRawComplexIndex 2 (2 - 2)] =
      [0, 1, 2, 3, 8, 10, 4, 6, 11, 5, 7, 9] := by decide

end CompactAlbert

#check CompactAlbert.literalNativeCoordinatePoint_eq_included
#check CompactAlbert.literalNativePhasePoint_eq_included
#check CompactAlbert.literalNative_first_twelve_raw_labels
#print axioms CompactAlbert.literalNativeCoordinatePoint_eq_included
#print axioms CompactAlbert.literalNativePhasePoint_eq_included
#print axioms CompactAlbert.literalNative_first_twelve_raw_labels

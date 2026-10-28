module

public import NativePartialAction

@[expose] public section

/-!
# Two left actions on the existing native real carrier

In the checked native row convention the partial map is (a,B) ↦ (a,VB).
Its source global map is (a,B) ↦ (VaVᴴ,VB). These maps are constructed on
Glennie.Albert through the existing real coordinates. The Hermitian condition
needed by the coordinate inverse is proved directly; no new scalar structure
on a Hermitian subtype, Albert carrier or native operation is introduced.

This first endpoint proves real linearity, matrix-pair identities, fixed-unit
and inverse laws, fixation of the included complex anchors, and agreement on
the visible scalar slice. Product covariance, native pairing isometry and the
actual original point-label binding remain separate subsequent obligations.

New first-party elementary matrix/linear-algebra proofs; no upstream proof body
is copied. The imported portable NativeIncludedQuartetReadouts source already
owns the native carrier and Tits interfaces; standalone wrappers must not be
co-imported because they redeclare its extracted source. Inherited provenance
and Apache-2.0 notices remain in NativePartialAction's unchanged import closure.
Mathlib is pinned at 065356127b1dc0016f66b7283ce0ce2c4055aa55.
The native right-hidden action was inspected to check the row convention; it
is a different global automorphism, not the partial map defined here.
Thanks to the native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace CompactAlbert

/-- Left multiplication of the hidden row block in the existing coordinates. -/
def titsPartialLeft (V : TitsComplexMatrix) : TitsCoordinates →ₗ[ℝ] TitsCoordinates where
  toFun q := (q.1, q.2.1, V * q.2.2)
  map_add' q r := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · exact Matrix.mul_add _ _ _
  map_smul' t q := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · exact Matrix.mul_smul _ _ _

/-- The actual real-linear partial map, defined without a unitary premise. -/
def nativePartialLeft (V : TitsComplexMatrix) : Glennie.Albert →ₗ[ℝ] Glennie.Albert :=
  compactTitsCoordinateEquiv.symm.toLinearMap.comp
    ((titsPartialLeft V).comp compactTitsCoordinateEquiv.toLinearMap)

theorem nativePartialLeft_coordinates (V : TitsComplexMatrix) (x : Glennie.Albert) :
    toTitsCoordinates (nativePartialLeft V x) =
      ((toTitsCoordinates x).1, (toTitsCoordinates x).2.1,
        V * (toTitsCoordinates x).2.2) := by
  change compactTitsCoordinateEquiv (compactTitsCoordinateEquiv.symm _) = _
  exact compactTitsCoordinateEquiv.apply_symm_apply _

/-- The partial map's exact native pair formula. -/
theorem nativePartialLeft_pair (V : TitsComplexMatrix) (x : Glennie.Albert) :
    nativeTitsMatrixPair (nativePartialLeft V x) =
      ((nativeTitsMatrixPair x).1, V * (nativeTitsMatrixPair x).2) := by
  change toMatrixPair (toTitsCoordinates (nativePartialLeft V x)) = _
  rw [nativePartialLeft_coordinates]
  rfl

/-- Matrix conjugation preserves the actual Hermitian condition. -/
theorem leftConjugate_isHermitian (V a : TitsComplexMatrix) (ha : a.IsHermitian) :
    (V * a * V.conjTranspose).IsHermitian := by
  change a.conjTranspose = a at ha
  change (V * a * V.conjTranspose).conjTranspose = V * a * V.conjTranspose
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, ha]
  exact (Matrix.mul_assoc _ _ _).symm

/-- Lift the conjugating matrix pair through the existing Hermitian coordinate
inverse. Its visible Hermitian proof is established, not a constructor premise. -/
def nativeFullLeftValue (V : TitsComplexMatrix) (x : Glennie.Albert) : Glennie.Albert :=
  fromTitsCoordinates (fromHermitianPair
    (⟨V * (nativeTitsMatrixPair x).1 * V.conjTranspose,
      leftConjugate_isHermitian V _ (hermitianMatrix_isHermitian (toTitsCoordinates x))⟩,
      V * (nativeTitsMatrixPair x).2))

theorem nativeFullLeftValue_pair (V : TitsComplexMatrix) (x : Glennie.Albert) :
    nativeTitsMatrixPair (nativeFullLeftValue V x) =
      (V * (nativeTitsMatrixPair x).1 * V.conjTranspose,
        V * (nativeTitsMatrixPair x).2) := by
  have h : toHermitianPair (toTitsCoordinates (nativeFullLeftValue V x)) =
      (⟨V * (nativeTitsMatrixPair x).1 * V.conjTranspose,
        leftConjugate_isHermitian V _ (hermitianMatrix_isHermitian (toTitsCoordinates x))⟩,
        V * (nativeTitsMatrixPair x).2) := by
    unfold nativeFullLeftValue
    rw [toTitsCoordinates_fromTitsCoordinates, toHermitianPair_fromHermitianPair]
  apply Prod.ext
  · exact congrArg (fun p : HermitianTitsPair => p.1.val) h
  · exact congrArg (fun p : HermitianTitsPair => p.2) h

/-- The full conjugating map is linear on the existing real carrier. -/
def nativeFullLeft (V : TitsComplexMatrix) : Glennie.Albert →ₗ[ℝ] Glennie.Albert where
  toFun := nativeFullLeftValue V
  map_add' x y := by
    apply nativeTitsMatrixPair_injective
    simp only [nativeFullLeftValue_pair, map_add]
    apply Prod.ext
    · change V * ((nativeTitsMatrixPair x).1 + (nativeTitsMatrixPair y).1) *
          V.conjTranspose =
        V * (nativeTitsMatrixPair x).1 * V.conjTranspose +
          V * (nativeTitsMatrixPair y).1 * V.conjTranspose
      rw [Matrix.mul_add, Matrix.add_mul]
    · change V * ((nativeTitsMatrixPair x).2 + (nativeTitsMatrixPair y).2) =
        V * (nativeTitsMatrixPair x).2 + V * (nativeTitsMatrixPair y).2
      exact Matrix.mul_add _ _ _
  map_smul' r x := by
    apply nativeTitsMatrixPair_injective
    simp only [nativeFullLeftValue_pair, map_smul]
    apply Prod.ext
    · change V * (r • (nativeTitsMatrixPair x).1) * V.conjTranspose =
        r • (V * (nativeTitsMatrixPair x).1 * V.conjTranspose)
      rw [Matrix.mul_smul, Matrix.smul_mul]
    · change V * (r • (nativeTitsMatrixPair x).2) =
        r • (V * (nativeTitsMatrixPair x).2)
      exact Matrix.mul_smul _ _ _

/-- Both pair components of the full native real-linear map. -/
theorem nativeFullLeft_pair (V : TitsComplexMatrix) (x : Glennie.Albert) :
    nativeTitsMatrixPair (nativeFullLeft V x) =
      (V * (nativeTitsMatrixPair x).1 * V.conjTranspose,
        V * (nativeTitsMatrixPair x).2) :=
  nativeFullLeftValue_pair V x

/-- Native unit, in the same pair view used by both maps. -/
theorem nativeTitsMatrixPair_unit :
    nativeTitsMatrixPair (1 : Glennie.Albert) = ((1 : TitsComplexMatrix), 0) := by
  change toMatrixPair (compactTitsCoordinateEquiv (1 : Glennie.Albert)) = _
  rw [compactTitsCoordinateEquiv_unit]
  apply Prod.ext
  · ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [toMatrixPair, titsUnit, hermitianMatrix]
  · rfl

theorem nativePartialLeft_unit (V : TitsComplexMatrix) :
    nativePartialLeft V (1 : Glennie.Albert) = 1 := by
  apply nativeTitsMatrixPair_injective
  simp only [nativePartialLeft_pair, nativeTitsMatrixPair_unit, Matrix.mul_zero]

theorem nativeFullLeft_unit (V : TitsComplexMatrix)
    (hV : V * V.conjTranspose = (1 : TitsComplexMatrix)) :
    nativeFullLeft V (1 : Glennie.Albert) = 1 := by
  apply nativeTitsMatrixPair_injective
  simp only [nativeFullLeft_pair, nativeTitsMatrixPair_unit, Matrix.mul_zero,
    Matrix.mul_one, hV]

/-- Every included Hermitian visible matrix is fixed by the partial map. -/
theorem nativePartialLeft_include (V : TitsComplexMatrix)
    (a : {a : TitsComplexMatrix // a.IsHermitian}) :
    nativePartialLeft V (includeHermitianMatrix a) = includeHermitianMatrix a := by
  apply nativeTitsMatrixPair_injective
  simp only [nativePartialLeft_pair, includeHermitianMatrix_pair, Matrix.mul_zero]

/-- Agreement holds on the actual native visible-scalar slice. The real
canonical nonanchor slice is the specialization c=1/3. -/
theorem nativePartialLeft_eq_full_of_visible_scalar (V : TitsComplexMatrix)
    (hV : V * V.conjTranspose = (1 : TitsComplexMatrix))
    (x : Glennie.Albert) (c : ℂ)
    (hx : (nativeTitsMatrixPair x).1 = c • (1 : TitsComplexMatrix)) :
    nativePartialLeft V x = nativeFullLeft V x := by
  apply nativeTitsMatrixPair_injective
  rw [nativePartialLeft_pair, nativeFullLeft_pair]
  apply Prod.ext
  · simp only [hx, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hV]
  · rfl

theorem nativePartialLeft_one (x : Glennie.Albert) :
    nativePartialLeft (1 : TitsComplexMatrix) x = x := by
  apply nativeTitsMatrixPair_injective
  simp only [nativePartialLeft_pair, Matrix.one_mul]

theorem nativeFullLeft_one (x : Glennie.Albert) :
    nativeFullLeft (1 : TitsComplexMatrix) x = x := by
  apply nativeTitsMatrixPair_injective
  simp only [nativeFullLeft_pair, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one]

/-- First V, then W: the left parameter is WV. -/
theorem nativePartialLeft_comp (V W : TitsComplexMatrix) (x : Glennie.Albert) :
    nativePartialLeft W (nativePartialLeft V x) = nativePartialLeft (W * V) x := by
  apply nativeTitsMatrixPair_injective
  simp only [nativePartialLeft_pair, Matrix.mul_assoc]

theorem nativeFullLeft_comp (V W : TitsComplexMatrix) (x : Glennie.Albert) :
    nativeFullLeft W (nativeFullLeft V x) = nativeFullLeft (W * V) x := by
  apply nativeTitsMatrixPair_injective
  simp only [nativeFullLeft_pair, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Two-sided unitarity supplies the actual real-linear inverse. Determinant
one is needed later for Jordan covariance, not for these inverse laws. -/
def nativeFullLeftEquiv (V : TitsComplexMatrix)
    (hV : V * V.conjTranspose = (1 : TitsComplexMatrix))
    (hVleft : V.conjTranspose * V = (1 : TitsComplexMatrix)) :
    Glennie.Albert ≃ₗ[ℝ] Glennie.Albert where
  toFun := nativeFullLeft V
  invFun := nativeFullLeft V.conjTranspose
  left_inv x := by rw [nativeFullLeft_comp, hVleft, nativeFullLeft_one]
  right_inv x := by rw [nativeFullLeft_comp, hV, nativeFullLeft_one]
  map_add' := (nativeFullLeft V).map_add
  map_smul' := (nativeFullLeft V).map_smul

end CompactAlbert

module

public import NativeComplementaryConstruction
public import NativePolynomialEvaluationStaged

/-
# The actual compact Albert common-right special-unitary action

This is a minimal adaptation of the existing compact-albert-recognition
action proof, commit 40d3b344180d9ddb78aaa2876873377c1e631515:
https://github.com/macgregor-sudo/compact-albert-recognition
Glennie/Native/SectorLeftAction.lean, SHA256
3314a6376c62a7f41294dace69a9d6be6209ee3dd1d74c8fb08a56fe2c3f5c89,
leftMulEquiv/sectorLeftEquiv and its Gram, adjugate, product and trace proofs;
Glennie/Theorems/SectorTransport.lean, SHA256
62a2094972e4f574e9c7a1be0b5bad6ecb85082798f589c76e32eeadf884e4fc,
sectorAdjointAdjugate_mul and sectorAdjointAdjugate_unitary.

Changes: use the already checked Tits row B=Mᴴ=−conj Z, so the old parameter
h=Vᴴ acts by B↦BV; use the existing actual compactTitsCoordinateEquiv and
native_tits_product_pair instead of importing another native sector model.
The matrix covariance argument is retained, including singular hidden inputs.
No native carrier, product, bilinearity law or cubic identity is redefined.
The common-right SU(3) subgroup is classical; this adapter makes no novelty,
exhaustion, quotient, Lie-group or manifold claim.

The inspected upstream LICENSE is Apache-2.0, SHA256
b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1;
its complete THIRD-PARTY-NOTICES.md has SHA256
a41bd37f412cd3bf658a1cb8a8c80f109b35e6278c35df95ef919c18577afeee.
The license is retained unchanged in LICENSES/Native-Albert-Apache-2.0.txt;
the notice is retained with public scope/locator clarifications in
LICENSES/Native-Albert-THIRD-PARTY-NOTICES.md. The hashes above identify the originals. Neither
source file has a separate author/copyright notice; none is invented here.
The pinned project README and notice credit AI-generated development under
Robert MacGregor's direction and maintenance; this is project provenance,
not an invented per-file authorship claim.
No release license is assigned to new contributions by this adaptation.
Thanks to the compact-albert-recognition, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/


@[expose] public section
noncomputable section

namespace CompactAlbert

/-- Right multiplication of the actual hidden row block, linear over R. -/
def titsRightMultiply (V : TitsComplexMatrix) : TitsCoordinates →ₗ[ℝ] TitsCoordinates where
  toFun q := (q.1, q.2.1, q.2.2 * V)
  map_add' q r := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · exact Matrix.add_mul _ _ _
  map_smul' t q := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · exact Matrix.smul_mul _ _ _

/-- The existing native carrier acted on through its checked real coordinates.
No unitarity is needed to define this real-linear map. -/
def nativeRightMultiply (V : TitsComplexMatrix) : Glennie.Albert →ₗ[ℝ] Glennie.Albert :=
  compactTitsCoordinateEquiv.symm.toLinearMap.comp
    ((titsRightMultiply V).comp compactTitsCoordinateEquiv.toLinearMap)

/-- The three real diagonals and three cyclic complex scalars remain fixed. -/
theorem nativeRightMultiply_coordinates (V : TitsComplexMatrix) (x : Glennie.Albert) :
    toTitsCoordinates (nativeRightMultiply V x) =
      ((toTitsCoordinates x).1, (toTitsCoordinates x).2.1,
        (toTitsCoordinates x).2.2 * V) := by
  change compactTitsCoordinateEquiv (compactTitsCoordinateEquiv.symm _) = _
  exact compactTitsCoordinateEquiv.apply_symm_apply _

/-- Both matrix components of the actual native map, in the fixed B-row gauge. -/
theorem nativeRightMultiply_pair (V : TitsComplexMatrix) (x : Glennie.Albert) :
    nativeTitsMatrixPair (nativeRightMultiply V x) =
      ((nativeTitsMatrixPair x).1, (nativeTitsMatrixPair x).2 * V) := by
  change toMatrixPair (toTitsCoordinates (nativeRightMultiply V x)) = _
  rw [nativeRightMultiply_coordinates]
  rfl

private theorem right_gram (V : TitsComplexMatrix)
    (hV : V * V.conjTranspose = (1 : TitsComplexMatrix)) (B D : TitsComplexMatrix) :
    (B * V) * (D * V).conjTranspose = B * D.conjTranspose := by
  calc
    _ = (B * V) * (V.conjTranspose * D.conjTranspose) := by
      rw [Matrix.conjTranspose_mul]
    _ = B * ((V * V.conjTranspose) * D.conjTranspose) := by
      simp only [Matrix.mul_assoc]
    _ = B * D.conjTranspose := by rw [hV, Matrix.one_mul]

private theorem right_adjoint_adjugate (V : TitsComplexMatrix)
    (hV : V * V.conjTranspose = (1 : TitsComplexMatrix)) (hd : V.det = 1)
    (B : TitsComplexMatrix) :
    (B * V).adjugate.conjTranspose = B.adjugate.conjTranspose * V := by
  have hsharp := (adjugate_conjTranspose_eq_iff_det_eq_one V hV).mpr hd
  simp only [Matrix.adjugate_mul_distrib, Matrix.conjTranspose_mul, hsharp]

private theorem right_polar_adjugate (V : TitsComplexMatrix)
    (hV : V * V.conjTranspose = (1 : TitsComplexMatrix)) (hd : V.det = 1)
    (B D : TitsComplexMatrix) :
    ((B * V + D * V).adjugate.conjTranspose - (B * V).adjugate.conjTranspose -
      (D * V).adjugate.conjTranspose) =
      ((B + D).adjugate.conjTranspose - B.adjugate.conjTranspose -
        D.adjugate.conjTranspose) * V := by
  rw [← Matrix.add_mul]
  simp only [right_adjoint_adjugate V hV hd, Matrix.sub_mul]

private theorem productComplex_right (V : TitsComplexMatrix)
    (hV : V * V.conjTranspose = (1 : TitsComplexMatrix)) (a B c D : TitsComplexMatrix) :
    compactSecondTitsProductComplex a (B * V) c (D * V) =
      compactSecondTitsProductComplex a B c D := by
  simp only [compactSecondTitsProductComplex, right_gram V hV]

private theorem productHidden_right (V : TitsComplexMatrix)
    (hV : V * V.conjTranspose = (1 : TitsComplexMatrix)) (hd : V.det = 1)
    (a B c D : TitsComplexMatrix) :
    compactSecondTitsProductHidden a (B * V) c (D * V) =
      compactSecondTitsProductHidden a B c D * V := by
  simp only [compactSecondTitsProductHidden, right_polar_adjugate V hV hd,
    Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc]

/-- Actual native product preservation for determinant-one unitaries.
The hidden arguments and their sum may be singular. -/
theorem nativeRightMultiply_jordan (V : TitsComplexMatrix)
    (hV : V * V.conjTranspose = (1 : TitsComplexMatrix)) (hd : V.det = 1)
    (x y : Glennie.Albert) :
    nativeRightMultiply V (Glennie.jordan x y) =
      Glennie.jordan (nativeRightMultiply V x) (nativeRightMultiply V y) := by
  apply nativeTitsMatrixPair_injective
  have hp (u v : Glennie.Albert) :
      nativeTitsMatrixPair (Glennie.jordan u v) =
        compactSecondTitsProduct (nativeTitsMatrixPair u) (nativeTitsMatrixPair v) :=
    native_tits_product_pair u v
  simp only [nativeRightMultiply_pair, hp]
  apply Prod.ext
  · exact (productComplex_right V hV _ _ _ _).symm
  · exact (productHidden_right V hV hd _ _ _ _).symm

/-- The actual unnormalized native trace is fixed, without a unitary premise. -/
theorem nativeRightMultiply_trace (V : TitsComplexMatrix) (x : Glennie.Albert) :
    Glennie.trace (nativeRightMultiply V x) = Glennie.trace x := by
  rw [← compactTitsCoordinateEquiv_trace (nativeRightMultiply V x),
    ← compactTitsCoordinateEquiv_trace x]
  change titsTrace (toTitsCoordinates (nativeRightMultiply V x)) = _
  rw [nativeRightMultiply_coordinates]
  rfl

/-- The actual native unit has zero hidden block and is fixed. -/
theorem nativeRightMultiply_unit (V : TitsComplexMatrix) :
    nativeRightMultiply V (1 : Glennie.Albert) = 1 := by
  apply compactTitsCoordinateEquiv.injective
  change toTitsCoordinates (nativeRightMultiply V 1) = _
  rw [nativeRightMultiply_coordinates]
  change ((compactTitsCoordinateEquiv (1 : Glennie.Albert)).1,
    (compactTitsCoordinateEquiv (1 : Glennie.Albert)).2.1,
    (compactTitsCoordinateEquiv (1 : Glennie.Albert)).2.2 * V) =
      compactTitsCoordinateEquiv (1 : Glennie.Albert)
  rw [compactTitsCoordinateEquiv_unit]
  simp only [titsUnit, Matrix.zero_mul]

/-- Every included complex Hermitian matrix is fixed pointwise. -/
theorem nativeRightMultiply_includeHermitianMatrix (V : TitsComplexMatrix)
    (a : {a : TitsComplexMatrix // a.IsHermitian}) :
    nativeRightMultiply V (includeHermitianMatrix a) = includeHermitianMatrix a := by
  apply nativeTitsMatrixPair_injective
  rw [nativeRightMultiply_pair, includeHermitianMatrix_pair]
  simp only [Matrix.zero_mul]

/-- The actual complementary-point constructor transforms by U↦UV.
This coordinate identity needs no unitarity condition on U or V. -/
theorem nativeRightMultiply_complementaryPoint (U V : TitsComplexMatrix) :
    nativeRightMultiply V (nativeComplementaryPoint U) = nativeComplementaryPoint (U * V) := by
  apply nativeTitsMatrixPair_injective
  rw [nativeRightMultiply_pair, nativeComplementaryPoint_pair, nativeComplementaryPoint_pair]
  simp only [Matrix.smul_mul]

/-- Right multiplication is unital as an operator on the actual native space. -/
theorem nativeRightMultiply_one (x : Glennie.Albert) :
    nativeRightMultiply (1 : TitsComplexMatrix) x = x := by
  apply nativeTitsMatrixPair_injective
  simp only [nativeRightMultiply_pair, Matrix.mul_one]

/-- First acting by V and then by W acts by VW. Equivalently,
operator composition R_V∘R_W is R_(WV), not R_(VW). -/
theorem nativeRightMultiply_comp (V W : TitsComplexMatrix) (x : Glennie.Albert) :
    nativeRightMultiply W (nativeRightMultiply V x) = nativeRightMultiply (V * W) x := by
  apply nativeTitsMatrixPair_injective
  simp only [nativeRightMultiply_pair, Matrix.mul_assoc]

private theorem specialUnitary_left_inverse (V : TitsComplexMatrix)
    (hV : V * V.conjTranspose = (1 : TitsComplexMatrix)) (hd : V.det = 1) :
    V.conjTranspose * V = (1 : TitsComplexMatrix) := by
  have hsharp := (adjugate_conjTranspose_eq_iff_det_eq_one V hV).mpr hd
  have hadj : V.adjugate = V.conjTranspose := by
    have h := congrArg (fun M : TitsComplexMatrix => M.conjTranspose) hsharp
    simpa only [Matrix.conjTranspose_conjTranspose] using h
  calc
    _ = V.adjugate * V := by rw [hadj]
    _ = 1 := by rw [Matrix.adjugate_mul, hd, one_smul]

/-- The actual real-linear equivalence for the common-right SU(3) action.
Product, trace and unit preservation are proved above, not constructor assumptions. -/
def nativeRightSU3Equiv (V : TitsComplexMatrix)
    (hV : V * V.conjTranspose = (1 : TitsComplexMatrix)) (hd : V.det = 1) :
    Glennie.Albert ≃ₗ[ℝ] Glennie.Albert where
  toFun := nativeRightMultiply V
  invFun := nativeRightMultiply V.conjTranspose
  left_inv x := by rw [nativeRightMultiply_comp, hV, nativeRightMultiply_one]
  right_inv x := by
    rw [nativeRightMultiply_comp, specialUnitary_left_inverse V hV hd,
      nativeRightMultiply_one]
  map_add' := (nativeRightMultiply V).map_add
  map_smul' := (nativeRightMultiply V).map_smul

/-- Equality of these actual native operators recovers the SU(3) parameter;
there is no pointwise central quotient. -/
theorem nativeRightMultiply_faithful (V W : TitsComplexMatrix)
    (h : nativeRightMultiply V = nativeRightMultiply W) : V = W := by
  have hp := congrArg (fun f : Glennie.Albert →ₗ[ℝ] Glennie.Albert =>
    f (nativeComplementaryPoint (1 : TitsComplexMatrix))) h
  rw [nativeRightMultiply_complementaryPoint, nativeRightMultiply_complementaryPoint,
    Matrix.one_mul, Matrix.one_mul] at hp
  have hb := congrArg (fun x : Glennie.Albert =>
    (3 : ℂ) • (toTitsCoordinates x).2.2) hp
  simpa only [nativeComplementaryPoint_scaled_hidden] using hb

end CompactAlbert

/- Co-import consumer for the actual native right action and polynomial branch. -/


#check @CompactAlbert.nativeRightMultiply
#check @CompactAlbert.nativeRightMultiply_coordinates
#check @CompactAlbert.nativeRightMultiply_pair
#check @CompactAlbert.nativeRightMultiply_jordan
#check @CompactAlbert.nativeRightMultiply_trace
#check @CompactAlbert.nativeRightMultiply_unit
#check @CompactAlbert.nativeRightMultiply_includeHermitianMatrix
#check @CompactAlbert.nativeRightMultiply_complementaryPoint
#check @CompactAlbert.nativeRightMultiply_one
#check @CompactAlbert.nativeRightMultiply_comp
#check @CompactAlbert.nativeRightSU3Equiv
#check @CompactAlbert.nativeRightMultiply_faithful

#print axioms CompactAlbert.nativeRightMultiply
#print axioms CompactAlbert.nativeRightMultiply_coordinates
#print axioms CompactAlbert.nativeRightMultiply_pair
#print axioms CompactAlbert.nativeRightMultiply_jordan
#print axioms CompactAlbert.nativeRightMultiply_trace
#print axioms CompactAlbert.nativeRightMultiply_unit
#print axioms CompactAlbert.nativeRightMultiply_includeHermitianMatrix
#print axioms CompactAlbert.nativeRightMultiply_complementaryPoint
#print axioms CompactAlbert.nativeRightMultiply_one
#print axioms CompactAlbert.nativeRightMultiply_comp
#print axioms CompactAlbert.nativeRightSU3Equiv
#print axioms CompactAlbert.nativeRightMultiply_faithful

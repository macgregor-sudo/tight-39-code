module

public import DirKTransfer
public import BookNativeNormalKernelBridge
public import BookNativeAxisBridge
public import A5Main

@[expose] public section

/-! The fixed native Book family operators: `K^re_b = Ψ_s⁻¹ ∘ hid(rootRealGenerator) ∘ Ψ_s` and the
imaginary companion, `s = b / 6`. Their 27×27 coordinate matrices are the real and imaginary parts of the
Lean Q12 sheet operator `q12Op b`, hence (DirKCheck) of the JSON matrices. Phase independent. First-party. -/

set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.HTPhaseComplete
open Option2.NativeStress.BookHT Option2.NativeStress.BookHT.TangentCoordinates
open CKM.NativeFirstOrder CKM.NativeFourFamily NativePolynomial CompactAlbert
open scoped Matrix

/-- Native hidden conjugation `(a, B) ↦ (0, X B - B X)`, typed on Tits matrices. -/
def hidConjT (X : TitsComplexMatrix) (a : Glennie.Albert) : Glennie.Albert :=
  Elim.mkPoint 0 Matrix.isHermitian_zero
    (X * (nativeTitsMatrixPair a).2 - (nativeTitsMatrixPair a).2 * X)

theorem hidConjT_eq (X : TitsComplexMatrix) (a : Glennie.Albert) :
    hidConjT X a = nativeHiddenConjugation X a := rfl

theorem hidConjT_pair (X : TitsComplexMatrix) (a : Glennie.Albert) :
    nativeTitsMatrixPair (hidConjT X a) =
      (0, X * (nativeTitsMatrixPair a).2 - (nativeTitsMatrixPair a).2 * X) :=
  Elim.mkPoint_pair _ _ _

/-- The same map, real-linear. -/
def hidConjL (X : TitsComplexMatrix) : Glennie.Albert →ₗ[ℝ] Glennie.Albert where
  toFun := hidConjT X
  map_add' a b := by
    apply nativeTitsMatrixPair_injective
    rw [map_add, hidConjT_pair, hidConjT_pair, hidConjT_pair, map_add]
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.snd_add, Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' r a := by
    apply nativeTitsMatrixPair_injective
    rw [map_smul, hidConjT_pair, hidConjT_pair, map_smul]
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.smul_snd, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

@[simp] theorem hidConjL_apply (X : TitsComplexMatrix) (a : Glennie.Albert) :
    hidConjL X a = hidConjT X a := rfl

/-- The fixed native operator of sheet `s` and hidden generator `X`. -/
def kOp (s : Fin 4) (X : TitsComplexMatrix) : Glennie.Albert →ₗ[ℝ] Glennie.Albert :=
  anchorΨinv s ∘ₗ hidConjL X ∘ₗ anchorΨ s

def rootOf (b : Fin 24) : Fin 3 × Fin 3 := rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩

def kRe (b : Fin 24) : Glennie.Albert →ₗ[ℝ] Glennie.Albert :=
  kOp (d6Sheet b) (rootRealGenerator (rootOf b).1 (rootOf b).2)

def kIm (b : Fin 24) : Glennie.Albert →ₗ[ℝ] Glennie.Albert :=
  kOp (d6Sheet b) (rootImagGenerator (rootOf b).1 (rootOf b).2)

theorem q12SheetInverse_complex_real (s : Fin 4) (x : Fin 27 → Q12) (r : Fin 27 → ℝ)
    (hx : ∀ k, Q12.toComplex (x k) = (r k : ℂ)) (k : Fin 27) :
    Q12.toComplex (q12SheetInverse s x k) =
      (upperCoordinates (anchorΨ s (fromUpperCoordinates r)) k : ℂ) := by
  fin_cases s <;>
    simp [q12SheetInverse, anchorΨ, transportTinv, upper_signedTransport, TitsS.sgnPerm, hx]

theorem single_complex (c k : Fin 27) :
    Q12.toComplex ((Pi.single c (1 : Q12) : Fin 27 → Q12) k) =
      (((Pi.single c (1 : ℝ) : Fin 27 → ℝ) k : ℝ) : ℂ) := by
  by_cases h : k = c
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem kRe_basis (b : Fin 24) (c k : Fin 27) :
    upperCoordinates (kRe b (fromUpperCoordinates (Pi.single c 1))) k =
      (Q12.toComplex (q12Op b (Pi.single c 1) k)).re := by
  unfold q12Op
  rw [q12SheetTransport_re_native]
  have hin := q12SheetInverse_complex_real (d6Sheet b) (Pi.single c 1) (Pi.single c 1)
    (single_complex c) 
  have he : (fun j => (Q12.toComplex (q12RootCoordinates (rootOf b).1 (rootOf b).2
      (q12SheetInverse (d6Sheet b) (Pi.single c 1)) j)).re) =
      upperCoordinates (nativeHiddenConjugation (rootRealGenerator (rootOf b).1 (rootOf b).2)
        (anchorΨ (d6Sheet b) (fromUpperCoordinates (Pi.single c 1)))) := by
    funext j
    exact q12RootCoordinates_re_native _ _ _ _ hin j
  change upperCoordinates (anchorΨinv (d6Sheet b) (hidConjT _
    (anchorΨ (d6Sheet b) (fromUpperCoordinates (Pi.single c 1))))) k = _
  rw [hidConjT_eq, rootOf] at *
  rw [he, fromUpperCoordinates_upperCoordinates]

theorem kIm_basis (b : Fin 24) (c k : Fin 27) :
    upperCoordinates (kIm b (fromUpperCoordinates (Pi.single c 1))) k =
      (Q12.toComplex (q12Op b (Pi.single c 1) k)).im := by
  unfold q12Op
  rw [q12SheetTransport_im_native]
  have hin := q12SheetInverse_complex_real (d6Sheet b) (Pi.single c 1) (Pi.single c 1)
    (single_complex c)
  have he : (fun j => (Q12.toComplex (q12RootCoordinates (rootOf b).1 (rootOf b).2
      (q12SheetInverse (d6Sheet b) (Pi.single c 1)) j)).im) =
      upperCoordinates (nativeHiddenConjugation (rootImagGenerator (rootOf b).1 (rootOf b).2)
        (anchorΨ (d6Sheet b) (fromUpperCoordinates (Pi.single c 1)))) := by
    funext j
    exact q12RootCoordinates_im_native _ _ _ _ hin j
  change upperCoordinates (anchorΨinv (d6Sheet b) (hidConjT _
    (anchorΨ (d6Sheet b) (fromUpperCoordinates (Pi.single c 1))))) k = _
  rw [hidConjT_eq, rootOf] at *
  rw [he, fromUpperCoordinates_upperCoordinates]

/-- Coordinates of a real-linear Albert map are a matrix product with its basis images. -/
theorem coords_of_linear (F : Glennie.Albert →ₗ[ℝ] Glennie.Albert) (v : Glennie.Albert) (k : Fin 27) :
    upperCoordinates (F v) k =
      ∑ c, upperCoordinates (F (fromUpperCoordinates (Pi.single c 1))) k * upperCoordinates v c := by
  let M : (Fin 27 → ℝ) →ₗ[ℝ] (Fin 27 → ℝ) :=
    upperCoordinateEquiv.toLinearMap ∘ₗ F ∘ₗ upperCoordinateEquiv.symm.toLinearMap
  have hM (w : Fin 27 → ℝ) : M w = upperCoordinates (F (fromUpperCoordinates w)) := rfl
  have hsum : upperCoordinates v = ∑ c, upperCoordinates v c • (Pi.single c (1 : ℝ) : Fin 27 → ℝ) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hv : upperCoordinates (F v) =
      ∑ c, upperCoordinates v c • upperCoordinates (F (fromUpperCoordinates (Pi.single c 1))) := by
    calc upperCoordinates (F v) = M (upperCoordinates v) := by
          rw [hM, fromUpperCoordinates_upperCoordinates]
      _ = M (∑ c, upperCoordinates v c • (Pi.single c (1 : ℝ) : Fin 27 → ℝ)) := by rw [← hsum]
      _ = _ := by
          rw [map_sum]; exact Finset.sum_congr rfl fun c _ => by rw [map_smul, hM]
  rw [hv, Finset.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm]

theorem kRe_coords (b : Fin 24) (v : Glennie.Albert) (k : Fin 27) :
    upperCoordinates (kRe b v) k =
      ∑ c, (Q12.toComplex (q12Op b (Pi.single c 1) k)).re * upperCoordinates v c := by
  rw [coords_of_linear]
  simp only [kRe_basis]

theorem kIm_coords (b : Fin 24) (v : Glennie.Albert) (k : Fin 27) :
    upperCoordinates (kIm b v) k =
      ∑ c, (Q12.toComplex (q12Op b (Pi.single c 1) k)).im * upperCoordinates v c := by
  rw [coords_of_linear]
  simp only [kIm_basis]

/-- Anchor states have zero hidden part in their own anchored frame, at every unit phase. -/
theorem hidConj_anchor_zero {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (s : Fin 4) (X : TitsComplexMatrix)
    (p : Fin 39) (hp : ((anchorRelabel s).symm p).val < 12) :
    hidConjT X (anchorΨ s (literalPoint ξ p)) = 0 := by
  have h := anchor_form hξ s ((anchorRelabel s).symm p)
  rw [Equiv.apply_symm_apply] at h
  have hB : (nativeTitsMatrixPair (anchorΨ s (literalPoint ξ p))).2 = 0 := by
    rw [h]
    simp only [stdAnchored, hp, dite_true, includeHermitianMatrix_pair]
  apply nativeTitsMatrixPair_injective
  rw [hidConjT_pair, map_zero, hB, Matrix.mul_zero, Matrix.zero_mul, sub_self]
  rfl

/-- The fixed operators ARE the actual A5 pre-family derivatives at every unit phase. -/
theorem kRe_preVar {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (b : Fin 24) (p : Fin 39) :
    upperCoordinates (kRe b (literalPoint ξ p)) =
      preVar ξ hξ (d6Sheet b) (rootRealParam ⟨b.val % 6, by omega⟩,
        rootRealParam ⟨b.val % 6, by omega⟩, 0) p := by
  rw [preVar_same_conjugation, suMat_rootRealParam]
  change upperCoordinates (anchorΨinv (d6Sheet b) (hidConjT _
    (anchorΨ (d6Sheet b) (literalPoint ξ p)))) = _
  split_ifs with hp
  · rw [hidConj_anchor_zero hξ _ _ p hp]
  · rfl

theorem kIm_preVar {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (b : Fin 24) (p : Fin 39) :
    upperCoordinates (kIm b (literalPoint ξ p)) =
      preVar ξ hξ (d6Sheet b) (rootImagParam ⟨b.val % 6, by omega⟩,
        rootImagParam ⟨b.val % 6, by omega⟩, 0) p := by
  rw [preVar_same_conjugation, suMat_rootImagParam]
  change upperCoordinates (anchorΨinv (d6Sheet b) (hidConjT _
    (anchorΨ (d6Sheet b) (literalPoint ξ p)))) = _
  split_ifs with hp
  · rw [hidConj_anchor_zero hξ _ _ p hp]
  · rfl

end Option2.NativeStress.HTPhaseComplete
open Option2.NativeStress.HTPhaseComplete
#print axioms kRe_coords
#print axioms kIm_coords
#print axioms kRe_preVar
#print axioms kIm_preVar

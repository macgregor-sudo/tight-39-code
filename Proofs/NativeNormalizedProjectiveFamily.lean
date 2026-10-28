module

public import ThreeCycleNormalizedProjectiveUnitary
public import NativeThreeCycleCompletion
public import NativeCentralArrayTopology

@[expose] public section

/-!
The actual labelled normalized construction in canonical native upper coordinates.
This composes the proved standard special-unitary center quotient times two
circles with the accepted clock-first matrix reindexing and the independently
owned native central-array coordinate embedding. 

All frames use the fixed forward native central order. No new Albert topology,
orientation quotient, matrix formula, validity hypothesis or gauge relation is
introduced. This is a topological closed embedding and actual frame validity;
Analytic immersion is a separate conclusion.
First-party composition only; imported native and mathlib notices are retained.
Thanks to the contributors. “If I have seen further it is by standing on the
sholders of Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
namespace CompactAlbert

open UnitaryErrorBases UnitaryErrorBases.ThreeCycleNormalized
open QuadraticCertificate.ExactCKMConfiguration
open NativeCentralArrayTopology

/-- The accepted inverse label/matrix maps, now with their existing product topologies. -/
def challengeFamilyNativeArrayHomeomorph : Family ≃ₜ (Fin 9 → TitsComplexMatrix) where
  toFun := nativeArrayOfChallengeFamily
  invFun := challengeFamilyOfNativeArray
  left_inv := challengeFamilyOfNativeArray_nativeArrayOfChallengeFamily
  right_inv := nativeArrayOfChallengeFamily_challengeFamilyOfNativeArray
  continuous_toFun := by
    apply continuous_pi
    intro r
    apply continuous_matrix
    intro i j
    change Continuous (fun U : Family => U (challengeLabelEquiv.symm r)
      (challengeMatrixIndexEquiv i) (challengeMatrixIndexEquiv j))
    exact (continuous_apply _).comp ((continuous_apply _).comp (continuous_apply _))
  continuous_invFun := by
    apply continuous_pi
    intro p
    apply continuous_matrix
    intro i j
    change Continuous (fun U : Fin 9 → TitsComplexMatrix => U (challengeLabelEquiv p)
      (challengeMatrixIndexEquiv.symm i) (challengeMatrixIndexEquiv.symm j))
    exact (continuous_apply _).comp ((continuous_apply _).comp (continuous_apply _))

/-- The actual normalized native matrix array in the standard projective parameters. -/
def nativeNormalizedProjectiveArray
    (x : SpecialUnitaryCenterQuotient × (Circle × Circle)) : Fin 9 → TitsComplexMatrix :=
  nativeArrayOfChallengeFamily (projectiveNormalizedFamily x)

/-- The fixed-forward native central construction in all canonical upper coordinates. -/
def nativeNormalizedProjectiveFamily
    (x : SpecialUnitaryCenterQuotient × (Circle × Circle)) : Fin 9 → Fin 3 → Fin 27 → ℝ :=
  centralArrayCoordinates (fun _ => false) (nativeNormalizedProjectiveArray x)

theorem nativeNormalizedProjectiveArray_mk (Q : StandardSpecialUnitary) (z : Circle × Circle) :
    nativeNormalizedProjectiveArray (QuotientGroup.mk Q, z) =
      nativeThreeCycleArray Q.val (phaseOfCircles z) := rfl

/-- Exact binding to the original constructed array, native constructor and coordinates. -/
theorem nativeNormalizedProjectiveFamily_mk (Q : StandardSpecialUnitary)
    (z : Circle × Circle) (r : Fin 9) (k : Fin 3) :
    nativeNormalizedProjectiveFamily (QuotientGroup.mk Q, z) r k =
      NativePolynomial.upperCoordinates
        (nativeCentralTriple (nativeThreeCycleArray Q.val (phaseOfCircles z) r) k) := rfl

/-- The canonical decoder recovers the actual native points for every quotient parameter. -/
theorem nativeNormalizedProjectiveFamily_decode
    (x : SpecialUnitaryCenterQuotient × (Circle × Circle)) (r : Fin 9) (k : Fin 3) :
    NativePolynomial.fromUpperCoordinates (nativeNormalizedProjectiveFamily x r k) =
      nativeCentralTriple (nativeNormalizedProjectiveArray x r) k :=
  NativePolynomial.fromUpperCoordinates_upperCoordinates _

/-- The accepted clock-first label and same-direction matrix index maps are retained. -/
theorem nativeNormalizedProjectiveArray_entries (Q : StandardSpecialUnitary)
    (z : Circle × Circle) (p : Label) (i j : Fin 3) :
    nativeNormalizedProjectiveArray (QuotientGroup.mk Q, z) (challengeLabelEquiv p) i j =
      normalizedFamily Q.val (phaseOfCircles z) p
        (challengeMatrixIndexEquiv i) (challengeMatrixIndexEquiv j) := by
  rw [nativeNormalizedProjectiveArray_mk, nativeThreeCycleArray_apply, Equiv.symm_apply_apply]

/-- Actual common-right normalization: every parameter has zeroth matrix I. -/
theorem nativeNormalizedProjectiveArray_zero
    (x : SpecialUnitaryCenterQuotient × (Circle × Circle)) :
    nativeNormalizedProjectiveArray x 0 = (1 : TitsComplexMatrix) := by
  rcases x with ⟨q, z⟩
  induction q using Quotient.inductionOn with | h Q =>
    exact nativeThreeCycleArray_zero Q.val (phaseOfCircles z)
      ((isSpecialUnitary_iff_mem_standard Q.val).mpr Q.property)

/-- Closed embedding of the actual labelled native construction in its canonical
upper-coordinate ambient. No global topology on Glennie.Albert is postulated. -/
theorem isClosedEmbedding_nativeNormalizedProjectiveFamily :
    Topology.IsClosedEmbedding nativeNormalizedProjectiveFamily :=
  (isClosedEmbedding_centralArrayCoordinates (fun _ => false)).comp
    (challengeFamilyNativeArrayHomeomorph.isClosedEmbedding.comp
      isClosedEmbedding_projectiveNormalizedFamily)

/-- Every parameter gives actual native frames with all original first-twelve
anchor readouts and all labelled cross-frame readouts, without a validity premise. -/
theorem nativeNormalizedProjectiveFamily_actual_nine_frames
    (x : SpecialUnitaryCenterQuotient × (Circle × Circle)) :
    ((∀ r : Fin 9, Glennie.Frame (nativeCentralTriple (nativeNormalizedProjectiveArray x r)) ∧
      ∀ k : Fin 3, ∀ i : Fin 39, i.val < 12 →
        Glennie.trace (Glennie.jordan
          (nativeCentralTriple (nativeNormalizedProjectiveArray x r) k) (nativePoint i)) =
            (1 / 3 : ℝ)) ∧
    (∀ r s : Fin 9, r ≠ s → ∀ k l : Fin 3,
      Glennie.trace (Glennie.jordan
        (nativeCentralTriple (nativeNormalizedProjectiveArray x r) k)
        (nativeCentralTriple (nativeNormalizedProjectiveArray x s) l)) = (1 / 3 : ℝ))) := by
  rcases x with ⟨q, z⟩
  induction q using Quotient.inductionOn with | h Q =>
    exact nativeThreeCycleArray_actual_nine_frames Q.val (phaseOfCircles z)
      ((isSpecialUnitary_iff_mem_standard Q.val).mpr Q.property)

end CompactAlbert

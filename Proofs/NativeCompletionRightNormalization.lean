module

public import NativeIncludedQuartetReadouts

@[expose] public section

/-!
Exact common-right normalization on the actual Fin9 TitsComplexMatrix arrays.
Every SU3 array has zeroth value I after U_i↦U_i U_0†; the algebraic fibres
are precisely common-right SU3 orbits, with unique explicit parameter U_0† V_0.
No quotient framework, topology, embedding, reindexing or full A2 is asserted.
First-party composition of the accepted actual matrix carrier and pinned
Mathlib matrix/unitary/adjoint APIs (065356127b1dc0016f66b7283ce0ce2c4055aa55).
Thanks to their contributors. “If I have seen further it is by standing on the
sholders of Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
namespace CompactAlbert

/-- The original nine labels are unchanged; zero is the actual first label. -/
def completionRightNormalization (U : Fin 9 → TitsComplexMatrix) :
    Fin 9 → TitsComplexMatrix := fun i => U i * (U 0).conjTranspose

private theorem left_gram (A : TitsComplexMatrix) (hA : A * A.conjTranspose = 1) :
    A.conjTranspose * A = 1 := mul_eq_one_comm.mp hA

private theorem specialUnitary_adjoint (A : TitsComplexMatrix)
    (hA : A * A.conjTranspose = 1 ∧ A.det = 1) :
    A.conjTranspose * A.conjTranspose.conjTranspose = 1 ∧ A.conjTranspose.det = 1 := by
  constructor
  · rw [Matrix.conjTranspose_conjTranspose]
    exact left_gram A hA.1
  · rw [Matrix.det_conjTranspose, hA.2, star_one]

private theorem specialUnitary_mul (A B : TitsComplexMatrix)
    (hA : A * A.conjTranspose = 1 ∧ A.det = 1)
    (hB : B * B.conjTranspose = 1 ∧ B.det = 1) :
    (A * B) * (A * B).conjTranspose = 1 ∧ (A * B).det = 1 := by
  constructor
  · rw [Matrix.conjTranspose_mul]
    calc
      (A * B) * (B.conjTranspose * A.conjTranspose) =
          A * ((B * B.conjTranspose) * A.conjTranspose) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hB.1, Matrix.one_mul, hA.1]
  · rw [Matrix.det_mul, hA.2, hB.2, one_mul]

/-- Every actual normalized matrix remains special unitary. -/
theorem completionRightNormalization_specialUnitary
    (U : Fin 9 → TitsComplexMatrix)
    (hU : ∀ i, U i * (U i).conjTranspose = 1 ∧ (U i).det = 1) (i : Fin 9) :
    completionRightNormalization U i * (completionRightNormalization U i).conjTranspose = 1 ∧
      (completionRightNormalization U i).det = 1 :=
  specialUnitary_mul (U i) (U 0).conjTranspose (hU i) (specialUnitary_adjoint (U 0) (hU 0))

/-- The actual zeroth array label is normalized to the identity. -/
theorem completionRightNormalization_zero (U : Fin 9 → TitsComplexMatrix)
    (hU : ∀ i, U i * (U i).conjTranspose = 1 ∧ (U i).det = 1) :
    completionRightNormalization U 0 = (1 : TitsComplexMatrix) := (hU 0).1

/-- Common-right normalization is invariant under one common right unitary.
The algebraic identity itself needs no determinant or SU3 condition on U. -/
theorem completionRightNormalization_common_right (U : Fin 9 → TitsComplexMatrix)
    (R : TitsComplexMatrix) (hR : R * R.conjTranspose = 1) :
    completionRightNormalization (fun i => U i * R) = completionRightNormalization U := by
  funext i
  unfold completionRightNormalization
  rw [Matrix.conjTranspose_mul]
  calc
    (U i * R) * (R.conjTranspose * (U 0).conjTranspose) =
        U i * ((R * R.conjTranspose) * (U 0).conjTranspose) := by simp only [Matrix.mul_assoc]
    _ = U i * (U 0).conjTranspose := by rw [hR, Matrix.one_mul]

/-- Every common-right parameter is recovered explicitly from the zeroth
actual matrices, with no presumed normalized-equality or quotient interface. -/
theorem completionRightNormalization_parameter (U V : Fin 9 → TitsComplexMatrix)
    (hU : ∀ i, U i * (U i).conjTranspose = 1 ∧ (U i).det = 1)
    (R : TitsComplexMatrix) (hR : ∀ i, V i = U i * R) :
    R = (U 0).conjTranspose * V 0 := by
  rw [hR 0, ← Matrix.mul_assoc, left_gram (U 0) (hU 0).1, Matrix.one_mul]

/-- Equal normalized actual arrays are exactly the common-right SU3 fibres.
The common multiplier is unique; the preceding lemma identifies U_0† V_0. -/
theorem completionRightNormalization_fibre (U V : Fin 9 → TitsComplexMatrix)
    (hU : ∀ i, U i * (U i).conjTranspose = 1 ∧ (U i).det = 1)
    (hV : ∀ i, V i * (V i).conjTranspose = 1 ∧ (V i).det = 1) :
    completionRightNormalization U = completionRightNormalization V ↔
      ∃! R : TitsComplexMatrix,
        R * R.conjTranspose = 1 ∧ R.det = 1 ∧ ∀ i : Fin 9, V i = U i * R := by
  constructor
  · intro hnorm
    let R := (U 0).conjTranspose * V 0
    have hsu : R * R.conjTranspose = 1 ∧ R.det = 1 :=
      specialUnitary_mul (U 0).conjTranspose (V 0)
        (specialUnitary_adjoint (U 0) (hU 0)) (hV 0)
    have haction (i : Fin 9) : V i = U i * R := by
      have hi := congrFun hnorm i
      change U i * (U 0).conjTranspose = V i * (V 0).conjTranspose at hi
      calc
        V i = (V i * (V 0).conjTranspose) * V 0 := by
          rw [Matrix.mul_assoc, left_gram (V 0) (hV 0).1, Matrix.mul_one]
        _ = (U i * (U 0).conjTranspose) * V 0 := by rw [hi]
        _ = U i * R := Matrix.mul_assoc _ _ _
    refine ⟨R, ⟨hsu.1, hsu.2, haction⟩, ?_⟩
    intro S hS
    exact completionRightNormalization_parameter U V hU S hS.2.2
  · rintro ⟨R, hR, _⟩
    have hVeq : V = fun i => U i * R := funext hR.2.2
    rw [hVeq, completionRightNormalization_common_right U R hR.1]

end CompactAlbert

module

public import ChallengeUEBDefinitions
public import NativeNineFrameDictionary
public import NativeRightSU3Action
public import NativePolynomialEvaluationStaged

/-
# The actual nine-frame dictionary in the existing Challenge UEB interface

The exact Challenge definitions are imported from their single-owner
extraction. Explicit matrix/label equivalences retain the ZMod indices and
clock-first labels; the left/right Gram conversion uses the existing unitary
group iff lemmas. The native endpoint composes the already proved actual
nine-frame iff, retaining each independent central/reverse order.

This is a first-party finite-index and theorem-composition adapter, not a
replacement UEB predicate or a new classification. No frame property,
evaluation identity, gauge quotient or exhaustive fixer is assumed. Original
thirteen-frame/quartet properties, residual ideals, analytic derivatives and
the final Challenge's later endpoints remain separate.

Native and adapted-code notices are preserved in the imported modules:
https://github.com/macgregor-sudo/compact-albert-recognition,
commit 40d3b344180d9ddb78aaa2876873377c1e631515. Matrix/index APIs come from
https://github.com/leanprover-community/mathlib4,
commit 065356127b1dc0016f66b7283ce0ce2c4055aa55. No proof body is copied here.
Thanks to those projects' contributors for the reused results; no release
license is assigned to new first-party contributions.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/


@[expose] public section
noncomputable section

namespace CompactAlbert

open UnitaryErrorBases.ComplexQuartet

/-- The explicit row/column index map; at this pin its positive branch is refl. -/
def challengeMatrixIndexEquiv : Fin 3 ≃ UnitaryErrorBases.Index :=
  (ZMod.finEquiv 3).toEquiv

/-- Clock index first: the ordered label (a,b) has native array index 3a+b. -/
def challengeLabelEquiv : UnitaryErrorBases.Label ≃ Fin 9 :=
  (challengeMatrixIndexEquiv.symm.prodCongr challengeMatrixIndexEquiv.symm).trans
    finProdFinEquiv

theorem challengeLabelEquiv_val (p : UnitaryErrorBases.Label) :
    (challengeLabelEquiv p).val = 3 * p.1.val + p.2.val := by
  change p.2.val + 3 * p.1.val = 3 * p.1.val + p.2.val
  exact Nat.add_comm _ _

/-- Both index maps have the same orientation; there is no transpose or star. -/
def challengeMatrixEquiv : TitsComplexMatrix ≃ UnitaryErrorBases.Mat :=
  Matrix.reindex challengeMatrixIndexEquiv challengeMatrixIndexEquiv

theorem challengeMatrixEquiv_apply (A : TitsComplexMatrix)
    (i j : UnitaryErrorBases.Index) :
    challengeMatrixEquiv A i j =
      A (challengeMatrixIndexEquiv.symm i) (challengeMatrixIndexEquiv.symm j) := rfl

/-- The two matrix index types coincide at this pin; the displayed equivalence
therefore preserves this exact Hilbert–Schmidt trace by typed reduction. -/
theorem challengeMatrixEquiv_hilbertSchmidt_trace (A B : TitsComplexMatrix) :
    ((challengeMatrixEquiv A).conjTranspose * challengeMatrixEquiv B).trace =
      (A.conjTranspose * B).trace := rfl

/-- The existing Challenge predicate uses the left Gram equation. The native
dictionary uses the equivalent right Gram equation, with determinant unchanged. -/
theorem challengeMatrixEquiv_specialUnitary_iff (A : TitsComplexMatrix) :
    UnitaryErrorBases.IsSpecialUnitary (challengeMatrixEquiv A) ↔
      A * A.conjTranspose = (1 : TitsComplexMatrix) ∧ A.det = 1 := by
  change (A.conjTranspose * A = 1 ∧ A.det = 1) ↔
    (A * A.conjTranspose = 1 ∧ A.det = 1)
  have hleft : A ∈ Matrix.unitaryGroup (Fin 3) ℂ ↔ A.conjTranspose * A = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff' (A := A))
  have hright : A ∈ Matrix.unitaryGroup (Fin 3) ℂ ↔ A * A.conjTranspose = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff (A := A))
  exact and_congr (hleft.symm.trans hright) Iff.rfl

/-- The native nine matrices, now in the existing Challenge's exact family type. -/
def challengeFamilyOfNativeArray (U : Fin 9 → TitsComplexMatrix) : UnitaryErrorBases.Family :=
  fun p => challengeMatrixEquiv (U (challengeLabelEquiv p))

/-- The explicit inverse label/matrix maps, retaining every ordered label. -/
def nativeArrayOfChallengeFamily (U : UnitaryErrorBases.Family) : Fin 9 → TitsComplexMatrix :=
  fun r => challengeMatrixEquiv.symm (U (challengeLabelEquiv.symm r))

theorem nativeArrayOfChallengeFamily_challengeFamilyOfNativeArray
    (U : Fin 9 → TitsComplexMatrix) :
    nativeArrayOfChallengeFamily (challengeFamilyOfNativeArray U) = U := by
  funext r
  simp only [nativeArrayOfChallengeFamily, challengeFamilyOfNativeArray,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply]

theorem challengeFamilyOfNativeArray_nativeArrayOfChallengeFamily
    (U : UnitaryErrorBases.Family) :
    challengeFamilyOfNativeArray (nativeArrayOfChallengeFamily U) = U := by
  funext p
  simp only [nativeArrayOfChallengeFamily, challengeFamilyOfNativeArray,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- This is the existing IsUnitaryErrorBasis identifier, with its exact frozen
body. Every change of finite index and Gram convention is explicit. -/
theorem challengeFamilyOfNativeArray_isUnitaryErrorBasis_iff
    (U : Fin 9 → TitsComplexMatrix) :
    UnitaryErrorBases.IsUnitaryErrorBasis (challengeFamilyOfNativeArray U) ↔
      (∀ r : Fin 9, U r * (U r).conjTranspose = (1 : TitsComplexMatrix) ∧
        (U r).det = 1) ∧
      (∀ r s : Fin 9, r ≠ s → ((U r).conjTranspose * U s).trace = 0) := by
  constructor
  · rintro ⟨hunitary, horthogonal⟩
    constructor
    · intro r
      have h := hunitary (challengeLabelEquiv.symm r)
      change UnitaryErrorBases.IsSpecialUnitary
        (challengeMatrixEquiv (U (challengeLabelEquiv (challengeLabelEquiv.symm r)))) at h
      rw [Equiv.apply_symm_apply] at h
      exact (challengeMatrixEquiv_specialUnitary_iff (U r)).mp h
    · intro r s hrs
      have hne : challengeLabelEquiv.symm r ≠ challengeLabelEquiv.symm s :=
        fun h => hrs (challengeLabelEquiv.symm.injective h)
      have h := horthogonal _ _ hne
      change ((challengeMatrixEquiv (U (challengeLabelEquiv (challengeLabelEquiv.symm r)))).conjTranspose *
        challengeMatrixEquiv (U (challengeLabelEquiv (challengeLabelEquiv.symm s)))).trace = 0 at h
      simpa only [Equiv.apply_symm_apply, challengeMatrixEquiv_hilbertSchmidt_trace] using h
  · rintro ⟨hunitary, horthogonal⟩
    constructor
    · intro p
      change UnitaryErrorBases.IsSpecialUnitary (challengeMatrixEquiv (U (challengeLabelEquiv p)))
      exact (challengeMatrixEquiv_specialUnitary_iff _).mpr (hunitary _)
    · intro p q hpq
      change ((challengeMatrixEquiv (U (challengeLabelEquiv p))).conjTranspose *
        challengeMatrixEquiv (U (challengeLabelEquiv q))).trace = 0
      rw [challengeMatrixEquiv_hilbertSchmidt_trace]
      exact horthogonal _ _ (fun h => hpq (challengeLabelEquiv.injective h))

/-- The actual nine-frame dictionary now concludes the exact existing Challenge
UEB predicate. Each frame's central or reverse order remains part of the witness. -/
theorem native_nine_complementary_frames_iff_exists_challenge_UEB
    (p : Fin 9 → Fin 3 → Glennie.Albert) :
    ((∀ r : Fin 9, Glennie.Frame (p r)) ∧
      (∀ (r : Fin 9) (i t : Fin 3), Glennie.trace
        (Glennie.jordan (p r i) (literalNativeCoordinatePoint t)) = (1 / 3 : ℝ)) ∧
      (∀ (r : Fin 9) (i : Fin 3) (s t : PhaseIndex), Glennie.trace
        (Glennie.jordan (p r i) (literalNativePhasePoint s t)) = (1 / 3 : ℝ)) ∧
      (∀ r s : Fin 9, r ≠ s → ∀ i j : Fin 3, Glennie.trace
        (Glennie.jordan (p r i) (p s j)) = (1 / 3 : ℝ))) ↔
      ∃ U : UnitaryErrorBases.Family,
        UnitaryErrorBases.IsUnitaryErrorBasis U ∧
        (∀ r : Fin 9,
          p r = nativeCentralTriple (nativeArrayOfChallengeFamily U r) ∨
          p r = nativeReverseCentralTriple (nativeArrayOfChallengeFamily U r)) := by
  constructor
  · intro h
    rcases (native_nine_complementary_frames_iff_exists_unitary_array p).mp h with
      ⟨U, hunitary, horthogonal, horder⟩
    refine ⟨challengeFamilyOfNativeArray U,
      (challengeFamilyOfNativeArray_isUnitaryErrorBasis_iff U).mpr ⟨hunitary, horthogonal⟩, ?_⟩
    rw [nativeArrayOfChallengeFamily_challengeFamilyOfNativeArray]
    exact horder
  · rintro ⟨U, hUEB, horder⟩
    have hconditions :=
      (challengeFamilyOfNativeArray_isUnitaryErrorBasis_iff (nativeArrayOfChallengeFamily U)).mp
        (by simpa only [challengeFamilyOfNativeArray_nativeArrayOfChallengeFamily] using hUEB)
    exact (native_nine_complementary_frames_iff_exists_unitary_array p).mpr
      ⟨nativeArrayOfChallengeFamily U, hconditions.1, hconditions.2, horder⟩

end CompactAlbert

/- The exact Challenge predicate composed with the actual native dictionary,
co-importing the action and polynomial-evaluation ownership branches. -/


#check @CompactAlbert.challengeMatrixIndexEquiv
#print axioms CompactAlbert.challengeMatrixIndexEquiv
#check @CompactAlbert.challengeLabelEquiv
#print axioms CompactAlbert.challengeLabelEquiv
#check @CompactAlbert.challengeLabelEquiv_val
#print axioms CompactAlbert.challengeLabelEquiv_val
#check @CompactAlbert.challengeMatrixEquiv
#print axioms CompactAlbert.challengeMatrixEquiv
#check @CompactAlbert.challengeMatrixEquiv_apply
#print axioms CompactAlbert.challengeMatrixEquiv_apply
#check @CompactAlbert.challengeMatrixEquiv_hilbertSchmidt_trace
#print axioms CompactAlbert.challengeMatrixEquiv_hilbertSchmidt_trace
#check @CompactAlbert.challengeMatrixEquiv_specialUnitary_iff
#print axioms CompactAlbert.challengeMatrixEquiv_specialUnitary_iff
#check @CompactAlbert.challengeFamilyOfNativeArray
#print axioms CompactAlbert.challengeFamilyOfNativeArray
#check @CompactAlbert.nativeArrayOfChallengeFamily
#print axioms CompactAlbert.nativeArrayOfChallengeFamily
#check @CompactAlbert.nativeArrayOfChallengeFamily_challengeFamilyOfNativeArray
#print axioms CompactAlbert.nativeArrayOfChallengeFamily_challengeFamilyOfNativeArray
#check @CompactAlbert.challengeFamilyOfNativeArray_nativeArrayOfChallengeFamily
#print axioms CompactAlbert.challengeFamilyOfNativeArray_nativeArrayOfChallengeFamily
#check @CompactAlbert.challengeFamilyOfNativeArray_isUnitaryErrorBasis_iff
#print axioms CompactAlbert.challengeFamilyOfNativeArray_isUnitaryErrorBasis_iff
#check @CompactAlbert.native_nine_complementary_frames_iff_exists_challenge_UEB
#print axioms CompactAlbert.native_nine_complementary_frames_iff_exists_challenge_UEB

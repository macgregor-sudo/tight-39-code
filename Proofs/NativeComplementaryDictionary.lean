/-
# Native complementary-frame overlap and the ordered matrix dictionary

All-nine overlaps compose the existing actual native trace formula with
matrix trace scaling. No octonion, Albert-product or metric foundation is
reproved. The prior SectorModel.inner_sector_model and SectorTitsProduct
adapter already establish the inherited metric; the imported first-party
module links that metric to the current emitted native model.

The actual overlap convention is Re tr(U Vᴴ). The Hilbert–Schmidt convention
tr(Uᴴ V) is retained by an explicit complex-conjugation identity and a zero
equivalence. Both possible central orders are included. The final dictionary
is an existence iff for the existing native Frame and the original quartet
readouts, using ordinary matrices with explicit Gram/determinant equations.
It is not a packaged bijection, gauge quotient or UEB classification.

These are first-party compositions of classical compact Albert/matrix
arguments, without copied proof bodies or a novelty claim. Complete native
source notices and mathematical attribution remain in the imported modules.
Thanks to those authors and to the Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/
module

public import NativeComplementaryConstruction

@[expose] public section
noncomputable section

namespace CompactAlbert

open UnitaryErrorBases.ComplexQuartet UnitaryErrorBases.ThreeCycleFourier

/-- The two complex trace conventions are conjugates, not equal in general. -/
theorem matrixTrace_pair_eq_star_hilbertSchmidt (U V : TitsComplexMatrix) :
    (U * V.conjTranspose).trace = star ((U.conjTranspose * V).trace) := by
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.trace_mul_comm V.conjTranspose U] using
    Matrix.trace_conjTranspose (U.conjTranspose * V)

/-- Complex trace zero is unchanged when passing to the Hilbert–Schmidt order. -/
theorem matrixTrace_pair_zero_iff_hilbertSchmidt_zero (U V : TitsComplexMatrix) :
    (U * V.conjTranspose).trace = 0 ↔ (U.conjTranspose * V).trace = 0 := by
  rw [matrixTrace_pair_eq_star_hilbertSchmidt]
  simp

/-- Central matrix phases rotate the existing actual native overlap. -/
theorem nativeComplementaryPoint_overlap_smul
    (U V : TitsComplexMatrix) (c d : ℂ) :
    Glennie.trace (Glennie.jordan (nativeComplementaryPoint (c • U))
      (nativeComplementaryPoint (d • V))) =
        1 / 3 + (2 / 9 : ℝ) *
          (c * star d * (U * V.conjTranspose).trace).re := by
  rw [nativeComplementaryPoint_overlap, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul]
  rfl

private theorem complex_eq_zero_of_two_rotated_real_readouts (z : ℂ)
    (hreal : z.re = 0) (hrotated : (omega * z).re = 0) : z = 0 := by
  have him : omega.im ≠ 0 := by
    have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
    have hi : omega.im = Real.sqrt (3 : ℝ) / 2 := by
      norm_num [omega, Complex.mul_re, Complex.mul_im]
    rw [hi]
    exact ne_of_gt (div_pos hs (by norm_num))
  apply Complex.ext
  · exact hreal
  · change z.im = 0
    have hproduct : omega.im * z.im = 0 := by
      rw [Complex.mul_re, hreal] at hrotated
      linarith
    exact (mul_eq_zero.mp hproduct).resolve_left him

/-- All nine actual overlaps are one third exactly when the complex matrix
trace vanishes. No special-unitary or frame premise is required. -/
theorem native_central_triples_overlap_iff (U V : TitsComplexMatrix) :
    (∀ i j : Fin 3, Glennie.trace
      (Glennie.jordan (nativeCentralTriple U i) (nativeCentralTriple V j)) =
        (1 / 3 : ℝ)) ↔ (U * V.conjTranspose).trace = 0 := by
  constructor
  · intro h
    have h00 : Glennie.trace (Glennie.jordan (nativeComplementaryPoint U)
        (nativeComplementaryPoint V)) = (1 / 3 : ℝ) := h 0 0
    have h10 : Glennie.trace (Glennie.jordan (nativeComplementaryPoint (omega • U))
        (nativeComplementaryPoint V)) = (1 / 3 : ℝ) := h 1 0
    have hreal := (nativeComplementaryPoint_overlap_eq_third_iff U V).mp h00
    have hrotated :=
      (nativeComplementaryPoint_overlap_eq_third_iff (omega • U) V).mp h10
    have hrotated' : (omega * (U * V.conjTranspose).trace).re = 0 := by
      simpa only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] using hrotated
    exact complex_eq_zero_of_two_rotated_real_readouts _ hreal hrotated'
  · intro hz
    have hphase (c d : ℂ) :
        Glennie.trace (Glennie.jordan (nativeComplementaryPoint (c • U))
          (nativeComplementaryPoint (d • V))) = (1 / 3 : ℝ) := by
      rw [nativeComplementaryPoint_overlap_smul, hz]
      simp
    intro i j
    fin_cases i <;> fin_cases j
    · change Glennie.trace (Glennie.jordan (nativeComplementaryPoint U)
        (nativeComplementaryPoint V)) = (1 / 3 : ℝ)
      simpa only [one_smul] using hphase 1 1
    · change Glennie.trace (Glennie.jordan (nativeComplementaryPoint U)
        (nativeComplementaryPoint (omega • V))) = (1 / 3 : ℝ)
      simpa only [one_smul] using hphase 1 omega
    · change Glennie.trace (Glennie.jordan (nativeComplementaryPoint U)
        (nativeComplementaryPoint ((omega ^ 2) • V))) = (1 / 3 : ℝ)
      simpa only [one_smul] using hphase 1 (omega ^ 2)
    · change Glennie.trace (Glennie.jordan (nativeComplementaryPoint (omega • U))
        (nativeComplementaryPoint V)) = (1 / 3 : ℝ)
      simpa only [one_smul] using hphase omega 1
    · exact hphase omega omega
    · exact hphase omega (omega ^ 2)
    · change Glennie.trace (Glennie.jordan (nativeComplementaryPoint ((omega ^ 2) • U))
        (nativeComplementaryPoint V)) = (1 / 3 : ℝ)
      simpa only [one_smul] using hphase (omega ^ 2) 1
    · exact hphase (omega ^ 2) omega
    · exact hphase (omega ^ 2) (omega ^ 2)

private theorem forall_reverseCentralTriple_iff
    (U : TitsComplexMatrix) (P : Glennie.Albert → Prop) :
    (∀ i : Fin 3, P (nativeReverseCentralTriple U i)) ↔
      (∀ i : Fin 3, P (nativeCentralTriple U i)) := by
  constructor
  · intro h i
    fin_cases i
    · exact h 0
    · exact h 2
    · exact h 1
  · intro h i
    fin_cases i
    · exact h 0
    · exact h 2
    · exact h 1

/-- Either central orientation of each ordered triple has the same all-nine
criterion; the universal readouts are unaffected by swapping outcomes 1,2. -/
theorem native_ordered_central_triples_overlap_iff
    (U V : TitsComplexMatrix) (p q : Fin 3 → Glennie.Albert)
    (hp : p = nativeCentralTriple U ∨ p = nativeReverseCentralTriple U)
    (hq : q = nativeCentralTriple V ∨ q = nativeReverseCentralTriple V) :
    (∀ i j : Fin 3, Glennie.trace (Glennie.jordan (p i) (q j)) = (1 / 3 : ℝ)) ↔
      (U * V.conjTranspose).trace = 0 := by
  let R : Glennie.Albert → Glennie.Albert → Prop :=
    fun x y => Glennie.trace (Glennie.jordan x y) = (1 / 3 : ℝ)
  have hright (a : Fin 3 → Glennie.Albert) :
      (∀ i j : Fin 3, R (a i) (nativeReverseCentralTriple V j)) ↔
        (∀ i j : Fin 3, R (a i) (nativeCentralTriple V j)) := by
    constructor
    · intro h i
      exact (forall_reverseCentralTriple_iff V (R (a i))).mp (h i)
    · intro h i
      exact (forall_reverseCentralTriple_iff V (R (a i))).mpr (h i)
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact native_central_triples_overlap_iff U V
  · exact (hright (nativeCentralTriple U)).trans (native_central_triples_overlap_iff U V)
  · exact (forall_reverseCentralTriple_iff U
      (fun x => ∀ j : Fin 3, R x (nativeCentralTriple V j))).trans
        (native_central_triples_overlap_iff U V)
  · exact (forall_reverseCentralTriple_iff U
      (fun x => ∀ j : Fin 3, R x (nativeReverseCentralTriple V j))).trans
        ((hright (nativeCentralTriple U)).trans (native_central_triples_overlap_iff U V))

/-- The all-nine criterion in the frozen Hilbert–Schmidt matrix convention. -/
theorem native_ordered_central_triples_overlap_iff_hilbertSchmidt
    (U V : TitsComplexMatrix) (p q : Fin 3 → Glennie.Albert)
    (hp : p = nativeCentralTriple U ∨ p = nativeReverseCentralTriple U)
    (hq : q = nativeCentralTriple V ∨ q = nativeReverseCentralTriple V) :
    (∀ i j : Fin 3, Glennie.trace (Glennie.jordan (p i) (q j)) = (1 / 3 : ℝ)) ↔
      (U.conjTranspose * V).trace = 0 :=
  (native_ordered_central_triples_overlap_iff U V p q hp hq).trans
    (matrixTrace_pair_zero_iff_hilbertSchmidt_zero U V)

/-- The actual visible-third point is recovered by its literal scaled hidden
matrix, using injectivity of the existing native coordinate map. -/
theorem nativeComplementaryPoint_scaled_hidden_inverse (x : Glennie.Albert)
    (ha : hermitianMatrix (toTitsCoordinates x) =
      (1 / 3 : ℂ) • (1 : TitsComplexMatrix)) :
    nativeComplementaryPoint ((3 : ℂ) • (toTitsCoordinates x).2.2) = x := by
  apply nativeTitsMatrixPair_injective
  rw [nativeComplementaryPoint_pair]
  change ((1 / 3 : ℂ) • (1 : TitsComplexMatrix),
      (1 / 3 : ℂ) • ((3 : ℂ) • (toTitsCoordinates x).2.2)) =
    (hermitianMatrix (toTitsCoordinates x), (toTitsCoordinates x).2.2)
  rw [ha]
  norm_num [smul_smul]

/-- Native frames with the original quartet readouts are precisely the two
central orders of a matrix with explicit special-unitary equations. This
is an existence dictionary, with no gauge or uniqueness assertion. -/
theorem native_complementary_frame_iff_exists_central_order
    (p : Fin 3 → Glennie.Albert) :
    (Glennie.Frame p ∧
      (∀ i t : Fin 3, Glennie.trace
        (Glennie.jordan (p i) (literalNativeCoordinatePoint t)) = (1 / 3 : ℝ)) ∧
      (∀ (i : Fin 3) (s t : PhaseIndex), Glennie.trace
        (Glennie.jordan (p i) (literalNativePhasePoint s t)) = (1 / 3 : ℝ))) ↔
      ∃ U : TitsComplexMatrix,
        (U * U.conjTranspose = (1 : TitsComplexMatrix) ∧ U.det = 1) ∧
          (p = nativeCentralTriple U ∨ p = nativeReverseCentralTriple U) := by
  constructor
  · rintro ⟨hframe, hE, hP⟩
    let U : Fin 3 → TitsComplexMatrix :=
      fun i => (3 : ℂ) • (toTitsCoordinates (p i)).2.2
    have hU : U 0 * (U 0).conjTranspose = (1 : TitsComplexMatrix) ∧ (U 0).det = 1 :=
      (native_idempotent_iff_scaled_specialUnitary_of_literal_quartet_readouts
        (p 0) (hE 0) (hP 0)).mp (hframe.idempotent 0)
    have hrecover (i : Fin 3) : nativeComplementaryPoint (U i) = p i :=
      nativeComplementaryPoint_scaled_hidden_inverse (p i)
        ((native_literal_quartet_readouts_iff (p i)).mp ⟨hE i, hP i⟩)
    have hcentral := native_complementary_triple_hidden_central_alternatives
      p hframe.idempotent hE hP hframe.sum_unit
    change (U 1 = omega • U 0 ∧ U 2 = omega ^ 2 • U 0) ∨
      (U 1 = omega ^ 2 • U 0 ∧ U 2 = omega • U 0) at hcentral
    refine ⟨U 0, hU, ?_⟩
    rcases hcentral with h | h
    · left
      funext i
      fin_cases i
      · exact (hrecover 0).symm
      · change p 1 = nativeComplementaryPoint (omega • U 0)
        rw [← h.1]
        exact (hrecover 1).symm
      · change p 2 = nativeComplementaryPoint ((omega ^ 2) • U 0)
        rw [← h.2]
        exact (hrecover 2).symm
    · right
      funext i
      fin_cases i
      · exact (hrecover 0).symm
      · change p 1 = nativeComplementaryPoint ((omega ^ 2) • U 0)
        rw [← h.1]
        exact (hrecover 1).symm
      · change p 2 = nativeComplementaryPoint (omega • U 0)
        rw [← h.2]
        exact (hrecover 2).symm
  · rintro ⟨U, hU, horder⟩
    have hframes := native_central_triples_are_frames U hU
    rcases horder with rfl | rfl
    · refine ⟨hframes.1, ?_, ?_⟩
      · intro i t
        fin_cases i <;> exact (nativeComplementaryPoint_literal_readouts _).1 t
      · intro i s t
        fin_cases i <;> exact (nativeComplementaryPoint_literal_readouts _).2 s t
    · refine ⟨hframes.2, ?_, ?_⟩
      · intro i t
        fin_cases i <;> exact (nativeComplementaryPoint_literal_readouts _).1 t
      · intro i s t
        fin_cases i <;> exact (nativeComplementaryPoint_literal_readouts _).2 s t

end CompactAlbert



#check @CompactAlbert.matrixTrace_pair_eq_star_hilbertSchmidt
#check @CompactAlbert.matrixTrace_pair_zero_iff_hilbertSchmidt_zero
#check @CompactAlbert.nativeComplementaryPoint_overlap_smul
#check @CompactAlbert.native_central_triples_overlap_iff
#check @CompactAlbert.native_ordered_central_triples_overlap_iff
#check @CompactAlbert.native_ordered_central_triples_overlap_iff_hilbertSchmidt
#check @CompactAlbert.nativeComplementaryPoint_scaled_hidden_inverse
#check @CompactAlbert.native_complementary_frame_iff_exists_central_order

#print axioms CompactAlbert.matrixTrace_pair_eq_star_hilbertSchmidt
#print axioms CompactAlbert.matrixTrace_pair_zero_iff_hilbertSchmidt_zero
#print axioms CompactAlbert.nativeComplementaryPoint_overlap_smul
#print axioms CompactAlbert.native_central_triples_overlap_iff
#print axioms CompactAlbert.native_ordered_central_triples_overlap_iff
#print axioms CompactAlbert.native_ordered_central_triples_overlap_iff_hilbertSchmidt
#print axioms CompactAlbert.nativeComplementaryPoint_scaled_hidden_inverse
#print axioms CompactAlbert.native_complementary_frame_iff_exists_central_order

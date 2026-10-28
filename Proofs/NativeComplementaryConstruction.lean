/-
# Constructing native complementary frames from special-unitary matrices

The actual native point has visible component I/3 and hidden component U/3.
The existing inverse coordinate map constructs the point, while all products,
traces, readouts, sums and frame assertions below use the original native
operations. No frame property is an input to the construction.

These first-party application proofs compose the existing compact Albert
point dictionary with elementary central cube-root arithmetic. The actual
native residual identity supplies orthogonality from idempotency and unit
sum; it uses no spectral or positivity argument. The ordered reverse frame
is retained. The single-pair overlap keeps the adjoint on the second matrix;
full cross-frame complex trace orthogonality is a separate endpoint.

This is classical compact Albert/second-Tits mathematics, already described
in MASTER6.2, not a novelty claim. Inherited source attribution, complete
Apache-2.0 notices and mathematical references remain in the imported
first-party sources; no proof body below is copied from another source.
Thanks to those source authors and to the Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/
module

public import NativeComplementaryTriples
public import LiteralComplexCharacterNorm

@[expose] public section
set_option backward.proofsInPublic true
noncomputable section

namespace CompactAlbert

open UnitaryErrorBases.ComplexQuartet UnitaryErrorBases.ThreeCycleFourier

/-- The actual native point with visible component I/3 and hidden component
U/3. No condition on U is imposed by this definition. -/
def nativeComplementaryPoint (U : TitsComplexMatrix) : Glennie.Albert :=
  fromTitsCoordinates ((fun _ => (1 / 3 : ℝ)), 0, (1 / 3 : ℂ) • U)

/-- Both actual matrix components of the constructed native point. -/
theorem nativeComplementaryPoint_pair (U : TitsComplexMatrix) :
    nativeTitsMatrixPair (nativeComplementaryPoint U) =
      ((1 / 3 : ℂ) • (1 : TitsComplexMatrix), (1 / 3 : ℂ) • U) := by
  change toMatrixPair (toTitsCoordinates (fromTitsCoordinates _)) = _
  rw [toTitsCoordinates_fromTitsCoordinates]
  apply Prod.ext
  · apply Matrix.ext
    intro row column
    fin_cases row <;> fin_cases column <;>
      norm_num [toMatrixPair, hermitianMatrix, Matrix.smul_apply]
  · rfl

theorem nativeComplementaryPoint_visible (U : TitsComplexMatrix) :
    hermitianMatrix (toTitsCoordinates (nativeComplementaryPoint U)) =
      (1 / 3 : ℂ) • (1 : TitsComplexMatrix) :=
  congrArg (fun p : TitsMatrixPair => p.1) (nativeComplementaryPoint_pair U)

theorem nativeComplementaryPoint_scaled_hidden (U : TitsComplexMatrix) :
    (3 : ℂ) • (toTitsCoordinates (nativeComplementaryPoint U)).2.2 = U := by
  have h := congrArg (fun p : TitsMatrixPair => p.2) (nativeComplementaryPoint_pair U)
  change (toTitsCoordinates (nativeComplementaryPoint U)).2.2 = (1 / 3 : ℂ) • U at h
  rw [h]
  norm_num [smul_smul]

/-- The constructor's ordinary native trace is one for every U. -/
theorem nativeComplementaryPoint_trace (U : TitsComplexMatrix) :
    Glennie.trace (nativeComplementaryPoint U) = 1 :=
  native_trace_eq_one_of_visible_third _ (nativeComplementaryPoint_visible U)

/-- The constructed point has all twelve original native quartet readouts,
without an idempotency hypothesis. -/
theorem nativeComplementaryPoint_literal_readouts (U : TitsComplexMatrix) :
    (∀ t : Fin 3, Glennie.trace (Glennie.jordan (nativeComplementaryPoint U)
      (literalNativeCoordinatePoint t)) = (1 / 3 : ℝ)) ∧
    (∀ s t : PhaseIndex, Glennie.trace (Glennie.jordan (nativeComplementaryPoint U)
      (literalNativePhasePoint s t)) = (1 / 3 : ℝ)) :=
  (native_literal_quartet_readouts_iff _).mpr (nativeComplementaryPoint_visible U)

/-- Idempotency is proved equivalent to the explicit special-unitary
equations on the input matrix, rather than imposed by the constructor. -/
theorem nativeComplementaryPoint_idempotent_iff (U : TitsComplexMatrix) :
    Glennie.jordan (nativeComplementaryPoint U) (nativeComplementaryPoint U) =
        nativeComplementaryPoint U ↔
      U * U.conjTranspose = (1 : TitsComplexMatrix) ∧ U.det = 1 := by
  simpa only [nativeComplementaryPoint_scaled_hidden] using
    native_idempotent_iff_scaled_specialUnitary_conditions
      (nativeComplementaryPoint U) (nativeComplementaryPoint_visible U)

private theorem omega_mul_star_eq_one : omega * star omega = 1 := by
  have hn : Complex.normSq omega = 1 := by
    simpa [UnitaryErrorBases.ThreeCycleFourier.character, ZMod.val_one_eq_one_mod] using
      character_normSq_eq_one (1 : PhaseIndex)
  simpa only [Complex.star_def, Complex.mul_conj, hn, Complex.ofReal_one]

private theorem specialUnitary_conditions_smul
    (U : TitsComplexMatrix) (c : ℂ)
    (hU : U * U.conjTranspose = (1 : TitsComplexMatrix) ∧ U.det = 1)
    (hc : c * star c = 1) (hcube : c ^ 3 = 1) :
    (c • U) * (c • U).conjTranspose = (1 : TitsComplexMatrix) ∧
      (c • U).det = 1 := by
  constructor
  · rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hU.1, hc, one_smul]
  · rw [Matrix.det_smul, hU.2]
    norm_num [hcube]

private theorem omega_sq_mul_star_eq_one : omega ^ 2 * star (omega ^ 2) = 1 := by
  rw [star_pow, ← mul_pow, omega_mul_star_eq_one]
  norm_num

private theorem omega_sq_cube : (omega ^ 2) ^ 3 = 1 := by
  calc
    (omega ^ 2) ^ 3 = (omega ^ 3) ^ 2 := by ring
    _ = 1 := by rw [omega_cube]; norm_num

/-- The two possible ordered central triples use the project's fixed omega. -/
def nativeCentralTriple (U : TitsComplexMatrix) : Fin 3 → Glennie.Albert :=
  ![nativeComplementaryPoint U, nativeComplementaryPoint (omega • U),
    nativeComplementaryPoint ((omega ^ 2) • U)]

def nativeReverseCentralTriple (U : TitsComplexMatrix) : Fin 3 → Glennie.Albert :=
  ![nativeComplementaryPoint U, nativeComplementaryPoint ((omega ^ 2) • U),
    nativeComplementaryPoint (omega • U)]

/-- The actual three-point sum is the native unit, for arbitrary U. -/
theorem nativeCentralTriple_sum (U : TitsComplexMatrix) :
    nativeCentralTriple U 0 + nativeCentralTriple U 1 +
      nativeCentralTriple U 2 = 1 := by
  apply nativeTitsMatrixPair_injective
  rw [map_add, map_add]
  have hunit : nativeTitsMatrixPair (1 : Glennie.Albert) =
      (1, 0) := by
    change toMatrixPair (compactTitsCoordinateEquiv (1 : Glennie.Albert)) = _
    rw [compactTitsCoordinateEquiv_unit]
    apply Prod.ext
    · apply Matrix.ext
      intro row column
      fin_cases row <;> fin_cases column <;>
        norm_num [toMatrixPair, hermitianMatrix, titsUnit]
    · rfl
  change nativeTitsMatrixPair (nativeComplementaryPoint U) +
    nativeTitsMatrixPair (nativeComplementaryPoint (omega • U)) +
    nativeTitsMatrixPair (nativeComplementaryPoint ((omega ^ 2) • U)) = _
  rw [nativeComplementaryPoint_pair, nativeComplementaryPoint_pair,
    nativeComplementaryPoint_pair, hunit]
  apply Prod.ext
  · change (1 / 3 : ℂ) • (1 : TitsComplexMatrix) +
      (1 / 3 : ℂ) • (1 : TitsComplexMatrix) +
      (1 / 3 : ℂ) • (1 : TitsComplexMatrix) = 1
    module
  · change (1 / 3 : ℂ) • U + (1 / 3 : ℂ) • (omega • U) +
      (1 / 3 : ℂ) • ((omega ^ 2) • U) = 0
    rw [omega_sq]
    module

private theorem native_jordan_complement_residual_o01 (x y : Glennie.Albert) :
    ((2 : ℝ) • Glennie.jordan x y).o01 =
      ((Glennie.jordan (1 - x - y) (1 - x - y) - (1 - x - y)) -
        (Glennie.jordan x x - x) - (Glennie.jordan y y - y)).o01 := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [Glennie.jordan_o01, Glennie.octMul, Glennie.octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

private theorem native_jordan_complement_residual_o02 (x y : Glennie.Albert) :
    ((2 : ℝ) • Glennie.jordan x y).o02 =
      ((Glennie.jordan (1 - x - y) (1 - x - y) - (1 - x - y)) -
        (Glennie.jordan x x - x) - (Glennie.jordan y y - y)).o02 := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [Glennie.jordan_o02, Glennie.octMul, Glennie.octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

private theorem native_jordan_complement_residual_o12 (x y : Glennie.Albert) :
    ((2 : ℝ) • Glennie.jordan x y).o12 =
      ((Glennie.jordan (1 - x - y) (1 - x - y) - (1 - x - y)) -
        (Glennie.jordan x x - x) - (Glennie.jordan y y - y)).o12 := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [Glennie.jordan_o12, Glennie.octMul, Glennie.octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

/-- The elementary residual identity in the actual native coordinates.
The proof uses only the existing binary native entry formulas. -/
theorem native_jordan_complement_residual (x y : Glennie.Albert) :
    (2 : ℝ) • Glennie.jordan x y =
      (Glennie.jordan (1 - x - y) (1 - x - y) - (1 - x - y)) -
        (Glennie.jordan x x - x) - (Glennie.jordan y y - y) := by
  apply Glennie.Albert.extExplicit
  · simp [Glennie.jordan_d0, Glennie.octDot_coordinates,
      Glennie.octNormSq, Quaternion.normSq_def']
    ring
  · simp [Glennie.jordan_d1, Glennie.octDot_coordinates,
      Glennie.octNormSq, Quaternion.normSq_def']
    ring
  · simp [Glennie.jordan_d2, Glennie.octDot_coordinates,
      Glennie.octNormSq, Quaternion.normSq_def']
    ring
  · exact native_jordan_complement_residual_o01 x y
  · exact native_jordan_complement_residual_o02 x y
  · exact native_jordan_complement_residual_o12 x y

/-- Three actual idempotents summing to the unit are orthogonal pairwise.
No positivity or trace condition is needed for this pairwise consequence. -/
theorem native_jordan_eq_zero_of_idempotents_sum
    (x y z : Glennie.Albert)
    (hx : Glennie.jordan x x = x) (hy : Glennie.jordan y y = y)
    (hz : Glennie.jordan z z = z) (hsum : x + y + z = 1) :
    Glennie.jordan x y = 0 := by
  have hcomp : z = 1 - x - y := by
    calc
      z = (x + y + z) - x - y := by module
      _ = 1 - x - y := by rw [hsum]
  have h := native_jordan_complement_residual x y
  rw [← hcomp, hx, hy, hz] at h
  have hzero : (2 : ℝ) • Glennie.jordan x y = 0 := by simpa using h
  have hhalf := congrArg (fun a : Glennie.Albert => (1 / 2 : ℝ) • a) hzero
  norm_num [smul_smul] at hhalf
  exact hhalf

private theorem native_frame_of_trace_idempotent_sum
    (p : Fin 3 → Glennie.Albert)
    (htrace : ∀ i, Glennie.trace (p i) = 1)
    (hidem : ∀ i, Glennie.jordan (p i) (p i) = p i)
    (hsum : p 0 + p 1 + p 2 = 1) : Glennie.Frame p := by
  have h01 := native_jordan_eq_zero_of_idempotents_sum
    (p 0) (p 1) (p 2) (hidem 0) (hidem 1) (hidem 2) hsum
  have h02 := native_jordan_eq_zero_of_idempotents_sum
    (p 0) (p 2) (p 1) (hidem 0) (hidem 2) (hidem 1)
    (by simpa only [add_assoc, add_left_comm, add_comm] using hsum)
  have h12 := native_jordan_eq_zero_of_idempotents_sum
    (p 1) (p 2) (p 0) (hidem 1) (hidem 2) (hidem 0)
    (by simpa only [add_assoc, add_left_comm, add_comm] using hsum)
  refine ⟨htrace, hidem, ?_, hsum⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · exact h01
  · exact h02
  · change Glennie.jordan (p 1) (p 0) = 0
    rw [Glennie.jordan_comm (p 1) (p 0)]
    exact h01
  · exact False.elim (hij rfl)
  · exact h12
  · change Glennie.jordan (p 2) (p 0) = 0
    rw [Glennie.jordan_comm (p 2) (p 0)]
    exact h02
  · change Glennie.jordan (p 2) (p 1) = 0
    rw [Glennie.jordan_comm (p 2) (p 1)]
    exact h12
  · exact False.elim (hij rfl)

/-- Both ordered central triples are actual native trace-one frames when
the input satisfies exactly the explicit special-unitary equations. -/
theorem native_central_triples_are_frames (U : TitsComplexMatrix)
    (hU : U * U.conjTranspose = (1 : TitsComplexMatrix) ∧ U.det = 1) :
    Glennie.Frame (nativeCentralTriple U) ∧
      Glennie.Frame (nativeReverseCentralTriple U) := by
  have homega := specialUnitary_conditions_smul U omega hU
    omega_mul_star_eq_one omega_cube
  have hsq := specialUnitary_conditions_smul U (omega ^ 2) hU
    omega_sq_mul_star_eq_one omega_sq_cube
  have htrace (V : TitsComplexMatrix) := nativeComplementaryPoint_trace V
  have hidem : ∀ V : TitsComplexMatrix,
      V * V.conjTranspose = (1 : TitsComplexMatrix) ∧ V.det = 1 →
        Glennie.jordan (nativeComplementaryPoint V) (nativeComplementaryPoint V) =
          nativeComplementaryPoint V := fun V h =>
    (nativeComplementaryPoint_idempotent_iff V).mpr h
  constructor
  · apply native_frame_of_trace_idempotent_sum
    · intro i
      fin_cases i <;> exact htrace _
    · intro i
      fin_cases i
      · exact hidem U hU
      · exact hidem (omega • U) homega
      · exact hidem ((omega ^ 2) • U) hsq
    · exact nativeCentralTriple_sum U
  · apply native_frame_of_trace_idempotent_sum
    · intro i
      fin_cases i <;> exact htrace _
    · intro i
      fin_cases i
      · exact hidem U hU
      · exact hidem ((omega ^ 2) • U) hsq
      · exact hidem (omega • U) homega
    · change nativeComplementaryPoint U +
        nativeComplementaryPoint ((omega ^ 2) • U) +
          nativeComplementaryPoint (omega • U) = 1
      have hsum := nativeCentralTriple_sum U
      change nativeComplementaryPoint U + nativeComplementaryPoint (omega • U) +
        nativeComplementaryPoint ((omega ^ 2) • U) = 1 at hsum
      simpa only [add_assoc, add_left_comm, add_comm] using hsum

/-- The actual overlap of two constructed points, with the adjoint on V.
This identity holds before any unitarity or idempotency condition. -/
theorem nativeComplementaryPoint_overlap (U V : TitsComplexMatrix) :
    Glennie.trace (Glennie.jordan (nativeComplementaryPoint U)
      (nativeComplementaryPoint V)) =
        1 / 3 + (2 / 9 : ℝ) * (U * V.conjTranspose).trace.re := by
  rw [native_trace_jordan_eq_scaled_overlap_of_visible_thirds _ _
    (nativeComplementaryPoint_visible U) (nativeComplementaryPoint_visible V),
    nativeComplementaryPoint_scaled_hidden, nativeComplementaryPoint_scaled_hidden]

/-- A single unbiased native overlap is precisely the real trace-zero
condition. Complex trace zero is a stronger cross-frame conclusion. -/
theorem nativeComplementaryPoint_overlap_eq_third_iff (U V : TitsComplexMatrix) :
    Glennie.trace (Glennie.jordan (nativeComplementaryPoint U)
      (nativeComplementaryPoint V)) = (1 / 3 : ℝ) ↔
        (U * V.conjTranspose).trace.re = 0 := by
  rw [nativeComplementaryPoint_overlap]
  constructor <;> intro h <;> linarith

end CompactAlbert



#check @CompactAlbert.nativeComplementaryPoint_pair
#check @CompactAlbert.nativeComplementaryPoint_visible
#check @CompactAlbert.nativeComplementaryPoint_scaled_hidden
#check @CompactAlbert.nativeComplementaryPoint_trace
#check @CompactAlbert.nativeComplementaryPoint_literal_readouts
#check @CompactAlbert.nativeComplementaryPoint_idempotent_iff
#check @CompactAlbert.nativeCentralTriple_sum
#check @CompactAlbert.native_jordan_complement_residual
#check @CompactAlbert.native_jordan_eq_zero_of_idempotents_sum
#check @CompactAlbert.native_central_triples_are_frames
#check @CompactAlbert.nativeComplementaryPoint_overlap
#check @CompactAlbert.nativeComplementaryPoint_overlap_eq_third_iff

#print axioms CompactAlbert.nativeComplementaryPoint_pair
#print axioms CompactAlbert.nativeComplementaryPoint_visible
#print axioms CompactAlbert.nativeComplementaryPoint_scaled_hidden
#print axioms CompactAlbert.nativeComplementaryPoint_trace
#print axioms CompactAlbert.nativeComplementaryPoint_literal_readouts
#print axioms CompactAlbert.nativeComplementaryPoint_idempotent_iff
#print axioms CompactAlbert.nativeCentralTriple_sum
#print axioms CompactAlbert.native_jordan_complement_residual
#print axioms CompactAlbert.native_jordan_eq_zero_of_idempotents_sum
#print axioms CompactAlbert.native_central_triples_are_frames
#print axioms CompactAlbert.nativeComplementaryPoint_overlap
#print axioms CompactAlbert.nativeComplementaryPoint_overlap_eq_third_iff

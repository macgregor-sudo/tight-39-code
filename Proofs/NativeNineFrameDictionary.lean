module

public import NativeComplementaryDictionary
public import NativeRightSU3Action
public import NativePolynomialEvaluationStaged

/-
# Nine actual complementary frames and their special-unitary matrix array

This first-party composition calls the passed actual native ordered-frame
dictionary and the either-order Hilbert–Schmidt overlap equivalence. The
point, frame, trace and matrix product facts come from those declarations;
no octonion or Albert foundation is reproved or copied here.

For each ordered frame its central or reverse order remains explicit. The
matrix array has nine determinant-one unitaries with pairwise trace-zero
Hilbert–Schmidt products. This is classical unitary-error-basis terminology,
not a new classification result. The existing project's IsUnitaryErrorBasis
identifier uses ZMod labels/indices and a left Gram convention: its exact
index/Gram adapter, the complete thirteen-frame object and original residual
binding remain separate. No gauge quotient or exhaustive-fixer premise occurs.

The imported compact native source is compact-albert-recognition,
https://github.com/macgregor-sudo/compact-albert-recognition,
commit 40d3b344180d9ddb78aaa2876873377c1e631515. Its Apache-2.0 LICENSE and
notice are retained in LICENSES/Native-Albert-Apache-2.0.txt and
LICENSES/Native-Albert-THIRD-PARTY-NOTICES.md (public scope/locator clarifications).
All upstream and adapted-code notices remain in the imported modules. This
file copies no proof body and assigns no release license to new contributions.
Thanks to the native project, Lean and mathlib contributors for these results.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/


@[expose] public section
noncomputable section

namespace CompactAlbert

open UnitaryErrorBases.ComplexQuartet

/-- Nine actual ordered frames with the original twelve quartet readouts and
mutual complementarity are exactly the two central orders of a trace-orthogonal
array of determinant-one unitary matrices. Each order and representative is
retained; no quotient, relabelling or bundled UEB identification is assumed. -/
theorem native_nine_complementary_frames_iff_exists_unitary_array
    (p : Fin 9 → Fin 3 → Glennie.Albert) :
    ((∀ r : Fin 9, Glennie.Frame (p r)) ∧
      (∀ (r : Fin 9) (i t : Fin 3), Glennie.trace
        (Glennie.jordan (p r i) (literalNativeCoordinatePoint t)) = (1 / 3 : ℝ)) ∧
      (∀ (r : Fin 9) (i : Fin 3) (s t : PhaseIndex), Glennie.trace
        (Glennie.jordan (p r i) (literalNativePhasePoint s t)) = (1 / 3 : ℝ)) ∧
      (∀ r s : Fin 9, r ≠ s → ∀ i j : Fin 3, Glennie.trace
        (Glennie.jordan (p r i) (p s j)) = (1 / 3 : ℝ))) ↔
      ∃ U : Fin 9 → TitsComplexMatrix,
        (∀ r : Fin 9, U r * (U r).conjTranspose = (1 : TitsComplexMatrix) ∧
          (U r).det = 1) ∧
        (∀ r s : Fin 9, r ≠ s → ((U r).conjTranspose * U s).trace = 0) ∧
        (∀ r : Fin 9,
          p r = nativeCentralTriple (U r) ∨ p r = nativeReverseCentralTriple (U r)) := by
  constructor
  · rintro ⟨hframes, hcoordinate, hphase, hoverlap⟩
    have hex (r : Fin 9) :
        ∃ U : TitsComplexMatrix,
          (U * U.conjTranspose = (1 : TitsComplexMatrix) ∧ U.det = 1) ∧
            (p r = nativeCentralTriple U ∨ p r = nativeReverseCentralTriple U) :=
      (native_complementary_frame_iff_exists_central_order (p r)).mp
        ⟨hframes r, hcoordinate r, hphase r⟩
    let U : Fin 9 → TitsComplexMatrix := fun r => Classical.choose (hex r)
    have hunitary (r : Fin 9) :
        U r * (U r).conjTranspose = (1 : TitsComplexMatrix) ∧ (U r).det = 1 :=
      (Classical.choose_spec (hex r)).1
    have horder (r : Fin 9) :
        p r = nativeCentralTriple (U r) ∨ p r = nativeReverseCentralTriple (U r) :=
      (Classical.choose_spec (hex r)).2
    refine ⟨U, hunitary, ?_, horder⟩
    intro r s hrs
    exact (native_ordered_central_triples_overlap_iff_hilbertSchmidt
      (U r) (U s) (p r) (p s) (horder r) (horder s)).mp (hoverlap r s hrs)
  · rintro ⟨U, hunitary, horthogonal, horder⟩
    have hframe (r : Fin 9) :=
      (native_complementary_frame_iff_exists_central_order (p r)).mpr
        ⟨U r, hunitary r, horder r⟩
    refine ⟨(fun r => (hframe r).1), (fun r => (hframe r).2.1),
      (fun r => (hframe r).2.2), ?_⟩
    intro r s hrs
    exact (native_ordered_central_triples_overlap_iff_hilbertSchmidt
      (U r) (U s) (p r) (p s) (horder r) (horder s)).mpr (horthogonal r s hrs)

end CompactAlbert

/- The actual nine-frame statement co-imported with both existing branches. -/


#check @CompactAlbert.native_nine_complementary_frames_iff_exists_unitary_array
#print axioms CompactAlbert.native_nine_complementary_frames_iff_exists_unitary_array

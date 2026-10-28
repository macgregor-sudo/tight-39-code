module

public import NativeActualFrameDictionary

@[expose] public section

/-!
# Nine complementary frames at the actual twelve native labels

The finite-array equivalence retains a separate central orientation for each frame.

The previously accepted actual-frame Main has source SHA256
72d51a6ee46e37ad96cd0a221e852a3990b1c71950af53d314da316bfc289335,
canonical ResearchClaim 0f6b2834-7e86-5df1-9fff-b0600f8a280a revision1.
It remains unchanged. This file adds one finite-array composition of its
actual-frame equivalence and the accepted either-order overlap equivalence.
Classical choice selects one representative for each frame; uniqueness is
neither needed nor assumed. Each frame retains its own central orientation.

The accepted literal NativeNineFrameDictionary source, SHA256
bee7556210d92fd45373a78296e5daa2eb4ffc2a672b931584653a38d4605aeb,
was checked for matching conventions. It is not an additional import here.
This is first-party mathematical composition, not copied upstream proof code.
Imported owners retain all provenance, license and attribution notices.
Thanks to the native-model, CKM, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018

No original residual solution is silently treated as a frame. No bundled UEB,
uniqueness, gauge quotient, global embedding, phase extension, chart, real
exhaustion or code-bound equality theorem is asserted.
-/

noncomputable section

namespace CompactAlbert.ActualNineFrameDictionary

open ActualFrameDictionary
open QuadraticCertificate.ExactCKMConfiguration

/-- Nine ordered Albert frames, each unbiased to the actual first twelve
native points and mutually unbiased across distinct frame labels, are exactly
the central triples of nine pairwise complex-trace-orthogonal special-unitary
matrices, with an independent forward-or-reverse order for every frame. -/
theorem actual_nine_frames_iff_trace_orthogonal_array
    (p : Fin 9 → Fin 3 → Glennie.Albert) :
    ((∀ r : Fin 9, Glennie.Frame (p r) ∧
        ∀ k : Fin 3, ∀ i : Fin 39, i.val < 12 →
          Glennie.trace (Glennie.jordan (p r k) (nativePoint i)) = (1 / 3 : ℝ)) ∧
      (∀ r s : Fin 9, r ≠ s → ∀ k l : Fin 3,
        Glennie.trace (Glennie.jordan (p r k) (p s l)) = (1 / 3 : ℝ))) ↔
      ∃ U : Fin 9 → TitsComplexMatrix,
        (∀ r : Fin 9,
          U r * (U r).conjTranspose = (1 : TitsComplexMatrix) ∧ (U r).det = 1) ∧
        (∀ r : Fin 9,
          p r = nativeCentralTriple (U r) ∨ p r = nativeReverseCentralTriple (U r)) ∧
        (∀ r s : Fin 9, r ≠ s → ((U r).conjTranspose * U s).trace = 0) := by
  constructor
  · rintro ⟨hframes, hcross⟩
    have hex (r : Fin 9) :
        ∃ V : TitsComplexMatrix,
          (V * V.conjTranspose = (1 : TitsComplexMatrix) ∧ V.det = 1) ∧
            (p r = nativeCentralTriple V ∨ p r = nativeReverseCentralTriple V) :=
      (actual_frame_iff_specialUnitary_central_order (p r)).mp (hframes r)
    let U : Fin 9 → TitsComplexMatrix := fun r => Classical.choose (hex r)
    have hU (r : Fin 9) :
        U r * (U r).conjTranspose = (1 : TitsComplexMatrix) ∧ (U r).det = 1 :=
      (Classical.choose_spec (hex r)).1
    have horder (r : Fin 9) :
        p r = nativeCentralTriple (U r) ∨ p r = nativeReverseCentralTriple (U r) :=
      (Classical.choose_spec (hex r)).2
    refine ⟨U, hU, horder, ?_⟩
    intro r s hrs
    exact (native_ordered_central_triples_overlap_iff_hilbertSchmidt
      (U r) (U s) (p r) (p s) (horder r) (horder s)).mp (hcross r s hrs)
  · rintro ⟨U, hU, horder, horthogonal⟩
    refine ⟨?_, ?_⟩
    · intro r
      exact (actual_frame_iff_specialUnitary_central_order (p r)).mpr
        ⟨U r, hU r, horder r⟩
    · intro r s hrs
      exact (native_ordered_central_triples_overlap_iff_hilbertSchmidt
        (U r) (U s) (p r) (p s) (horder r) (horder s)).mpr (horthogonal r s hrs)

end CompactAlbert.ActualNineFrameDictionary

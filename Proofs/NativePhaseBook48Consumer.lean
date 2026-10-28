module

public import NativePhaseBook48
public import BookHilbertCharZero
public import ChainMidAssembly

@[expose] public section

/-! One importing milestone consumer: the actual phase quadratic relations have
the Book Hilbert bound. This does not identify analytic components or ordinary
multiplicity, or any additional geometric conclusion. -/

noncomputable section
namespace Option2.NativeStress.PhaseBook48ConsumerA6
open MvPolynomial Module PolynomialJets SliceLemmas
open PhasePivotA6 PhasePivotLocusA6 PhaseHilbertA6 PhaseBook48A6
open CKM.NativeFirstOrder CKM.NativeFourFamily BookHT
open scoped BigOperators

set_option maxHeartbeats 600000 in
/-- Exact native all-degree relation bound on the good-phase pivot locus.
The 48 stress witnesses, coordinate change and Book bound are supplied by proofs,
not retained as assumptions of this endpoint. -/
theorem native_phase_cumulative_relations (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) :
    ∃ w : Fin 48 → Fin 2184 → ℂ,
      (∀ s j, ∑ r, w s r * nativeJ u.1 r j = 0) ∧
      ∀ N, HilbertFunctions.JetBounds.cumulative
        (fun d => finrank ℂ (equationCutPiece (nativeRows u.1) id w [] d)) N ≤
        4 * (N + 62).choose 62 + 1540 * (N + 61).choose 61 := by
  obtain ⟨B,piv,M,N,w,hB,hJB,hMN,_hNM,hw,hspan⟩ := native_book48_D6 u hgood hpivot
  have hvanish : cutLinearSpace (nativeRows u.1) id [] ≤ linearAnnihilator B :=
    ChainMid.cutLinearSpace_nil_le_linearAnnihilator (nativeRows u.1) id B hJB
  obtain ⟨_,_,_,_,_,_,hdim,_⟩ := PhaseKernelA6.native_linear_slice_on_locus u hpivot
  have hhom : ∀ k, (Dictionary.quadric k).IsHomogeneous 2 := by
    intro k
    rw [← BookHilbertCharZero.bookQuadrics_complex]
    exact (BookHilbertCharZero.bookIntegerQuadric_homogeneous k).map (Int.castRingHom ℂ)
  refine ⟨w,hw,?_⟩
  intro n
  exact ChainMid.cumulative_equationCutPiece_le hB (nativeRows u.1) id w
    hvanish hdim M N hMN Dictionary.quadric hhom hspan
    BookHilbertCharZero.dictionary_hilbert_bound n

#print axioms Option2.NativeStress.PhaseBook48ConsumerA6.native_phase_cumulative_relations
end Option2.NativeStress.PhaseBook48ConsumerA6

module

public import ThreeCycleNormalizedContinuity
public import ThreeCycleNormalizedFamilyFibres
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
Compactness and the exact central quotient of the accepted normalized family.
This module does not identify the quotient with a
separately defined standard PSU(3) times T², prove an immersion, transport the
topology to native frames, or claim exhaustion. All labels remain clock-first.

First-party proofs composing the retained construction and pinned mathlib APIs.
No upstream proof body is copied. In particular compactness uses closed subsets
of products of compact complex closed balls; embedding uses the standard
compact-to-Hausdorff theorem Continuous.isClosedEmbedding in mathlib's
Topology/Separation/Hausdorff.lean. Imported sources retain their notices.
Thanks to the Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, 1676. https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
namespace UnitaryErrorBases.ThreeCycleNormalized

private theorem norm_le_one_of_normSq_le_one (z : ℂ)
    (h : Complex.normSq z ≤ 1) : ‖z‖ ≤ 1 := by
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg z]

private theorem entry_norm_le_one (Q : Mat) (hQ : IsSpecialUnitary Q)
    (i j : Index) : ‖Q i j‖ ≤ 1 := by
  have hcolumn : ∑ k, Complex.normSq (Q k j) = 1 := by
    have h := congrArg (fun A : Mat => (A j j).re) hQ.1
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.mul_re, Complex.normSq_apply] using h
  apply norm_le_one_of_normSq_le_one
  rw [← hcolumn]
  exact Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (Q k j))
    (Finset.mem_univ i)

/-- Compactness of the literal matrix equations used by the construction. -/
theorem isCompact_specialUnitary : IsCompact {Q : Mat | IsSpecialUnitary Q} := by
  have hclosed : IsClosed {Q : Mat | IsSpecialUnitary Q} := by
    unfold IsSpecialUnitary
    exact (isClosed_eq (continuous_id.matrix_conjTranspose.mul continuous_id)
      continuous_const).inter (isClosed_eq continuous_id.matrix_det continuous_const)
  apply (isCompact_closedBall (0 : ℂ) 1).matrix.of_isClosed_subset hclosed
  intro Q hQ
  rw [Set.mem_matrix]
  intro i j
  simpa [Metric.mem_closedBall, dist_zero_right] using entry_norm_le_one Q hQ i j

/-- Compactness of the original unit-phase, product-one subtype. -/
theorem isCompact_phaseTriples :
    IsCompact {d : Index → ℂ | (∀ j, Complex.normSq (d j) = 1) ∧ ∏ j, d j = 1} := by
  have hclosed : IsClosed
      {d : Index → ℂ | (∀ j, Complex.normSq (d j) = 1) ∧ ∏ j, d j = 1} := by
    apply IsClosed.inter
    · have hset : {d : Index → ℂ | ∀ j, Complex.normSq (d j) = 1} =
          ⋂ j : Index, {d : Index → ℂ | Complex.normSq (d j) = 1} := by
        ext d
        simp
      rw [show (fun d : Index → ℂ => ∀ j, Complex.normSq (d j) = 1) =
          {d : Index → ℂ | ∀ j, Complex.normSq (d j) = 1} from rfl, hset]
      exact isClosed_iInter fun j =>
        isClosed_eq (Complex.continuous_normSq.comp (continuous_apply j)) continuous_const
    · exact isClosed_eq (continuous_finsetProd _ fun j _ => continuous_apply j) continuous_const
  apply (isCompact_pi_infinite fun _ : Index => isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset hclosed
  intro d hd j
  simpa [Metric.mem_closedBall, dist_zero_right] using
    norm_le_one_of_normSq_le_one (d j) (le_of_eq (hd.1 j))

instance compactSpace_specialUnitary : CompactSpace {Q : Mat // IsSpecialUnitary Q} :=
  isCompact_iff_compactSpace.mp isCompact_specialUnitary

instance compactSpace_phaseTriple : CompactSpace PhaseTriple :=
  isCompact_iff_compactSpace.mp isCompact_phaseTriples

/-- The unchanged actual constrained parameters before central descent. -/
abbrev Parameters := {Q : Mat // IsSpecialUnitary Q} × PhaseTriple

/-- Compactness is proved for the actual parameter carrier, with no premise. -/
theorem compactSpace_parameters : CompactSpace Parameters := inferInstance

/-- Only the conjugating matrix is quotiented; the entire phase triple is fixed. -/
def centralRelation (x y : Parameters) : Prop :=
  x.2 = y.2 ∧ ∃ c : ℂ, c ^ 3 = 1 ∧ y.1.val = c • x.1.val

theorem family_eq_iff_central (x y : Parameters) :
    normalizedFamily x.1.val x.2 = normalizedFamily y.1.val y.2 ↔ centralRelation x y :=
  normalizedFamily_eq_iff _ _ _ _ x.1.property y.1.property

/-- The explicit central relation is an equivalence, by the accepted exact fibres. -/
def centralSetoid : Setoid Parameters where
  r := centralRelation
  iseqv := {
    refl := fun x => (family_eq_iff_central x x).mp rfl
    symm := fun h => (family_eq_iff_central _ _).mp ((family_eq_iff_central _ _).mpr h).symm
    trans := fun hxy hyz => (family_eq_iff_central _ _).mp
      (((family_eq_iff_central _ _).mpr hxy).trans ((family_eq_iff_central _ _).mpr hyz)) }

/-- Concrete quotient by the displayed central relation, without a group-name alias. -/
abbrev CentralQuotient := Quotient centralSetoid

/-- The actual labelled normalized family descended through its exact fibres. -/
def descendedNormalizedFamily : CentralQuotient → Family :=
  Quotient.lift (fun x : Parameters => normalizedFamily x.1.val x.2)
    (fun x y h => (family_eq_iff_central x y).mpr h)

theorem descendedNormalizedFamily_mk (x : Parameters) :
    descendedNormalizedFamily (Quotient.mk centralSetoid x) =
      normalizedFamily x.1.val x.2 := rfl

theorem continuous_descendedNormalizedFamily : Continuous descendedNormalizedFamily := by
  apply Continuous.quotient_lift
  exact continuous_normalizedFamily.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem injective_descendedNormalizedFamily : Function.Injective descendedNormalizedFamily := by
  intro x y
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      intro h
      exact Quotient.sound ((family_eq_iff_central x y).mp h)

/-- Topological closed embedding onto the image of the exact central quotient.
This does not assert an immersion or standard PSU(3)×T² identification. -/
theorem isClosedEmbedding_descendedNormalizedFamily :
    Topology.IsClosedEmbedding descendedNormalizedFamily :=
  continuous_descendedNormalizedFamily.isClosedEmbedding injective_descendedNormalizedFamily

end UnitaryErrorBases.ThreeCycleNormalized

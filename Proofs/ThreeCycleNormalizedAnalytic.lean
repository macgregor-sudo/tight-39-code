module

public import NativeNormalizedProjectiveFamily
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section

/-!
Real-analytic ambient extension of the exact normalized monomial construction.
Only the PhaseTriple subtype restriction is removed from the old formula;
the equality on every actual PhaseTriple is definitional. Complex conjugation
is treated as real-linear, so no holomorphic assertion is made.
The native result uses the same fixed index maps, central constructors and all
upper coordinates. Neither arbitrary matrices nor arbitrary phases are asserted
to form valid states. Quotient analytic charts and immersion remain separate.
First-party composition of existing definitions and pinned mathlib analytic
APIs; no upstream proof copied. Imported owners retain their attribution.
Thanks to the contributors. “If I have seen further it is by standing on the
sholders of Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
namespace UnitaryErrorBases.ThreeCycleNormalized

open scoped BigOperators Matrix.Norms.Elementwise

/-- The unchanged normalized formula with its phase subtype restriction removed. -/
def normalizedFamilyExtension (qd : Mat × (Index → ℂ)) : Family := fun p =>
  qd.1 * (shift ^ p.2.val *
    Matrix.diagonal (fun j => if p.2 = 2 then qd.2 j else 1) * clock ^ p.1.val) *
    qd.1.conjTranspose

/-- Exact agreement for every original PhaseTriple, without a condition on Q. -/
theorem normalizedFamilyExtension_eq (Q : Mat) (d : PhaseTriple) :
    normalizedFamilyExtension (Q, d.val) = normalizedFamily Q d := rfl

/-- Global real analyticity in all ambient matrix and phase entries. -/
theorem analyticOnNhd_normalizedFamilyExtension :
    AnalyticOnNhd ℝ normalizedFamilyExtension Set.univ := by
  intro x _
  have hfst : AnalyticAt ℝ (fun y : Mat × (Index → ℂ) => y.1) x := analyticAt_fst
  have hsnd : AnalyticAt ℝ (fun y : Mat × (Index → ℂ) => y.2) x := analyticAt_snd
  have hmul {f g : (Mat × (Index → ℂ)) → Mat}
      (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x) :
      AnalyticAt ℝ (fun y => f y * g y) x := by
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.pi
    intro j
    simp only [Matrix.mul_apply]
    exact Finset.univ.analyticAt_sum fun k _ =>
      ((analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hf i)) k).mul
        ((analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hg k)) j)
  have hstar : AnalyticAt ℝ (fun y : Mat × (Index → ℂ) => y.1.conjTranspose) x := by
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.pi
    intro j
    change AnalyticAt ℝ (fun y : Mat × (Index → ℂ) => Complex.conjCLE (y.1 j i)) x
    exact (Complex.conjCLE.toContinuousLinearMap.analyticAt _).comp
      ((analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hfst j)) i)
  apply AnalyticAt.pi
  intro p
  have hdiag : AnalyticAt ℝ
      (fun y : Mat × (Index → ℂ) =>
        Matrix.diagonal (fun j => if p.2 = 2 then y.2 j else (1 : ℂ))) x := by
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.pi
    intro j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq]
      by_cases hp : p.2 = 2
      · simp only [ite_eq_left hp]
        exact (analyticAt_pi_iff.mp hsnd) i
      · simp only [ite_eq_right hp]
        exact analyticAt_const
    · simp only [Matrix.diagonal_apply_ne _ hij]
      exact analyticAt_const
  exact hmul (hmul hfst (hmul (hmul analyticAt_const hdiag) analyticAt_const)) hstar

end UnitaryErrorBases.ThreeCycleNormalized

namespace CompactAlbert.NativeCentralArrayTopology

open NativePolynomial UnitaryErrorBases.ThreeCycleFourier
open scoped Matrix.Norms.Elementwise

private theorem analyticAt_point_coordinates (U : TitsComplexMatrix) :
    AnalyticAt ℝ (fun V : TitsComplexMatrix => upperCoordinates (nativeComplementaryPoint V)) U := by
  let decode : TitsCoordinates →L[ℝ] (Fin 27 → ℝ) :=
    (upperCoordinateEquiv.toLinearMap.comp
      compactTitsCoordinateEquiv.symm.toLinearMap).toContinuousLinearMap
  change AnalyticAt ℝ (fun V : TitsComplexMatrix =>
    decode ((fun _ => (1 / 3 : ℝ)), 0, (1 / 3 : ℂ) • V)) U
  have hscale : AnalyticAt ℝ (fun V : TitsComplexMatrix => (1/3 : ℂ) • V) U :=
    (analyticAt_const (𝕜 := ℝ) (v := (1/3 : ℂ))).smul analyticAt_id
  exact (decode.analyticAt _).comp
    (analyticAt_const.prod (analyticAt_const.prod hscale))

/-- Analyticity of the actual central constructor in all native upper coordinates. -/
theorem analyticOnNhd_centralTripleCoordinates (reverse : Bool) :
    AnalyticOnNhd ℝ (centralTripleCoordinates reverse) Set.univ := by
  intro U _
  apply AnalyticAt.pi
  intro k
  have hphase (c : ℂ) : AnalyticAt ℝ (fun V : TitsComplexMatrix =>
      upperCoordinates (nativeComplementaryPoint (c • V))) U := by
    have hscale : AnalyticAt ℝ (fun V : TitsComplexMatrix => c • V) U :=
      (analyticAt_const (𝕜 := ℝ) (v := c)).smul analyticAt_id
    exact (analyticAt_point_coordinates _).comp hscale
  cases reverse
  · fin_cases k
    · exact analyticAt_point_coordinates U
    · exact hphase omega
    · exact hphase (omega ^ 2)
  · fin_cases k
    · exact analyticAt_point_coordinates U
    · exact hphase (omega ^ 2)
    · exact hphase omega

/-- Independent fixed orientations retain the exact existing finite product map. -/
theorem analyticOnNhd_centralArrayCoordinates (reverse : Fin 9 → Bool) :
    AnalyticOnNhd ℝ (centralArrayCoordinates reverse) Set.univ := by
  intro U _
  apply AnalyticAt.pi
  intro r
  exact ((analyticOnNhd_centralTripleCoordinates (reverse r)) (U r) (Set.mem_univ _)).comp
    (f := fun V : Fin 9 → TitsComplexMatrix => V r)
    ((ContinuousLinearMap.proj (R := ℝ) r).analyticAt U)

end CompactAlbert.NativeCentralArrayTopology

namespace CompactAlbert

open scoped Matrix.Norms.Elementwise
open UnitaryErrorBases UnitaryErrorBases.ThreeCycleNormalized
open NativeCentralArrayTopology

/-- The same fixed reindex and native constructors applied to the ambient extension. -/
def nativeNormalizedFamilyExtension (qd : Mat × (Index → ℂ)) :
    Fin 9 → Fin 3 → Fin 27 → ℝ :=
  centralArrayCoordinates (fun _ => false)
    (nativeArrayOfChallengeFamily (normalizedFamilyExtension qd))

/-- Every actual phase triple gives the same previously constructed native array. -/
theorem nativeNormalizedFamilyExtension_eq (Q : Mat) (d : PhaseTriple) :
    nativeNormalizedFamilyExtension (Q, d.val) =
      centralArrayCoordinates (fun _ => false) (nativeThreeCycleArray Q d) := rfl

/-- Exact representative binding to the frozen standard-quotient native family. -/
theorem nativeNormalizedFamilyExtension_mk (Q : StandardSpecialUnitary) (z : Circle × Circle) :
    nativeNormalizedFamilyExtension (Q.val, (phaseOfCircles z).val) =
      nativeNormalizedProjectiveFamily (QuotientGroup.mk Q, z) := rfl

/-- Global real analyticity of the exact native ambient representative extension. -/
theorem analyticOnNhd_nativeNormalizedFamilyExtension :
    AnalyticOnNhd ℝ nativeNormalizedFamilyExtension Set.univ := by
  intro x _
  have hn : AnalyticAt ℝ
      (fun y : Mat × (Index → ℂ) => nativeArrayOfChallengeFamily (normalizedFamilyExtension y)) x := by
    apply AnalyticAt.pi
    intro r
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.pi
    intro j
    change AnalyticAt ℝ (fun y : Mat × (Index → ℂ) =>
      normalizedFamilyExtension y (challengeLabelEquiv.symm r)
        (challengeMatrixIndexEquiv i) (challengeMatrixIndexEquiv j)) x
    exact (analyticAt_pi_iff.mp (analyticAt_pi_iff.mp
      (analyticAt_pi_iff.mp (analyticOnNhd_normalizedFamilyExtension x (Set.mem_univ _))
        (challengeLabelEquiv.symm r)) (challengeMatrixIndexEquiv i))) (challengeMatrixIndexEquiv j)
  exact ((analyticOnNhd_centralArrayCoordinates (fun _ => false)) _ (Set.mem_univ _)).comp hn

end CompactAlbert

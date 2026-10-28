module

public import ThreeCycleNormalizedProjectiveUnitary
public import UEBDeterminantDerivative
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section

/-!
# Literal local defining equations for the actual special-unitary matrices

On det(Q).re > 0, the equations Q†Q = I and
Im(det Q) = 0 are exactly membership in mathlib's existing special-unitary
group on the original cyclic Index. No manifold or rank assumption is added.
First-party composition of existing determinant, topology and analytic APIs;
no upstream proof body or generated private name is used. Imported owners
retain their notices and provenance. Thanks to the Lean, mathlib and project
contributors. “If I have seen further it is by standing on the sholders of
Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise Topology

namespace UnitaryErrorBases.ThreeCycleNormalized

/-- The explicit open region that excludes the negative real determinant root. -/
def specialUnitaryConstraintDomain : Set Mat := {Q | 0 < Q.det.re}

theorem isOpen_specialUnitaryConstraintDomain : IsOpen specialUnitaryConstraintDomain :=
  isOpen_lt continuous_const (Complex.continuous_re.comp continuous_id.matrix_det)

theorem one_mem_specialUnitaryConstraintDomain : (1 : Mat) ∈ specialUnitaryConstraintDomain := by
  simp [specialUnitaryConstraintDomain]

/-- Unitarity alone forces the determinant onto the unit circle. -/
theorem normSq_det_of_conjTranspose_mul_eq_one (Q : Mat)
    (hQ : Q.conjTranspose * Q = 1) : Complex.normSq Q.det = 1 := by
  have hd : star Q.det * Q.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, hQ, Matrix.det_one]
  apply Complex.ofReal_injective
  change (Complex.normSq Q.det : ℂ) = 1
  rw [Complex.normSq_eq_conj_mul_self]
  exact hd

/-- Positivity selects determinant +1 from the two real unit-circle roots. -/
theorem mem_specialUnitary_iff_constraints_of_pos_det_re (Q : Mat)
    (hpos : 0 < Q.det.re) :
    Q ∈ Matrix.specialUnitaryGroup Index ℂ ↔
      Q.conjTranspose * Q = 1 ∧ Q.det.im = 0 := by
  rw [← isSpecialUnitary_iff_mem_standard]
  constructor
  · rintro ⟨hQ, hdet⟩
    exact ⟨hQ, by rw [hdet]; rfl⟩
  · rintro ⟨hQ, him⟩
    refine ⟨hQ, ?_⟩
    have hn := normSq_det_of_conjTranspose_mul_eq_one Q hQ
    rw [Complex.normSq_apply, him] at hn
    have hre : Q.det.re = 1 := by nlinarith
    apply Complex.ext
    · simpa using hre
    · simpa using him

/-- The literal matrix/real residual; no projected or renamed equations. -/
def specialUnitaryLocalResidual (Q : Mat) : Mat × ℝ :=
  (Q.conjTranspose * Q - 1, Q.det.im)

theorem mem_specialUnitary_iff_residual_eq_zero (Q : Mat)
    (hQ : Q ∈ specialUnitaryConstraintDomain) :
    Q ∈ Matrix.specialUnitaryGroup Index ℂ ↔ specialUnitaryLocalResidual Q = 0 := by
  rw [mem_specialUnitary_iff_constraints_of_pos_det_re Q hQ]
  simp [specialUnitaryLocalResidual, Prod.ext_iff, sub_eq_zero]

/-- Actual neighborhood equivalence at the identity in the unchanged matrix topology. -/
theorem eventually_mem_specialUnitary_iff_residual_eq_zero :
    ∀ᶠ Q : Mat in 𝓝 1,
      Q ∈ Matrix.specialUnitaryGroup Index ℂ ↔ specialUnitaryLocalResidual Q = 0 := by
  filter_upwards [isOpen_specialUnitaryConstraintDomain.mem_nhds
    one_mem_specialUnitaryConstraintDomain] with Q hQ
  exact mem_specialUnitary_iff_residual_eq_zero Q hQ

/-- The residual has a global real-analytic ambient extension: itself. -/
theorem analyticOnNhd_specialUnitaryLocalResidual :
    AnalyticOnNhd ℝ specialUnitaryLocalResidual Set.univ := by
  intro Q _
  have hid : AnalyticAt ℝ (fun A : Mat => A) Q := analyticAt_id
  have hstar : AnalyticAt ℝ (fun A : Mat => A.conjTranspose) Q := by
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.pi
    intro j
    change AnalyticAt ℝ (fun A : Mat => Complex.conjCLE (A j i)) Q
    exact (Complex.conjCLE.toContinuousLinearMap.analyticAt _).comp
      ((analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hid j)) i)
  have hgram : AnalyticAt ℝ (fun A : Mat => A.conjTranspose * A) Q := by
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.pi
    intro j
    simp only [Matrix.mul_apply]
    exact Finset.univ.analyticAt_sum fun k _ =>
      ((analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hstar i)) k).mul
        ((analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hid k)) j)
  have hdet : AnalyticAt ℝ (fun A : Mat => A.det) Q :=
    ArchitectureUEBDerivative.detMultilinear.analyticAt
  have him : AnalyticAt ℝ (fun A : Mat => A.det.im) Q :=
    (Complex.imCLM.analyticAt _).comp hdet
  exact (hgram.sub analyticAt_const).prod him

end UnitaryErrorBases.ThreeCycleNormalized

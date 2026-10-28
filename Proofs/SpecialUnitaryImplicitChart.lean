module
public import SpecialUnitaryTangentNormalCoordinates
public import SpecialUnitaryLocalConstraints
public import SpecialUnitaryTangentDimension
public import Mathlib.Analysis.Calculus.ImplicitContDiff

@[expose] public section

/-!
# Actual special-unitary local analytic graph at identity

exact native kernel/range and the original Index=ZMod3.
The range-valued residual is proved equal to the literal Gram/determinant
residual; the positive-real determinant branch is used when identifying SU3.
This supplies an analytic local zero-fiber graph and two local inverse laws,
not an installed manifold atlas or a quotient analytic structure.

First-party composition of existing project owners and public mathlib APIs.
The implicit-function theorem is imported from mathlib at commit
065356127b1dc0016f66b7283ce0ce2c4055aa55, Mathlib/Analysis/Calculus/ImplicitContDiff.lean,
ContDiffAt.implicitFunction and its local equation/regularity theorems.
No upstream proof body is copied. Imported owners retain their provenance.
Thanks to the Lean, mathlib and project contributors. “If I have seen further
it is by standing on the sholders of Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/
noncomputable section
open scoped Matrix.Norms.Elementwise Topology ContDiff
open Filter UnitaryErrorBases.ThreeCycleNormalized
namespace UnitaryErrorBases.SpecialUnitaryConstraints

abbrev ConstraintTangent := LinearMap.ker constraintDifferential.toLinearMap
abbrev ConstraintRange := LinearMap.range constraintDifferential.toLinearMap

noncomputable def constraintDifferentialRange : Mat →L[ℝ] ConstraintRange :=
  constraintDifferential.codRestrict _ (fun A => ⟨A, rfl⟩)

noncomputable def localResidualRange (Q : Mat) : ConstraintRange :=
  constraintDifferentialRange (constraintNormalCLM (specialUnitaryLocalResidual Q))

theorem localResidualRange_val (Q : Mat) :
    (localResidualRange Q).val = specialUnitaryLocalResidual Q := by
  change constraintDifferential (constraintNormalCLM (specialUnitaryLocalResidual Q)) = _
  rw [constraintNormalCLM_apply]
  exact constraintDifferential_normal _
    ((Matrix.isHermitian_conjTranspose_mul_self Q).sub Matrix.isHermitian_one) _

def matrixOfConstraintCoordinates (p : ConstraintTangent × ConstraintRange) : Mat :=
  1 + tangentNormalCoordinates.symm p

noncomputable def coordinateResidual (p : ConstraintTangent × ConstraintRange) : ConstraintRange :=
  localResidualRange (matrixOfConstraintCoordinates p)

theorem analyticAt_localResidualRange (Q : Mat) : AnalyticAt ℝ localResidualRange Q :=
  (constraintDifferentialRange.analyticAt _).comp
    ((constraintNormalCLM.analyticAt _).comp
      (analyticOnNhd_specialUnitaryLocalResidual Q (Set.mem_univ Q)))

theorem analyticAt_matrixOfConstraintCoordinates (p : ConstraintTangent × ConstraintRange) :
    AnalyticAt ℝ matrixOfConstraintCoordinates p :=
  analyticAt_const.add (tangentNormalCoordinates.symm.toContinuousLinearMap.analyticAt p)

theorem analyticAt_coordinateResidual (p : ConstraintTangent × ConstraintRange) :
    AnalyticAt ℝ coordinateResidual p :=
  (analyticAt_localResidualRange _).comp (analyticAt_matrixOfConstraintCoordinates p)

@[simp] theorem matrixOfConstraintCoordinates_zero : matrixOfConstraintCoordinates 0 = 1 := by
  simp [matrixOfConstraintCoordinates]

@[simp] theorem coordinateResidual_zero : coordinateResidual 0 = 0 := by
  apply Subtype.ext
  simp only [coordinateResidual, localResidualRange_val, matrixOfConstraintCoordinates_zero]
  simp [specialUnitaryLocalResidual]

theorem specialUnitaryLocalResidual_hasFDerivAt_one :
    HasFDerivAt specialUnitaryLocalResidual constraintDifferential (1 : Mat) := by
  have h := constraintMap_hasFDerivAt_one.sub_const ((1 : Mat), (0 : ℝ))
  have he : specialUnitaryLocalResidual = (fun Q : Mat => constraintMap Q - ((1 : Mat), (0 : ℝ))) := by
    funext Q
    simp [specialUnitaryLocalResidual, constraintMap]
  rw [he]
  exact h

theorem coordinateResidual_hasFDerivAt_zero :
    HasFDerivAt coordinateResidual
      (ContinuousLinearMap.snd ℝ ConstraintTangent ConstraintRange) 0 := by
  have hm : HasFDerivAt matrixOfConstraintCoordinates
      tangentNormalCoordinates.symm.toContinuousLinearMap 0 :=
    (tangentNormalCoordinates.symm.toContinuousLinearMap.hasFDerivAt).const_add 1
  have hr := specialUnitaryLocalResidual_hasFDerivAt_one
  rw [← matrixOfConstraintCoordinates_zero] at hr
  have h := (constraintDifferentialRange.hasFDerivAt.comp 0
    (constraintNormalCLM.hasFDerivAt.comp 0 (hr.comp 0 hm)))
  change HasFDerivAt coordinateResidual _ 0 at h
  have he : constraintDifferentialRange ∘L constraintNormalCLM ∘L constraintDifferential ∘L
      tangentNormalCoordinates.symm.toContinuousLinearMap =
      ContinuousLinearMap.snd ℝ ConstraintTangent ConstraintRange := by
    apply ContinuousLinearMap.ext
    intro p
    apply Subtype.ext
    change constraintDifferential
      (constraintNormalCLM (constraintDifferential (tangentNormalCoordinates.symm p))) = p.2.val
    rw [constraintDifferential_tangentNormalCoordinates_symm,
      constraintNormalCLM_rightInverse]
  exact he ▸ h

theorem coordinateResidual_normal_partial :
    fderiv ℝ coordinateResidual 0 ∘L
      ContinuousLinearMap.inr ℝ ConstraintTangent ConstraintRange =
      ContinuousLinearMap.id ℝ ConstraintRange := by
  rw [coordinateResidual_hasFDerivAt_zero.fderiv]
  rfl

theorem coordinateResidual_normal_invertible :
    (fderiv ℝ coordinateResidual 0 ∘L
      ContinuousLinearMap.inr ℝ ConstraintTangent ConstraintRange).IsInvertible := by
  rw [coordinateResidual_normal_partial]
  exact ⟨ContinuousLinearEquiv.refl ℝ ConstraintRange, rfl⟩

theorem contDiffAt_coordinateResidual_zero : ContDiffAt ℝ ω coordinateResidual 0 :=
  (analyticAt_coordinateResidual 0).contDiffAt

noncomputable def specialUnitaryNormalGraph : ConstraintTangent → ConstraintRange :=
  contDiffAt_coordinateResidual_zero.implicitFunction (by simp)
    coordinateResidual_normal_invertible

@[simp] theorem specialUnitaryNormalGraph_zero : specialUnitaryNormalGraph 0 = 0 :=
  contDiffAt_coordinateResidual_zero.implicitFunction_apply_self (by simp)
    coordinateResidual_normal_invertible

theorem analyticAt_specialUnitaryNormalGraph : AnalyticAt ℝ specialUnitaryNormalGraph 0 :=
  (contDiffAt_coordinateResidual_zero.contDiffAt_implicitFunction (by simp)
    coordinateResidual_normal_invertible).analyticAt

theorem eventually_coordinateResidual_graph :
    ∀ᶠ k : ConstraintTangent in 𝓝 0,
      coordinateResidual (k, specialUnitaryNormalGraph k) = 0 := by
  have h : ∀ᶠ k : ConstraintTangent in 𝓝 0,
      coordinateResidual (k, specialUnitaryNormalGraph k) = coordinateResidual 0 :=
    contDiffAt_coordinateResidual_zero.eventually_apply_implicitFunction (by simp)
      coordinateResidual_normal_invertible
  simpa only [coordinateResidual_zero] using h

theorem eventually_coordinateResidual_eq_zero_iff_graph :
    ∀ᶠ p : ConstraintTangent × ConstraintRange in 𝓝 0,
      coordinateResidual p = 0 ↔ specialUnitaryNormalGraph p.1 = p.2 := by
  have h : ∀ᶠ p : ConstraintTangent × ConstraintRange in 𝓝 0,
      coordinateResidual p = coordinateResidual 0 ↔ specialUnitaryNormalGraph p.1 = p.2 :=
    contDiffAt_coordinateResidual_zero.eventually_apply_eq_iff_implicitFunction (by simp)
      coordinateResidual_normal_invertible
  simpa only [coordinateResidual_zero] using h

theorem localResidualRange_eq_zero_iff (Q : Mat) :
    localResidualRange Q = 0 ↔ specialUnitaryLocalResidual Q = 0 := by
  constructor
  · intro h
    simpa only [localResidualRange_val, Submodule.coe_zero] using congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    simpa only [localResidualRange_val, Submodule.coe_zero] using h

/-- The actual matrix graph, parameterized by the literal constraint kernel. -/
noncomputable def specialUnitaryIdentityParam (k : ConstraintTangent) : Mat :=
  matrixOfConstraintCoordinates (k, specialUnitaryNormalGraph k)

@[simp] theorem specialUnitaryIdentityParam_zero : specialUnitaryIdentityParam 0 = 1 := by
  simp only [specialUnitaryIdentityParam, specialUnitaryNormalGraph_zero]
  exact matrixOfConstraintCoordinates_zero

theorem analyticAt_specialUnitaryIdentityParam :
    AnalyticAt ℝ specialUnitaryIdentityParam 0 :=
  (analyticAt_matrixOfConstraintCoordinates _).comp
    (analyticAt_id.prod analyticAt_specialUnitaryNormalGraph)

/-- The chosen graph solves the actual equations and stays on the positive determinant branch. -/
theorem eventually_specialUnitaryIdentityParam_mem :
    ∀ᶠ k : ConstraintTangent in 𝓝 0,
      specialUnitaryIdentityParam k ∈ Matrix.specialUnitaryGroup Index ℂ := by
  have hcont : Tendsto specialUnitaryIdentityParam (𝓝 0) (𝓝 (1 : Mat)) := by
    exact specialUnitaryIdentityParam_zero ▸
      analyticAt_specialUnitaryIdentityParam.continuousAt.tendsto
  have hbranch := hcont.eventually eventually_mem_specialUnitary_iff_residual_eq_zero
  filter_upwards [eventually_coordinateResidual_graph, hbranch] with k hk hb
  apply hb.mpr
  exact (localResidualRange_eq_zero_iff _).mp hk

/-- In a genuine ambient coordinate neighborhood, SU3 is exactly this graph. -/
theorem eventually_mem_specialUnitary_iff_normalGraph :
    ∀ᶠ p : ConstraintTangent × ConstraintRange in 𝓝 0,
      matrixOfConstraintCoordinates p ∈ Matrix.specialUnitaryGroup Index ℂ ↔
        specialUnitaryNormalGraph p.1 = p.2 := by
  have hcont : Tendsto matrixOfConstraintCoordinates (𝓝 0) (𝓝 (1 : Mat)) := by
    exact matrixOfConstraintCoordinates_zero ▸
      (analyticAt_matrixOfConstraintCoordinates 0).continuousAt.tendsto
  have hb := hcont.eventually eventually_mem_specialUnitary_iff_residual_eq_zero
  filter_upwards [eventually_coordinateResidual_eq_zero_iff_graph, hb] with p hp hb
  exact hb.trans ((localResidualRange_eq_zero_iff _).symm.trans hp)

/-- Tangent coordinates of an actual ambient matrix, centered at identity. -/
def specialUnitaryIdentityCoordinates (Q : Mat) : ConstraintTangent :=
  (tangentNormalCoordinates (Q - 1)).1

/-- The left inverse holds for every parameter, independent of local validity. -/
theorem specialUnitaryIdentityCoordinates_param (k : ConstraintTangent) :
    specialUnitaryIdentityCoordinates (specialUnitaryIdentityParam k) = k := by
  simp [specialUnitaryIdentityCoordinates, specialUnitaryIdentityParam,
    matrixOfConstraintCoordinates]

/-- Every sufficiently near SU3 matrix is recovered from its literal tangent coordinates. -/
theorem eventually_mem_specialUnitary_iff_param_coordinates :
    ∀ᶠ Q : Mat in 𝓝 1,
      Q ∈ Matrix.specialUnitaryGroup Index ℂ ↔
        specialUnitaryIdentityParam (specialUnitaryIdentityCoordinates Q) = Q := by
  have hcont : Tendsto (fun Q : Mat => tangentNormalCoordinates (Q - 1))
      (𝓝 1) (𝓝 0) := by
    have hc : ContinuousAt (fun Q : Mat => tangentNormalCoordinates (Q - 1)) 1 :=
      tangentNormalCoordinates.continuous.continuousAt.comp
        (continuousAt_id.sub continuousAt_const : ContinuousAt (fun Q : Mat => Q - 1) 1)
    simpa only [sub_self, map_zero] using hc.tendsto
  filter_upwards [hcont.eventually eventually_mem_specialUnitary_iff_normalGraph] with Q hQ
  have hmatrix : matrixOfConstraintCoordinates (tangentNormalCoordinates (Q - 1)) = Q := by
    simp [matrixOfConstraintCoordinates]
  rw [hmatrix] at hQ
  refine hQ.trans ⟨?_, ?_⟩
  · intro h
    unfold specialUnitaryIdentityParam specialUnitaryIdentityCoordinates
    rw [h]
    exact hmatrix
  · intro h
    have he := congrArg (fun A : Mat => tangentNormalCoordinates (A - 1)) h
    simpa [specialUnitaryIdentityParam, matrixOfConstraintCoordinates,
      specialUnitaryIdentityCoordinates] using congrArg Prod.snd he

theorem analyticAt_specialUnitaryIdentityCoordinates (Q : Mat) :
    AnalyticAt ℝ specialUnitaryIdentityCoordinates Q :=
  (ContinuousLinearMap.fst ℝ ConstraintTangent ConstraintRange).analyticAt _ |>.comp
    ((tangentNormalCoordinates.toContinuousLinearMap.analyticAt _).comp
      (analyticAt_id.sub analyticAt_const))

/-- An open tangent neighborhood on which the analytic parameter map takes values in actual SU3. -/
theorem exists_open_specialUnitaryIdentityParam_domain :
    ∃ U : Set ConstraintTangent, IsOpen U ∧ 0 ∈ U ∧
      AnalyticOnNhd ℝ specialUnitaryIdentityParam U ∧
      ∀ k ∈ U, specialUnitaryIdentityParam k ∈ Matrix.specialUnitaryGroup Index ℂ := by
  obtain ⟨U, hU, hopen, hzero⟩ := eventually_nhds_iff.mp
    (analyticAt_specialUnitaryIdentityParam.eventually_analyticAt.and
      eventually_specialUnitaryIdentityParam_mem)
  exact ⟨U, hopen, hzero, fun k hk => (hU k hk).1, fun k hk => (hU k hk).2⟩

end UnitaryErrorBases.SpecialUnitaryConstraints

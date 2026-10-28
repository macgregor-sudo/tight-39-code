module
public import NativeNormalizedGraphDifferential
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

@[expose] public section

/-!
# Local coordinates for the actual exponential phase parameter

The forward function is the unchanged phaseExpParam used
by the native ten-direction differential proof. The pinned Circle.exp covering
supplies a local homeomorphism at zero, narrowed to the (-π,π) argument branch.
The product is composed with actual fixed circle multiplication and the frozen
phaseTripleHomeomorph. No phase chart or inverse property is assumed.
The inverse's actual argument formula is the restriction of a proved real-
analytic ambient extension; analytic overlap transitions follow from it.
No PhaseTriple manifold instance or quotient atlas is installed.

First-party composition, no upstream proof bodies copied. Primary public APIs:
mathlib commit 065356127b1dc0016f66b7283ce0ce2c4055aa55,
Analysis/SpecialFunctions/Complex/Circle.lean (Circle covering/argument),
Topology/IsLocalHomeomorph.lean (localInverseAt), and
Analysis/SpecialFunctions/Complex/Analytic.lean (analyticAt_clog).
Imported sources retain their notices. Thanks to the Lean, mathlib and project
contributors. “If I have seen further it is by standing on the sholders of
Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/
noncomputable section
open scoped Topology Matrix.Norms.Elementwise
open Set

namespace UnitaryErrorBases.ThreeCycleNormalized

/-- The actual exponential covering chart at zero, narrowed to its argument branch. -/
def circleExpLocalParam : OpenPartialHomeomorph ℝ Circle :=
  ((isLocalHomeomorph_circleExp.localInverseAt 0).symm).restr
    (Ioo (-Real.pi) Real.pi)

theorem circleExpLocalParam_apply (t : ℝ) : circleExpLocalParam t = Circle.exp t := by
  exact congrFun (isLocalHomeomorph_circleExp.localInverseAt_symm 0) t

theorem circleExpLocalParam_source : circleExpLocalParam.source =
    (isLocalHomeomorph_circleExp.localInverseAt 0).target ∩ Ioo (-Real.pi) Real.pi := by
  rw [circleExpLocalParam, OpenPartialHomeomorph.restr_source' _ _ isOpen_Ioo]
  rfl

theorem zero_mem_circleExpLocalParam_source : (0 : ℝ) ∈ circleExpLocalParam.source := by
  rw [circleExpLocalParam_source]
  exact ⟨isLocalHomeomorph_circleExp.self_mem_localInverseAt_target,
    neg_lt_zero.mpr Real.pi_pos, Real.pi_pos⟩

theorem circleExpLocalParam_symm_apply (z : Circle) (hz : z ∈ circleExpLocalParam.target) :
    circleExpLocalParam.symm z = Complex.arg (z : ℂ) := by
  have hs := circleExpLocalParam.map_target hz
  rw [circleExpLocalParam_source] at hs
  have he := circleExpLocalParam.right_inv hz
  rw [circleExpLocalParam_apply] at he
  calc
    circleExpLocalParam.symm z =
        Complex.arg (Circle.exp (circleExpLocalParam.symm z) : ℂ) :=
      (Circle.arg_exp hs.2.1 hs.2.2.le).symm
    _ = Complex.arg (z : ℂ) := congrArg (fun w : Circle => Complex.arg (w : ℂ)) he

/-- Fixed actual phase multiplication followed by the existing phase homeomorphism. -/
def phaseCircleTranslation (d₀ : PhaseTriple) : (Circle × Circle) ≃ₜ PhaseTriple :=
  ((Homeomorph.mulLeft (phaseCircle d₀ 0)).prodCongr
    (Homeomorph.mulLeft (phaseCircle d₀ 1))).trans phaseTripleHomeomorph.symm

theorem phaseCircleTranslation_apply (d₀ : PhaseTriple) (z : Circle × Circle) :
    phaseCircleTranslation d₀ z =
      phaseOfCircles (phaseCircle d₀ 0 * z.1, phaseCircle d₀ 1 * z.2) := rfl

theorem phaseCircleTranslation_symm_apply (d₀ d : PhaseTriple) :
    (phaseCircleTranslation d₀).symm d =
      ((phaseCircle d₀ 0)⁻¹ * phaseCircle d 0,
        (phaseCircle d₀ 1)⁻¹ * phaseCircle d 1) := rfl

/-- A genuine local homeomorphism whose forward function is the frozen exponential phase map. -/
def phaseExponentialLocalParam (d₀ : PhaseTriple) :
    OpenPartialHomeomorph (ℝ × ℝ) PhaseTriple :=
  (circleExpLocalParam.prod circleExpLocalParam).trans
    (phaseCircleTranslation d₀).toOpenPartialHomeomorph

theorem phaseExponentialLocalParam_apply (d₀ : PhaseTriple) (x : ℝ × ℝ) :
    phaseExponentialLocalParam d₀ x = phaseExpParam d₀ x := by
  change phaseOfCircles (phaseCircle d₀ 0 * circleExpLocalParam x.1,
    phaseCircle d₀ 1 * circleExpLocalParam x.2) = _
  rw [circleExpLocalParam_apply, circleExpLocalParam_apply]
  rfl

theorem phaseExponentialLocalParam_source (d₀ : PhaseTriple) :
    (phaseExponentialLocalParam d₀).source = circleExpLocalParam.source ×ˢ circleExpLocalParam.source := by
  ext x
  simp [phaseExponentialLocalParam]

theorem zero_mem_phaseExponentialLocalParam_source (d₀ : PhaseTriple) :
    (0 : ℝ × ℝ) ∈ (phaseExponentialLocalParam d₀).source := by
  rw [phaseExponentialLocalParam_source]
  exact ⟨zero_mem_circleExpLocalParam_source, zero_mem_circleExpLocalParam_source⟩

theorem self_mem_phaseExponentialLocalParam_target (d₀ : PhaseTriple) :
    d₀ ∈ (phaseExponentialLocalParam d₀).target := by
  have h := (phaseExponentialLocalParam d₀).map_source (zero_mem_phaseExponentialLocalParam_source d₀)
  simpa only [phaseExponentialLocalParam_apply, phaseExpParam_zero] using h

theorem phaseExponentialLocalParam_target (d₀ : PhaseTriple) :
    (phaseExponentialLocalParam d₀).target =
      {d | (phaseCircle d₀ 0)⁻¹ * phaseCircle d 0 ∈ circleExpLocalParam.target ∧
        (phaseCircle d₀ 1)⁻¹ * phaseCircle d 1 ∈ circleExpLocalParam.target} := by
  ext d
  simp [phaseExponentialLocalParam, phaseCircleTranslation_symm_apply]

/-- The explicit inverse-coordinate formula extends to ambient complex triples. -/
def phaseExponentialCoordinatesExtension (d₀ : PhaseTriple) (v : Index → ℂ) : ℝ × ℝ :=
  (Complex.arg ((d₀.val 0)⁻¹ * v 0), Complex.arg ((d₀.val 1)⁻¹ * v 1))

theorem phaseExponentialLocalParam_symm_apply (d₀ d : PhaseTriple)
    (hd : d ∈ (phaseExponentialLocalParam d₀).target) :
    (phaseExponentialLocalParam d₀).symm d = phaseExponentialCoordinatesExtension d₀ d.val := by
  rw [phaseExponentialLocalParam_target] at hd
  change (circleExpLocalParam.symm ((phaseCircle d₀ 0)⁻¹ * phaseCircle d 0),
    circleExpLocalParam.symm ((phaseCircle d₀ 1)⁻¹ * phaseCircle d 1)) = _
  rw [circleExpLocalParam_symm_apply _ hd.1, circleExpLocalParam_symm_apply _ hd.2]
  rfl

theorem phaseExponentialCoordinates_param (d₀ : PhaseTriple) (x : ℝ × ℝ)
    (hx : x ∈ (phaseExponentialLocalParam d₀).source) :
    phaseExponentialCoordinatesExtension d₀ (phaseExpParam d₀ x).val = x := by
  have h := (phaseExponentialLocalParam d₀).left_inv hx
  rw [phaseExponentialLocalParam_symm_apply d₀ _ ((phaseExponentialLocalParam d₀).map_source hx),
    phaseExponentialLocalParam_apply] at h
  exact h

theorem phaseExpParam_coordinates (d₀ d : PhaseTriple)
    (hd : d ∈ (phaseExponentialLocalParam d₀).target) :
    phaseExpParam d₀ (phaseExponentialCoordinatesExtension d₀ d.val) = d := by
  have h := (phaseExponentialLocalParam d₀).right_inv hd
  rw [phaseExponentialLocalParam_apply, phaseExponentialLocalParam_symm_apply d₀ d hd] at h
  exact h

theorem circleExpLocalParam_target_slitPlane (z : Circle)
    (hz : z ∈ circleExpLocalParam.target) : (z : ℂ) ∈ Complex.slitPlane := by
  have hs := circleExpLocalParam.map_target hz
  rw [circleExpLocalParam_source] at hs
  have hlt : Complex.arg (z : ℂ) < Real.pi := by
    rw [← circleExpLocalParam_symm_apply z hz]
    exact hs.2.2
  exact Complex.mem_slitPlane_iff_arg.mpr ⟨ne_of_lt hlt, Circle.coe_ne_zero z⟩

/-- Analyticity of the ambient inverse formula at every actual target phase.
This does not infer analyticity from the covering-map theorem. -/
theorem analyticAt_phaseExponentialCoordinatesExtension (d₀ d : PhaseTriple)
    (hd : d ∈ (phaseExponentialLocalParam d₀).target) :
    AnalyticAt ℝ (phaseExponentialCoordinatesExtension d₀) d.val := by
  rw [phaseExponentialLocalParam_target] at hd
  have h0 : (d₀.val 0)⁻¹ * d.val 0 ∈ Complex.slitPlane := by
    exact circleExpLocalParam_target_slitPlane _ hd.1
  have h1 : (d₀.val 1)⁻¹ * d.val 1 ∈ Complex.slitPlane := by
    exact circleExpLocalParam_target_slitPlane _ hd.2
  have harg (z : ℂ) (hz : z ∈ Complex.slitPlane) : AnalyticAt ℝ Complex.arg z := by
    have h := (Complex.imCLM.analyticAt _).comp (analyticAt_clog hz).restrictScalars
    change AnalyticAt ℝ (fun w : ℂ => (Complex.log w).im) z at h
    simpa only [Complex.log_im] using! h
  have ha : AnalyticAt ℝ (fun v : Index → ℂ => (d₀.val 0)⁻¹ * v 0) d.val :=
    analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℝ) (0 : Index)).analyticAt d.val)
  have hb : AnalyticAt ℝ (fun v : Index → ℂ => (d₀.val 1)⁻¹ * v 1) d.val :=
    analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℝ) (1 : Index)).analyticAt d.val)
  exact ((harg _ h0).comp_of_eq ha rfl).prod ((harg _ h1).comp_of_eq hb rfl)

theorem analyticAt_phaseExponentialLocalParam_val (d₀ : PhaseTriple) (x : ℝ × ℝ) :
    AnalyticAt ℝ (fun y => (phaseExponentialLocalParam d₀ y).val) x := by
  simpa only [phaseExponentialLocalParam_apply] using analyticAt_phaseExpParam_val d₀ x

/-- Genuine analytic compatibility of these particular local coordinates on their overlap. -/
theorem analyticAt_phaseExponentialLocalParam_transition (d₀ d₁ : PhaseTriple) (x : ℝ × ℝ)
    (hx : x ∈ (phaseExponentialLocalParam d₁).source)
    (hd : phaseExponentialLocalParam d₁ x ∈ (phaseExponentialLocalParam d₀).target) :
    AnalyticAt ℝ (fun y => (phaseExponentialLocalParam d₀).symm
      (phaseExponentialLocalParam d₁ y)) x := by
  have ha := (analyticAt_phaseExponentialCoordinatesExtension d₀
    (phaseExponentialLocalParam d₁ x) hd).comp_of_eq
      (analyticAt_phaseExponentialLocalParam_val d₁ x) rfl
  apply ha.congr
  have hn := ((phaseExponentialLocalParam d₁).continuousAt hx).preimage_mem_nhds
    ((phaseExponentialLocalParam d₀).open_target.mem_nhds hd)
  filter_upwards [hn] with y hy
  exact (phaseExponentialLocalParam_symm_apply d₀ (phaseExponentialLocalParam d₁ y) hy).symm

end UnitaryErrorBases.ThreeCycleNormalized

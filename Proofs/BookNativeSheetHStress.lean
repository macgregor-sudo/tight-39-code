module

public import BookNativeFamilyAnchor
public import BookNativeReducedQuadratic
public import GSResidual

@[expose] public section

/-! The specified native inverse-slice group coordinate transports the fixed-anchor H stresses.
No reproduction or positivity assumption is used. -/
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Option2.NativeStress.BookHT.SheetHStress
open CKM.NativeFirstOrder CKM.NativeFourFamily CKM.NativeGroupSlice
open SheetReduction TangentCoordinates NativeNormalKernelBridge ReducedQuadratic
open NativePolynomial QuadraticCertificate.ExactCKMConfiguration
open AnalyticDerivative
open scoped Topology BigOperators InnerProductSpace

abbrev FamilyCoordinates := Common × Triple

def rawFamily (i : Fin 4) (p : FamilyCoordinates) : Cfg :=
  preMap exactPhases exactPhases_unit i
    ((familyParam i p).1, 0, (familyParam i p).2)

def familyCfg (i : Fin 4) (p : FamilyCoordinates) : Cfg :=
  literalCfg exactPhases + (familySheet i p : Cfg)

/-- A specified inverse-chart coordinate, not a pointwise existential choice. -/
def familyGroupCoordinate (i : Fin 4) (p : FamilyCoordinates) : derC :=
  ((slicePH exactPhases exactPhases_unit).symm (rawFamily i p)).1

def familyRowAction (i : Fin 4) (p : FamilyCoordinates) : RealResiduals →L[ℝ] RealResiduals :=
  rowAction (groupChart (familyGroupCoordinate i p))

def componentField (i : Fin 4) (a : Fin 3) (p : FamilyCoordinates) : RealResiduals →L[ℝ] ℂ :=
  (stressCovector (NativeH.weightC i a)).comp (familyRowAction i p)

/-- Keep the Book direction w fixed, as required by the supported-stress criterion. -/
def realField (i : Fin 4) (w : Blocks) (p : FamilyCoordinates) : RealResiduals →L[ℝ] ℝ :=
  (NativeH.realStressFunctional i w).comp (familyRowAction i p)

@[simp] theorem rawFamily_zero (i : Fin 4) : rawFamily i 0 = literalCfg exactPhases := by
  simp only [rawFamily, familyParam_zero, Prod.fst_zero, Prod.snd_zero, Prod.mk_zero_zero]
  exact preMap_zero exactPhases_unit i

@[simp] theorem familyGroupCoordinate_zero (i : Fin 4) : familyGroupCoordinate i 0 = 0 := by
  simp only [familyGroupCoordinate, rawFamily_zero, slicePH_symm_literalCfg, Prod.fst_zero]

@[simp] theorem familyRowAction_zero (i : Fin 4) : familyRowAction i 0 = 1 := by
  rw [familyRowAction, familyGroupCoordinate_zero, groupChart_zero, rowAction_one]

@[simp] theorem componentField_zero (i : Fin 4) (a : Fin 3) :
    componentField i a 0 = stressCovector (NativeH.weightC i a) := by
  rw [componentField, familyRowAction_zero]
  rfl

@[simp] theorem realField_zero (i : Fin 4) (w : Blocks) :
    realField i w 0 = NativeH.realStressFunctional i w := by
  rw [realField, familyRowAction_zero]
  rfl

theorem rawFamily_analytic (i : Fin 4) : AnalyticAt ℝ (rawFamily i) 0 := by
  let J : SliceParam →L[ℝ] PreParam :=
    (ContinuousLinearMap.fst ℝ (Fin 8 → ℝ) (Fin 2 → ℝ)).prod
      ((0 : SliceParam →L[ℝ] (Fin 8 → ℝ)).prod
        (ContinuousLinearMap.snd ℝ (Fin 8 → ℝ) (Fin 2 → ℝ)))
  have he : AnalyticAt ℝ (fun p : FamilyCoordinates =>
      ((familyParam i p).1, (0 : Fin 8 → ℝ), (familyParam i p).2)) 0 :=
    (J.analyticAt _).comp (familyParam_analytic i)
  exact (analyticAt_preMap exactPhases_unit i).comp_of_eq he (by simp [familyParam_zero])

theorem familyGroupCoordinate_analytic (i : Fin 4) :
    AnalyticAt ℝ (familyGroupCoordinate i) 0 := by
  have hf := (analyticAt_slicePH_symm exactPhases exactPhases_unit).comp_of_eq
    (rawFamily_analytic i) (rawFamily_zero i)
  exact analyticAt_fst.comp hf

theorem familyRowAction_analytic (i : Fin 4) : AnalyticAt ℝ (familyRowAction i) 0 :=
  (analyticAt_rowAction _).comp ((analyticAt_groupChart _).comp (familyGroupCoordinate_analytic i))

theorem componentField_analytic (i : Fin 4) (a : Fin 3) :
    AnalyticAt ℝ (componentField i a) 0 :=
  ((ContinuousLinearMap.compL ℝ RealResiduals RealResiduals ℂ
    (stressCovector (NativeH.weightC i a))).analyticAt _).comp (familyRowAction_analytic i)

theorem realField_analytic (i : Fin 4) (w : Blocks) : AnalyticAt ℝ (realField i w) 0 :=
  ((ContinuousLinearMap.compL ℝ RealResiduals RealResiduals ℝ
    (NativeH.realStressFunctional i w)).analyticAt _).comp (familyRowAction_analytic i)

theorem rawFamily_mem_target (i : Fin 4) :
    ∀ᶠ p in 𝓝 (0 : FamilyCoordinates),
      rawFamily i p ∈ (slicePH exactPhases exactPhases_unit).target :=
  (rawFamily_analytic i).continuousAt.preimage_mem_nhds
    (by
      rw [rawFamily_zero]
      exact (slicePH exactPhases exactPhases_unit).open_target.mem_nhds
        (literalCfg_mem_slicePH_target exactPhases exactPhases_unit))

theorem rawFamily_eq_act (i : Fin 4) (p : FamilyCoordinates)
    (hp : rawFamily i p ∈ (slicePH exactPhases exactPhases_unit).target) :
    rawFamily i p = actC (groupChart (familyGroupCoordinate i p)) (familyCfg i p) :=
  ((slicePH exactPhases exactPhases_unit).right_inv hp).symm

/-- Differentiate the accepted off-shell covariance, in the actual full ambient domain. -/
theorem derivative_covariance {A : CEnd} (hA : A ∈ autC) (C : Cfg) :
    (fderiv ℝ AnalyticDerivative.originalF (actC A C)).comp (actC A) =
      (rowAction A).comp (fderiv ℝ AnalyticDerivative.originalF C) := by
  have hl := (originalF_differentiable.differentiableAt (x := actC A C)).hasFDerivAt.comp C
    (actC A).hasFDerivAt
  have hr := (rowAction A).hasFDerivAt.comp C
    (originalF_differentiable.differentiableAt (x := C)).hasFDerivAt
  have he : (AnalyticDerivative.originalF ∘ actC A) = rowAction A ∘ AnalyticDerivative.originalF :=
    funext fun x => originalF_actC hA x
  rw [he] at hl
  exact hl.unique hr

theorem componentField_annihilates (i : Fin 4) (a : Fin 3) (p : FamilyCoordinates)
    (hp : rawFamily i p ∈ (slicePH exactPhases exactPhases_unit).target) :
    (componentField i a p).comp (fderiv ℝ AnalyticDerivative.originalF (familyCfg i p)) = 0 := by
  have hn := raw_component_annihilates i a
    ((familyParam i p).1, 0, (familyParam i p).2)
  change (stressCovector (NativeH.weightC i a)).comp
    (fderiv ℝ AnalyticDerivative.originalF (rawFamily i p)) = 0 at hn
  rw [rawFamily_eq_act i p hp] at hn
  ext v
  change stressCovector (NativeH.weightC i a)
    (rowAction (groupChart (familyGroupCoordinate i p))
      (fderiv ℝ AnalyticDerivative.originalF (familyCfg i p) v)) = 0
  have hc := congrArg (fun L : Cfg →L[ℝ] RealResiduals => L v)
    (derivative_covariance (groupChart_mem_autC (familyGroupCoordinate i p)) (familyCfg i p))
  simp only [ContinuousLinearMap.comp_apply] at hc
  rw [← hc]
  exact congrArg (fun L : Cfg →L[ℝ] ℂ => L (actC (groupChart (familyGroupCoordinate i p)) v)) hn

/-- Explicit Hermitian combination, with the accepted factor three and real part. -/
theorem realField_apply (i : Fin 4) (w : Blocks) (p : FamilyCoordinates) (q : RealResiduals) :
    realField i w p q = 3 *
      (∑ a : Fin 3, star (sigma (w i) a) * componentField i a p q).re := by
  simpa only [realField, componentField, ContinuousLinearMap.comp_apply,
    AnalyticDerivative.stressCovector_apply] using
    NativeH.realStressFunctional_apply_hermitian i w (familyRowAction i p q)

theorem realField_annihilates (i : Fin 4) (w : Blocks) (p : FamilyCoordinates)
    (hp : rawFamily i p ∈ (slicePH exactPhases exactPhases_unit).target) :
    (realField i w p).comp (fderiv ℝ AnalyticDerivative.originalF (familyCfg i p)) = 0 := by
  ext v
  change realField i w p (fderiv ℝ AnalyticDerivative.originalF (familyCfg i p) v) = 0
  rw [realField_apply]
  have hc (a : Fin 3) : componentField i a p
      (fderiv ℝ AnalyticDerivative.originalF (familyCfg i p) v) = 0 :=
    congrArg (fun L : Cfg →L[ℝ] ℂ => L v) (componentField_annihilates i a p hp)
  simp only [hc, mul_zero, Finset.sum_const_zero, Complex.zero_re]

end Option2.NativeStress.BookHT.SheetHStress

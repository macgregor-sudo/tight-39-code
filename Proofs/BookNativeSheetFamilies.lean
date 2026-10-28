module

public import BookNativeNormalKernelEquivalence
public import NativeSliceImplicitReduction
public import A5Chart

@[expose] public section

/-! Actual A5 family germs reparametrized by the common tangent and unchanged Book axes. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.BookHT.SheetReduction
open TangentCoordinates NativeNormalKernelBridge
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeSliceNormalSplitting CKM.NativeSliceImplicitReduction
open NativePolynomial QuadraticCertificate.ExactCKMConfiguration
open scoped Topology

theorem strict_comp_zero {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : F → G} {f' : E →L[ℝ] F} {g' : F →L[ℝ] G}
    (hg : HasStrictFDerivAt g g' 0) (hf : HasStrictFDerivAt f f' 0) (h0 : f 0 = 0) :
    HasStrictFDerivAt (fun x => g (f x)) (g'.comp f') 0 := by
  have hg' : HasStrictFDerivAt g g' (f 0) := by rw [h0]; exact hg
  exact hg'.comp 0 hf

abbrev Common := fixQK exactPhases
abbrev Normal := normalC exactPhases
abbrev Complement := normalComplement exactPhases
abbrev KernelModel := Common × Blocks
abbrev Model := KernelModel × Complement

/-- Actual common tangent inclusion in the normal slice. -/
def commonNormal : Common →L[ℝ] Normal :=
  (fixQK exactPhases).subtypeL.codRestrict Normal (fun c => c.property.1.1.2)

def bookNormal : Blocks →L[ℝ] Normal := normalProjection.comp bookDirection

def commonDerivative : (Fin 4 → ℝ) →L[ℝ] Common :=
  ((normalC exactPhases).subtypeL.comp (sliceCommonDer exactPhases exactPhases_unit)).codRestrict
    Common (by
      intro θ
      change (sliceCommonDer exactPhases exactPhases_unit θ : Cfg) ∈ fixQK exactPhases
      rw [← range_sliceCommonDer exactPhases_good]
      exact ⟨sliceCommonDer exactPhases exactPhases_unit θ, ⟨θ, rfl⟩, rfl⟩)

theorem commonDerivative_bijective : Function.Bijective commonDerivative := by
  constructor
  · intro x y h
    apply sliceCommonDer_injective exactPhases_unit
    apply Subtype.ext
    exact congrArg (fun c : Common => (c : Cfg)) h
  · intro c
    have hc : (c : Cfg) ∈ fixQK exactPhases := c.property
    rw [← range_sliceCommonDer exactPhases_good] at hc
    obtain ⟨n, ⟨θ, rfl⟩, he⟩ := hc
    exact ⟨θ, Subtype.ext he⟩

def commonLinearEquiv : (Fin 4 → ℝ) ≃L[ℝ] Common :=
  (LinearEquiv.ofBijective commonDerivative.toLinearMap commonDerivative_bijective).toContinuousLinearEquiv

def commonSheet (c : Common) : Normal :=
  sliceCommon exactPhases exactPhases_unit (commonLinearEquiv.symm c)

@[simp] theorem commonSheet_zero : commonSheet 0 = 0 := by
  simp [commonSheet, sliceCommon_zero]

theorem commonSheet_analytic : AnalyticAt ℝ commonSheet 0 :=
  (analyticAt_sliceCommon exactPhases_unit).comp_of_eq (commonLinearEquiv.symm.analyticAt 0)
    (map_zero _)

theorem commonSheet_derivative : HasStrictFDerivAt commonSheet commonNormal 0 := by
  have hd := strict_comp_zero (hasStrictFDerivAt_sliceCommon exactPhases_unit)
    commonLinearEquiv.symm.hasStrictFDerivAt (map_zero _)
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro c
  apply Subtype.ext
  exact congrArg (fun x : Common => (x : Cfg)) (commonLinearEquiv.apply_symm_apply c)

/-- The exact already-proved Book-axis parameter vector as a real linear map. -/
def axisLinear (H : Fin 4) : Triple →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun := axisParameters H
  map_add' u v := by
    ext m
    fin_cases H <;> fin_cases m <;> simp [axisParameters, Pi.add_apply] <;> ring
  map_smul' a u := by
    ext m
    fin_cases H <;> fin_cases m <;> simp [axisParameters, Pi.smul_apply] <;> ring

def axisCL (H : Fin 4) : Triple →L[ℝ] (Fin 8 → ℝ) := (axisLinear H).toContinuousLinearMap

def axisParam (H : Fin 4) : Triple →L[ℝ] SliceParam := (axisCL H).prod 0

def familyInclusion (H : Fin 4) : (Fin 4 → ℝ) → SliceParam :=
  Classical.choose (exists_slice_inclusion exactPhases_unit H)

theorem familyInclusion_spec (H : Fin 4) :
    AnalyticAt ℝ (familyInclusion H) 0 ∧ familyInclusion H 0 = 0 ∧
      ∀ᶠ θ in 𝓝 (0 : Fin 4 → ℝ),
        sliceFam exactPhases exactPhases_unit H (familyInclusion H θ) =
          sliceCommon exactPhases exactPhases_unit θ :=
  Classical.choose_spec (exists_slice_inclusion exactPhases_unit H)

/-- Shift the actual common-to-family inclusion by the exact off-diagonal Book parameters. -/
def familyParam (H : Fin 4) (p : Common × Triple) : SliceParam :=
  familyInclusion H (commonLinearEquiv.symm p.1) + axisParam H p.2

def familySheet (H : Fin 4) (p : Common × Triple) : Normal :=
  sliceFam exactPhases exactPhases_unit H (familyParam H p)

@[simp] theorem familyParam_zero (H : Fin 4) : familyParam H 0 = 0 := by
  simp [familyParam, (familyInclusion_spec H).2.1]

@[simp] theorem familySheet_zero (H : Fin 4) : familySheet H 0 = 0 := by
  simp [familySheet, sliceFam_zero]

theorem familyParam_analytic (H : Fin 4) : AnalyticAt ℝ (familyParam H) 0 := by
  exact ((familyInclusion_spec H).1.comp_of_eq
    ((commonLinearEquiv.symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℝ Common Triple)).analyticAt 0) (map_zero _)).add
        (((axisParam H).comp (ContinuousLinearMap.snd ℝ Common Triple)).analyticAt 0)

theorem familySheet_analytic (H : Fin 4) : AnalyticAt ℝ (familySheet H) 0 :=
  (analyticAt_sliceFam exactPhases_unit H).comp_of_eq (familyParam_analytic H) (familyParam_zero H)

theorem familySheet_common_germ (H : Fin 4) :
    (fun c : Common => familySheet H (c, 0)) =ᶠ[𝓝 0] commonSheet := by
  have ht : Filter.Tendsto commonLinearEquiv.symm (𝓝 (0 : Common)) (𝓝 0) := by
    simpa only [map_zero] using commonLinearEquiv.symm.continuous.continuousAt.tendsto (x := 0)
  filter_upwards [ht.eventually (familyInclusion_spec H).2.2] with c hc
  simpa [familySheet, familyParam, commonSheet] using hc

def familyDerivative (H : Fin 4) : (Common × Triple) →L[ℝ] Normal :=
  commonNormal.coprod (bookNormal.comp (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => Triple) H))

theorem familySheet_derivative (H : Fin 4) :
    HasStrictFDerivAt (familySheet H) (familyDerivative H) 0 := by
  let J := (fderiv ℝ (familyInclusion H) 0).comp commonLinearEquiv.symm.toContinuousLinearMap
  have hj : HasStrictFDerivAt (fun c : Common => familyInclusion H (commonLinearEquiv.symm c)) J 0 :=
    strict_comp_zero (familyInclusion_spec H).1.hasStrictFDerivAt
      commonLinearEquiv.symm.hasStrictFDerivAt (map_zero _)
  have hfac : (sliceFamDer exactPhases exactPhases_unit H).comp J = commonNormal := by
    have hf : HasFDerivAt (fun c : Common => familySheet H (c, 0))
        ((sliceFamDer exactPhases exactPhases_unit H).comp J) 0 := by
      have hh := strict_comp_zero (hasStrictFDerivAt_sliceFam exactPhases_unit H) hj
        (by simp [(familyInclusion_spec H).2.1])
      simpa [familySheet, familyParam] using hh.hasFDerivAt
    exact (hf.congr_of_eventuallyEq (familySheet_common_germ H).symm).unique
      commonSheet_derivative.hasFDerivAt
  have hp : HasStrictFDerivAt (familyParam H) (J.coprod (axisParam H)) 0 := by
    exact (hj.comp (0 : Common × Triple) hasStrictFDerivAt_fst).add
      ((axisParam H).hasStrictFDerivAt.comp (0 : Common × Triple) hasStrictFDerivAt_snd)
  have hs := strict_comp_zero (hasStrictFDerivAt_sliceFam exactPhases_unit H) hp (familyParam_zero H)
  apply hs.congr_fderiv
  apply ContinuousLinearMap.ext
  intro p
  change sliceFamDer exactPhases exactPhases_unit H (J p.1 + axisParam H p.2) =
    commonNormal p.1 + bookNormal (Pi.single H p.2)
  rw [map_add, show sliceFamDer exactPhases exactPhases_unit H (J p.1) = commonNormal p.1
    from congrArg (fun L : Common →L[ℝ] Normal => L p.1) hfac]
  congr 1
  rw [sliceFamDer_eq_normalProjection]
  change normalProjection (preDer exactPhases exactPhases_unit H (axisParameters H p.2, 0, 0)) = _
  rw [preDer_apply, ← projectedSimultaneousFamily_eq_left, ← projectedBook_axis]
  rfl

/-- These are the actual original residuals on the native family germs. -/
theorem familySheet_originalF_germ (H : Fin 4) :
    ∀ᶠ p in 𝓝 (0 : Common × Triple), normalResidual exactPhases (familySheet H p) = 0 := by
  have ht : Filter.Tendsto (familyParam H) (𝓝 0) (𝓝 0) := by
    simpa only [familyParam_zero] using (familyParam_analytic H).continuousAt.tendsto
  exact ht.eventually (eventually_originalF_sliceFam exactPhases_unit H)

/-- The reparametrization is genuine: its derivative is a bijection onto the actual ten parameters. -/
theorem familyParam_derivative_bijective (H : Fin 4) :
    Function.Bijective (fderiv ℝ (familyParam H) 0) := by
  have hd : (sliceFamDer exactPhases exactPhases_unit H).comp (fderiv ℝ (familyParam H) 0) =
      familyDerivative H := by
    have hc := strict_comp_zero (hasStrictFDerivAt_sliceFam exactPhases_unit H)
      (familyParam_analytic H).hasStrictFDerivAt (familyParam_zero H)
    exact hc.hasFDerivAt.unique (familySheet_derivative H).hasFDerivAt
  have hi : Function.Injective (familyDerivative H) := by
    intro a b hab
    apply (familyCommonMap_bijective H).1
    apply Subtype.ext
    exact congrArg (fun n : Normal => (n : Cfg)) hab
  have hpi : Function.Injective (fderiv ℝ (familyParam H) 0) := by
    intro a b hab
    apply hi
    rw [← hd]
    simp only [ContinuousLinearMap.comp_apply, hab]
  have hdim : Module.finrank ℝ (Common × Triple) = Module.finrank ℝ SliceParam := by
    rw [Module.finrank_prod, finrank_fixQK exactPhases_good, finrank_triple_real]
    simp [SliceParam, Module.finrank_prod]
  exact ⟨hpi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hpi⟩

def familyParamEquiv (H : Fin 4) : (Common × Triple) ≃L[ℝ] SliceParam :=
  (LinearEquiv.ofBijective (fderiv ℝ (familyParam H) 0).toLinearMap
    (familyParam_derivative_bijective H)).toContinuousLinearEquiv

def familyParamPH (H : Fin 4) : OpenPartialHomeomorph (Common × Triple) SliceParam :=
  ((familyParam_analytic H).contDiffAt (n := 2)).toOpenPartialHomeomorph (familyParam H) (f' := familyParamEquiv H)
    ((familyParam_analytic H).differentiableAt.hasFDerivAt) (by norm_num)

end Option2.NativeStress.BookHT.SheetReduction
#print axioms Option2.NativeStress.BookHT.SheetReduction.familySheet_derivative
#print axioms Option2.NativeStress.BookHT.SheetReduction.familyParam_derivative_bijective

module

public import BookNativeSheetFamilies

@[expose] public section

/-! A simultaneous native sheet chart with its derivative fixed to the actual Book map. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.BookHT.SheetReduction
open TangentCoordinates NativeNormalKernelBridge
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeSliceNormalSplitting CKM.NativeSliceImplicitReduction
open NativePolynomial QuadraticCertificate.ExactCKMConfiguration
open scoped Topology

def kernelLinearEquiv : KernelModel ≃L[ℝ] normalKernel exactPhases :=
  bookNormalKernelEquiv.trans (LinearEquiv.toContinuousLinearEquiv (𝕜 := ℝ)
    (E := ↥(tanN exactPhases)) (F := ↥(normalKernel exactPhases)) (kernelEquivTanN exactPhases).symm)

def sheetDerivative : Model ≃L[ℝ] Normal :=
  (kernelLinearEquiv.prodCongr (complementRangeEquiv exactPhases)).trans
    (chartDerivative exactPhases).symm

theorem sheetDerivative_apply (p : Model) : sheetDerivative p =
    commonNormal p.1.1 + bookNormal p.1.2 + (p.2 : Normal) := by
  change (kernelLinearEquiv p.1 : Normal) +
    normalRightInverse exactPhases (complementRangeEquiv exactPhases p.2) = _
  have he : normalRightInverse exactPhases (complementRangeEquiv exactPhases p.2) =
      (p.2 : Normal) := by
    change (((complementRangeEquiv exactPhases).symm
      (complementRangeEquiv exactPhases p.2) : Complement) : Normal) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [he]
  rfl

def commonPr : Model →L[ℝ] Common :=
  (ContinuousLinearMap.fst ℝ Common Blocks).comp (ContinuousLinearMap.fst ℝ KernelModel Complement)
def familyPr (H : Fin 4) : Model →L[ℝ] (Common × Triple) :=
  commonPr.prod ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Triple) H).comp
    ((ContinuousLinearMap.snd ℝ Common Blocks).comp (ContinuousLinearMap.fst ℝ KernelModel Complement)))
def complementPr : Model →L[ℝ] Normal :=
  (normalComplement exactPhases).subtypeL.comp (ContinuousLinearMap.snd ℝ KernelModel Complement)

/-- The sum of the four actual families minus three copies of their common germ. -/
def sheetMap (p : Model) : Normal :=
  commonSheet (commonPr p) + ∑ H : Fin 4,
    (familySheet H (familyPr H p) - commonSheet (commonPr p)) + complementPr p

@[simp] theorem sheetMap_zero : sheetMap 0 = 0 := by
  simp [sheetMap]

theorem sheetMap_analytic : AnalyticAt ℝ sheetMap 0 := by
  have hc : AnalyticAt ℝ (fun p : Model => commonSheet (commonPr p)) 0 :=
    commonSheet_analytic.comp_of_eq (ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := Model) (F := ↥Common) commonPr 0) (map_zero _)
  have hs : ∀ H ∈ (Finset.univ : Finset (Fin 4)), AnalyticAt ℝ
      (fun p : Model => familySheet H (familyPr H p) - commonSheet (commonPr p)) 0 := by
    intro H _
    have hp : AnalyticAt ℝ (fun p : Model => familySheet H (familyPr H p)) 0 := by
      have hf : AnalyticAt ℝ (familySheet H) (familyPr H 0) := by
        rw [map_zero]; exact familySheet_analytic H
      exact hf.comp (ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := Model)
        (F := Common × Triple) (familyPr H) 0)
    exact AnalyticAt.sub (E := Model) (F := ↥Normal) hp hc
  exact (hc.add (Finset.analyticAt_fun_sum _ hs)).add (ContinuousLinearMap.analyticAt (𝕜 := ℝ) (E := Model) (F := ↥Normal) complementPr 0)

theorem sheetMap_derivative : HasStrictFDerivAt sheetMap
    (sheetDerivative : Model →L[ℝ] Normal) 0 := by
  have hc : HasStrictFDerivAt (fun p : Model => commonSheet (commonPr p))
      (commonNormal.comp commonPr) 0 := strict_comp_zero (E := Model) (F := ↥Common) (G := ↥Normal) commonSheet_derivative (ContinuousLinearMap.hasStrictFDerivAt (𝕜 := ℝ) (E := Model) (F := ↥Common) commonPr (x := 0)) (map_zero _)
  let B (H : Fin 4) : Model →L[ℝ] Normal := bookNormal.comp
    ((ContinuousLinearMap.single ℝ (fun _ : Fin 4 => Triple) H).comp
      ((ContinuousLinearMap.snd ℝ Common Triple).comp (familyPr H)))
  have hs : ∀ H ∈ (Finset.univ : Finset (Fin 4)), HasStrictFDerivAt
      (fun p : Model => familySheet H (familyPr H p) - commonSheet (commonPr p)) (B H) 0 := by
    intro H _
    have hf : HasStrictFDerivAt (fun p : Model => familySheet H (familyPr H p))
        ((familyDerivative H).comp (familyPr H)) 0 :=
      strict_comp_zero (E := Model) (F := Common × Triple) (G := ↥Normal)
        (familySheet_derivative H)
        (ContinuousLinearMap.hasStrictFDerivAt (𝕜 := ℝ) (E := Model)
          (F := Common × Triple) (familyPr H) (x := 0)) (map_zero _)
    apply (HasStrictFDerivAt.fun_sub (𝕜 := ℝ) (E := Model) (F := ↥Normal) hf hc).congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    change commonNormal p.1.1 + bookNormal (Pi.single H (p.1.2 H)) - commonNormal p.1.1 =
      bookNormal (Pi.single H (p.1.2 H))
    abel
  have hsum := HasStrictFDerivAt.fun_sum (𝕜 := ℝ) (E := Model) (F := ↥Normal) hs
  have hadd := HasStrictFDerivAt.fun_add (𝕜 := ℝ) (E := Model) (F := ↥Normal) hc hsum
  have hd := HasStrictFDerivAt.fun_add (𝕜 := ℝ) (E := Model) (F := ↥Normal) hadd
    (ContinuousLinearMap.hasStrictFDerivAt (𝕜 := ℝ) (E := Model) (F := ↥Normal) complementPr (x := 0))
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro p
  change (commonNormal.comp commonPr + ∑ H, B H + complementPr) p = sheetDerivative p
  rw [sheetDerivative_apply]
  simp only [add_apply, sum_apply]
  change commonNormal p.1.1 +
    (∑ H : Fin 4, bookNormal (Pi.single H (p.1.2 H))) +
      (p.2 : Normal) = _
  congr 2
  simpa using ContinuousLinearMap.sum_comp_single ℝ (fun _ : Fin 4 => Triple) bookNormal p.1.2

def sheetPH : OpenPartialHomeomorph Model Normal :=
  sheetMap_analytic.contDiffAt.toOpenPartialHomeomorph sheetMap (n := 2)
    sheetMap_derivative.hasFDerivAt (by norm_num)

@[simp] theorem sheetPH_coe : ⇑sheetPH = sheetMap := rfl

theorem zero_mem_sheetPH_source : (0 : Model) ∈ sheetPH.source :=
  (sheetMap_analytic.contDiffAt (n := 2)).mem_toOpenPartialHomeomorph_source
    sheetMap_derivative.hasFDerivAt (by norm_num)

@[simp] theorem sheetPH_zero : sheetPH 0 = 0 := sheetMap_zero

theorem zero_mem_sheetPH_target : (0 : Normal) ∈ sheetPH.target := by
  simpa only [sheetPH_zero] using sheetPH.map_source zero_mem_sheetPH_source

@[simp] theorem sheetPH_symm_zero : sheetPH.symm 0 = 0 := by
  simpa only [sheetPH_zero] using sheetPH.left_inv zero_mem_sheetPH_source

theorem sheetPH_C2 : ContDiffAt ℝ 2 sheetPH 0 := sheetMap_analytic.contDiffAt

theorem sheetPH_symm_C2 : ContDiffAt ℝ 2 sheetPH.symm 0 := by
  apply OpenPartialHomeomorph.contDiffAt_symm (𝕜 := ℝ) (E := Model) (F := Normal)
    sheetPH zero_mem_sheetPH_target (f₀' := sheetDerivative)
  · simpa only [sheetPH_symm_zero, sheetPH_coe] using sheetMap_derivative.hasFDerivAt
  · simpa only [sheetPH_symm_zero] using sheetPH_C2

def commonAxis : Common →L[ℝ] Model :=
  ((ContinuousLinearMap.id ℝ Common).prod (0 : Common →L[ℝ] Blocks)).prod 0

def familyAxis (H : Fin 4) : (Common × Triple) →L[ℝ] Model :=
  ((ContinuousLinearMap.fst ℝ Common Triple).prod
    ((ContinuousLinearMap.single ℝ (fun _ : Fin 4 => Triple) H).comp
      (ContinuousLinearMap.snd ℝ Common Triple))).prod 0

theorem sheetMap_common_germ : (fun c : Common => sheetMap (commonAxis c)) =ᶠ[𝓝 0] commonSheet := by
  filter_upwards [Filter.eventually_all.2 familySheet_common_germ] with c hc
  change commonSheet c + ∑ H : Fin 4, (familySheet H (c, 0) - commonSheet c) + 0 = commonSheet c
  simp [hc]

theorem sheetMap_family_germ (H : Fin 4) :
    (fun p : Common × Triple => sheetMap (familyAxis H p)) =ᶠ[𝓝 0] familySheet H := by
  have ht : Filter.Tendsto (Prod.fst : Common × Triple → Common) (𝓝 0) (𝓝 0) := continuousAt_fst.tendsto
  filter_upwards [ht.eventually (Filter.eventually_all.2 familySheet_common_germ)] with p hp
  change commonSheet p.1 + ∑ J : Fin 4,
    (familySheet J (p.1, (Pi.single H p.2 : Blocks) J) - commonSheet p.1) + 0 = familySheet H p
  rw [Finset.sum_eq_single H]
  · simp
  · intro J _ hJ
    simp [hJ, hp J]
  · intro h; exact absurd (Finset.mem_univ H) h

theorem sheetMap_family_originalF_germ (H : Fin 4) :
    ∀ᶠ p in 𝓝 (0 : Common × Triple), normalResidual exactPhases (sheetMap (familyAxis H p)) = 0 := by
  filter_upwards [sheetMap_family_germ H, familySheet_originalF_germ H] with p hp hz
  rw [hp]; exact hz

/-- The chart derivative retains the actual common, Book, and normal-complement vectors. -/
theorem sheetMap_fderiv_native (c : Common) (z : Blocks) (e : Complement) :
    (fderiv ℝ sheetMap 0 ((c, z), e) : Cfg) = (c : Cfg) +
      (normalProjection (unpackNative (realV z)) : Cfg) + ((e : Normal) : Cfg) := by
  rw [sheetMap_derivative.hasFDerivAt.fderiv]
  change (sheetDerivative ((c, z), e) : Cfg) = _
  rw [sheetDerivative_apply]
  rfl

end Option2.NativeStress.BookHT.SheetReduction
#print axioms Option2.NativeStress.BookHT.SheetReduction.sheetPH
#print axioms Option2.NativeStress.BookHT.SheetReduction.sheetMap_fderiv_native
#print axioms Option2.NativeStress.BookHT.SheetReduction.sheetMap_family_originalF_germ

module

public import BookNativeSheetChart

@[expose] public section

/-! Actual range elimination in the simultaneous Book sheet chart, preserving all four sheets. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.BookHT.SheetReduction
open TangentCoordinates NativeNormalKernelBridge
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeSliceNormalSplitting CKM.NativeSliceImplicitReduction
open NativePolynomial QuadraticCertificate.ExactCKMConfiguration
open scoped Topology

abbrev ReducedCoordinates := KernelModel × normalRange exactPhases

def rangeSheetDerivative : Model ≃L[ℝ] ReducedCoordinates :=
  (ContinuousLinearEquiv.refl ℝ KernelModel).prodCongr (complementRangeEquiv exactPhases)

def rangeSheetMap (p : Model) : ReducedCoordinates :=
  (p.1, rangeProjection exactPhases (normalResidual exactPhases (sheetMap p)))

@[simp] theorem rangeSheetMap_zero : rangeSheetMap 0 = 0 := by
  simp [rangeSheetMap, normalResidual, originalF_literalCfg exactPhases exactPhases_unit]

theorem normalDerivative_common (c : Common) : normalDerivative exactPhases (commonNormal c) = 0 :=
  c.property.1.1.1

theorem normalDerivative_book (z : Blocks) : normalDerivative exactPhases (bookNormal z) = 0 :=
  (projectedBook z).property.1

theorem rangeDerivative_sheetDerivative (p : Model) :
    rangeDerivative exactPhases (sheetDerivative p) = complementRangeEquiv exactPhases p.2 := by
  apply Subtype.ext
  rw [coe_rangeDerivative, sheetDerivative_apply, map_add, map_add,
    normalDerivative_common, normalDerivative_book, zero_add, zero_add]
  exact (complementRangeEquiv_apply exactPhases p.2).symm

theorem rangeSheetMap_C2 : ContDiffAt ℝ 2 rangeSheetMap 0 := by
  have hf : ContDiffAt ℝ 2 (fun p : Model => normalResidual exactPhases (sheetMap p)) 0 :=
    (normalResidual_contDiff exactPhases 2).contDiffAt.comp 0 sheetMap_analytic.contDiffAt
  exact (ContinuousLinearMap.fst ℝ KernelModel Complement).contDiff.contDiffAt.prodMk
    ((rangeProjection exactPhases).contDiff.contDiffAt.comp 0 hf)

theorem rangeSheetMap_derivative : HasFDerivAt rangeSheetMap
    (rangeSheetDerivative : Model →L[ℝ] ReducedCoordinates) 0 := by
  have hf : HasFDerivAt (fun p : Model => normalResidual exactPhases (sheetMap p))
      ((normalDerivative exactPhases).comp sheetDerivative.toContinuousLinearMap) 0 := by
    have h : HasFDerivAt (normalResidual exactPhases) (normalDerivative exactPhases) (sheetMap 0) := by
      rw [sheetMap_zero]; exact normalResidual_hasFDerivAt exactPhases
    exact HasFDerivAt.comp (𝕜 := ℝ) (E := Model) (F := Normal) (G := Residual) 0 h
      sheetMap_derivative.hasFDerivAt
  have hp : HasFDerivAt (fun p : Model => rangeProjection exactPhases
      (normalResidual exactPhases (sheetMap p)))
      ((rangeProjection exactPhases).comp ((normalDerivative exactPhases).comp
        sheetDerivative.toContinuousLinearMap)) 0 :=
    HasFDerivAt.comp (𝕜 := ℝ) (E := Model) (F := Residual)
      (G := ↥(normalRange exactPhases)) 0
      (rangeProjection exactPhases).hasFDerivAt hf
  have hfst : HasFDerivAt (Prod.fst : Model → KernelModel)
      (ContinuousLinearMap.fst ℝ KernelModel Complement) 0 :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := Model) (F := KernelModel)
      (ContinuousLinearMap.fst ℝ KernelModel Complement)
  have hd := HasFDerivAt.prodMk (𝕜 := ℝ) (E := Model) (F := KernelModel)
    (G := ↥(normalRange exactPhases)) hfst hp
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro p
  change (p.1, rangeProjection exactPhases (normalDerivative exactPhases (sheetDerivative p))) =
    (p.1, complementRangeEquiv exactPhases p.2)
  rw [rangeProjection_normalDerivative, rangeDerivative_sheetDerivative]

def rangeSheetPH : OpenPartialHomeomorph Model ReducedCoordinates :=
  rangeSheetMap_C2.toOpenPartialHomeomorph rangeSheetMap rangeSheetMap_derivative (by norm_num)

@[simp] theorem rangeSheetPH_coe : ⇑rangeSheetPH = rangeSheetMap := rfl

theorem zero_mem_rangeSheetPH_source : (0 : Model) ∈ rangeSheetPH.source :=
  rangeSheetMap_C2.mem_toOpenPartialHomeomorph_source rangeSheetMap_derivative (by norm_num)

@[simp] theorem rangeSheetPH_zero : rangeSheetPH 0 = 0 := rangeSheetMap_zero

theorem zero_mem_rangeSheetPH_target : (0 : ReducedCoordinates) ∈ rangeSheetPH.target := by
  simpa only [rangeSheetPH_zero] using rangeSheetPH.map_source zero_mem_rangeSheetPH_source

@[simp] theorem rangeSheetPH_symm_zero : rangeSheetPH.symm 0 = 0 := by
  simpa only [rangeSheetPH_zero] using rangeSheetPH.left_inv zero_mem_rangeSheetPH_source

theorem rangeSheetPH_symm_C2 : ContDiffAt ℝ 2 rangeSheetPH.symm 0 := by
  apply OpenPartialHomeomorph.contDiffAt_symm (𝕜 := ℝ) (E := Model) (F := ReducedCoordinates)
    rangeSheetPH zero_mem_rangeSheetPH_target (f₀' := rangeSheetDerivative)
  · simpa only [rangeSheetPH_symm_zero, rangeSheetPH_coe] using rangeSheetMap_derivative
  · simpa only [rangeSheetPH_symm_zero, rangeSheetPH_coe] using rangeSheetMap_C2

theorem rangeSheetPH_symm_derivative : HasFDerivAt rangeSheetPH.symm
    (rangeSheetDerivative.symm : ReducedCoordinates →L[ℝ] Model) 0 := by
  apply OpenPartialHomeomorph.hasFDerivAt_symm (𝕜 := ℝ) (E := Model) (F := ReducedCoordinates)
    rangeSheetPH zero_mem_rangeSheetPH_target (f' := rangeSheetDerivative)
  simpa only [rangeSheetPH_symm_zero, rangeSheetPH_coe] using rangeSheetMap_derivative

/-- Genuine local coordinates on the actual normal space after range elimination. -/
def reducedPH : OpenPartialHomeomorph ReducedCoordinates Normal := rangeSheetPH.symm.trans sheetPH

@[simp] theorem reducedPH_apply (q : ReducedCoordinates) :
    reducedPH q = sheetMap (rangeSheetPH.symm q) := rfl

theorem zero_mem_reducedPH_source : (0 : ReducedCoordinates) ∈ reducedPH.source := by
  change 0 ∈ rangeSheetPH.target ∧ rangeSheetPH.symm 0 ∈ sheetPH.source
  exact ⟨zero_mem_rangeSheetPH_target, by rw [rangeSheetPH_symm_zero]; exact zero_mem_sheetPH_source⟩

@[simp] theorem reducedPH_zero : reducedPH 0 = 0 := by simp

def reducedEmbedding (x : KernelModel) : Normal := reducedPH (x, 0)
def sheetResidual (x : KernelModel) : Residual := normalResidual exactPhases (reducedEmbedding x)

@[simp] theorem reducedEmbedding_zero : reducedEmbedding 0 = 0 := by simp only [reducedEmbedding, Prod.mk_zero_zero, reducedPH_zero]
@[simp] theorem sheetResidual_zero : sheetResidual 0 = 0 := by
  simp [sheetResidual, normalResidual, originalF_literalCfg exactPhases exactPhases_unit]

theorem reducedEmbedding_C2 : ContDiffAt ℝ 2 reducedEmbedding 0 := by
  have hi : ContDiffAt ℝ 2 (fun x : KernelModel => (x, (0 : normalRange exactPhases))) 0 :=
    contDiff_id.contDiffAt.prodMk contDiff_const.contDiffAt
  have hs : ContDiffAt ℝ 2 (fun x : KernelModel => rangeSheetPH.symm (x, 0)) 0 :=
    rangeSheetPH_symm_C2.comp 0 (f := fun x : KernelModel => (x, (0 : normalRange exactPhases))) hi
  have hm : ContDiffAt ℝ 2 sheetMap (rangeSheetPH.symm ((0 : KernelModel), 0)) := by
    simp only [Prod.mk_zero_zero, rangeSheetPH_symm_zero]
    exact sheetMap_analytic.contDiffAt
  exact hm.comp 0 (f := fun x : KernelModel => rangeSheetPH.symm (x, 0)) hs

theorem sheetResidual_C2 : ContDiffAt ℝ 2 sheetResidual 0 :=
  (normalResidual_contDiff exactPhases 2).contDiffAt.comp 0 reducedEmbedding_C2

/-- On actual local coordinates, every original row vanishes exactly at range zero and reduced zero. -/
theorem originalF_zero_iff_sheet_coordinates (q : ReducedCoordinates)
    (hq : q ∈ rangeSheetPH.target) :
    Option2.NativeStress.AnalyticDerivative.originalF (literalCfg exactPhases + (reducedPH q : Cfg)) = 0 ↔
      q.2 = 0 ∧ sheetResidual q.1 = 0 := by
  have hi : rangeSheetMap (rangeSheetPH.symm q) = q := rangeSheetPH.right_inv hq
  constructor
  · intro hz
    have h2 : q.2 = 0 := by
      have hh := congrArg Prod.snd hi
      change rangeProjection exactPhases
        (Option2.NativeStress.AnalyticDerivative.originalF
          (literalCfg exactPhases + (reducedPH q : Cfg))) = q.2 at hh
      rw [hz, map_zero] at hh
      exact hh.symm
    refine ⟨h2, ?_⟩
    have hp : (q.1, (0 : normalRange exactPhases)) = q := Prod.ext rfl h2.symm
    simpa only [sheetResidual, normalResidual, reducedEmbedding, hp] using hz
  · rintro ⟨h2, hz⟩
    have hp : (q.1, (0 : normalRange exactPhases)) = q := Prod.ext rfl h2.symm
    simpa only [sheetResidual, normalResidual, reducedEmbedding, hp] using hz

theorem reducedEmbedding_range_zero (x : KernelModel)
    (hx : (x, (0 : normalRange exactPhases)) ∈ rangeSheetPH.target) :
    rangeProjection exactPhases (sheetResidual x) = 0 :=
  congrArg Prod.snd (rangeSheetPH.right_inv hx)

def embeddingDerivative : KernelModel →L[ℝ] Normal := commonNormal.coprod bookNormal

theorem reducedEmbedding_derivative : HasFDerivAt reducedEmbedding embeddingDerivative 0 := by
  let I : KernelModel →L[ℝ] ReducedCoordinates :=
    ContinuousLinearMap.inl ℝ KernelModel (normalRange exactPhases)
  have hs : HasFDerivAt (fun x : KernelModel => rangeSheetPH.symm (x, 0))
      (rangeSheetDerivative.symm.toContinuousLinearMap.comp I) 0 :=
    HasFDerivAt.comp (𝕜 := ℝ) (E := KernelModel) (F := ReducedCoordinates) (G := Model)
      0 rangeSheetPH_symm_derivative I.hasFDerivAt
  have hm : HasFDerivAt sheetMap sheetDerivative.toContinuousLinearMap
      (rangeSheetPH.symm ((0 : KernelModel), 0)) := by
    simpa only [Prod.mk_zero_zero, rangeSheetPH_symm_zero] using sheetMap_derivative.hasFDerivAt
  have hd := HasFDerivAt.comp (𝕜 := ℝ) (E := KernelModel) (F := Model) (G := Normal)
    (f := fun x : KernelModel => rangeSheetPH.symm (x, 0)) 0 hm hs
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro x
  change sheetDerivative (x, (complementRangeEquiv exactPhases).symm 0) = embeddingDerivative x
  rw [map_zero, sheetDerivative_apply]
  simp [embeddingDerivative]

/-- The first Book derivative is exactly the projected supplied realV, including native coordinates. -/
theorem reducedEmbedding_Book_derivative (z : Blocks) :
    (fderiv ℝ reducedEmbedding 0 (0, z) : Cfg) =
      (normalProjection (unpackNative (realV z)) : Cfg) := by
  rw [reducedEmbedding_derivative.fderiv]
  simp [embeddingDerivative, bookNormal]

theorem sheetResidual_derivative_zero : HasFDerivAt sheetResidual
    (0 : KernelModel →L[ℝ] Residual) 0 := by
  have hn : HasFDerivAt (normalResidual exactPhases) (normalDerivative exactPhases)
      (reducedEmbedding 0) := by rw [reducedEmbedding_zero]; exact normalResidual_hasFDerivAt exactPhases
  have hd := hn.comp 0 reducedEmbedding_derivative
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro x
  change normalDerivative exactPhases (commonNormal x.1 + bookNormal x.2) = 0
  rw [map_add, normalDerivative_common, normalDerivative_book, add_zero]

/-- Range elimination fixes the actual family axes as germs. -/
theorem eliminated_family_germ (H : Fin 4) :
    (fun p : Common × Triple => reducedEmbedding (p.1, Pi.single H p.2)) =ᶠ[𝓝 0] familySheet H := by
  have hsource : ∀ᶠ p in 𝓝 (0 : Common × Triple), familyAxis H p ∈ rangeSheetPH.source :=
    (familyAxis H).continuous.continuousAt.preimage_mem_nhds
      (by rw [map_zero]; exact rangeSheetPH.open_source.mem_nhds zero_mem_rangeSheetPH_source)
  filter_upwards [hsource, sheetMap_family_originalF_germ H, sheetMap_family_germ H] with p hp hz he
  have hm : rangeSheetPH (familyAxis H p) = ((p.1, (Pi.single H p.2 : Blocks)), 0) := by
    change ((p.1, (Pi.single H p.2 : Blocks)), rangeProjection exactPhases
      (normalResidual exactPhases (sheetMap (familyAxis H p)))) = _
    rw [hz, map_zero]
  change sheetMap (rangeSheetPH.symm ((p.1, Pi.single H p.2), 0)) = familySheet H p
  rw [← hm, rangeSheetPH.left_inv hp, he]

/-- Every one of the four actual native sheet germs survives range elimination. -/
theorem sheetResidual_family_zero (H : Fin 4) :
    ∀ᶠ p in 𝓝 (0 : Common × Triple), sheetResidual (p.1, Pi.single H p.2) = 0 := by
  filter_upwards [eliminated_family_germ H, familySheet_originalF_germ H] with p hp hz
  change normalResidual exactPhases (reducedEmbedding (p.1, Pi.single H p.2)) = 0
  rw [hp]; exact hz

/-- The nonlinear range change preserves the common and Book coordinates exactly. -/
theorem rangeSheetPH_symm_preserves_kernel (q : ReducedCoordinates)
    (hq : q ∈ rangeSheetPH.target) : (rangeSheetPH.symm q).1 = q.1 :=
  congrArg Prod.fst (rangeSheetPH.right_inv hq)

theorem reducedPH_C2 : ContDiffAt ℝ 2 reducedPH 0 := by
  have hm : ContDiffAt ℝ 2 sheetMap (rangeSheetPH.symm 0) := by
    rw [rangeSheetPH_symm_zero]; exact sheetMap_analytic.contDiffAt
  exact hm.comp 0 rangeSheetPH_symm_C2

theorem reducedPH_symm_C2 : ContDiffAt ℝ 2 reducedPH.symm 0 := by
  have hr : ContDiffAt ℝ 2 rangeSheetPH (sheetPH.symm 0) := by
    rw [sheetPH_symm_zero]; exact rangeSheetMap_C2
  exact hr.comp 0 sheetPH_symm_C2

theorem sheetResidual_C2_neighborhood :
    ∃ W ∈ 𝓝 (0 : KernelModel), ∀ x ∈ W, ContDiffAt ℝ 2 sheetResidual x :=
  ⟨{x | ContDiffAt ℝ 2 sheetResidual x}, sheetResidual_C2.eventually (by norm_num), fun _ hx => hx⟩

/-- Full original zeros on an actual normal neighborhood are precisely the reduced zeros. -/
theorem originalF_zero_iff_normal (n : Normal) (hn : n ∈ reducedPH.target) :
    Option2.NativeStress.AnalyticDerivative.originalF (literalCfg exactPhases + (n : Cfg)) = 0 ↔
      (reducedPH.symm n).2 = 0 ∧ sheetResidual (reducedPH.symm n).1 = 0 := by
  have hq : reducedPH.symm n ∈ reducedPH.source := reducedPH.map_target hn
  have hr : reducedPH.symm n ∈ rangeSheetPH.target := hq.1
  have he := originalF_zero_iff_sheet_coordinates (reducedPH.symm n) hr
  rwa [reducedPH.right_inv hn] at he

end Option2.NativeStress.BookHT.SheetReduction
#print axioms Option2.NativeStress.BookHT.SheetReduction.reducedPH
#print axioms Option2.NativeStress.BookHT.SheetReduction.originalF_zero_iff_sheet_coordinates
#print axioms Option2.NativeStress.BookHT.SheetReduction.reducedEmbedding_Book_derivative
#print axioms Option2.NativeStress.BookHT.SheetReduction.sheetResidual_family_zero

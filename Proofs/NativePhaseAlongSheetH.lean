module

public import HTPhaseCompleteHPack
public import BookNativeSheetHStress

@[expose] public section

/-! All-unit-phase H stresses along the actual native sheets. The anchor-preserving
raw family, followed by the specified inverse slice coordinate, supplies the field.
No conclusion about the full phase-supported-stress criterion is asserted here. -/
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace Option2.NativeStress.PhaseAlongSheetH
open CKM.NativeFirstOrder CKM.NativeFourFamily CKM.NativeGroupSlice
open NativePolynomial NativePolynomial.PartialAction
open AnchorSupport HTPhaseComplete AnalyticDerivative PolynomialJets MvPolynomial
open HTPhaseKron QuadraticCertificate.ExactCKMConfiguration
open scoped BigOperators Topology

theorem preCfg_anchor (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4)
    (g h : UnitaryErrorBases.Mat) (d : UnitaryErrorBases.PhaseTriple)
    (p : Fin 39) (hp : AnchorRowSupport.AnchorPoint i p) :
    preCfg ξ i g h d p = literalCfg ξ p := by
  rw [← preCfg_base hξ i]
  change upperCoordinates (prePoint ξ i g h d p) =
    upperCoordinates (prePoint ξ i 1 1 (anchorTriple ξ hξ i) p)
  unfold prePoint
  rw [stdAnchored, dite_eq_left (BookHT.SheetHStress.anchorRelabel_symm_lt i p hp),
    stdAnchored, dite_eq_left (BookHT.SheetHStress.anchorRelabel_symm_lt i p hp)]

/-- The transported configuration has the fixed-seed anchors even away from the
phase basepoint, because the actual raw family fixes each quartet state. -/
theorem raw_transported_anchor (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (i : Fin 4) (p : PreParam) (v : Fin 1053) (hv : AnchorCoordinate i v) :
    stateAct (invCartan (Ux ξ hξ) i)
      (fun w => ((PartialAction.pack (preMap ξ hξ i p) w : ℝ) : ℂ)) v = Pbase v := by
  apply Eq.trans ?_ (transported_anchor ξ hξ i v hv)
  have hp : AnchorRowSupport.AnchorPoint i ⟨v.val / 27, by omega⟩ := by
    change v.val / 27 / 3 = 0 ∨
      (1 + 3 * i.val ≤ v.val / 27 / 3 ∧ v.val / 27 / 3 ≤ 3 + 3 * i.val)
    unfold AnchorCoordinate at hv
    omega
  have he : preMap ξ hξ i p ⟨v.val / 27, by omega⟩ =
      literalCfg ξ ⟨v.val / 27, by omega⟩ :=
    preCfg_anchor ξ hξ i _ _ _ ⟨v.val / 27, by omega⟩ hp
  have hstate : unpackC (fun w => ((PartialAction.pack (preMap ξ hξ i p) w : ℝ) : ℂ))
      ⟨v.val / 27, by omega⟩ =
      unpackC (fun w => ((PartialAction.pack (literalCfg ξ) w : ℝ) : ℂ))
      ⟨v.val / 27, by omega⟩ := by
    funext c
    simp only [unpackC, PartialAction.pack]
    have hi : (27 * (v.val / 27) + c.val) / 27 = v.val / 27 := by omega
    have hj : (27 * (v.val / 27) + c.val) % 27 = c.val := by omega
    simp only [hi, hj]
    exact congrArg (fun q : Fin 27 → ℝ => (q c : ℂ)) he
  exact congrArg (fun q => invCartan (Ux ξ hξ) i q
    ⟨v.val % 27, Nat.mod_lt _ (by norm_num)⟩) hstate

theorem raw_quadratic_line (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (i : Fin 4) (a : Fin 3) (p : PreParam) (W : Fin 1053 → ℝ) (t : ℝ) :
    stressCovector (ellRaw ξ hξ i a)
      (Option2.NativeStress.originalF (PartialAction.pack (preMap ξ hξ i p) + t • W)) =
      (t : ℂ)^2 * eval (stateAct (invCartan (Ux ξ hξ) i) (fun v => (W v : ℂ)))
        (contractedQuadratic Pbase (NativeH.weightC i a)) := by
  rw [stressCovector_apply]
  have he : (∑ r, ellRaw ξ hξ i a r *
      (Option2.NativeStress.originalF (PartialAction.pack (preMap ξ hξ i p) + t • W) r : ℂ)) =
      contractedF (ellRaw ξ hξ i a)
        ((fun v => ((PartialAction.pack (preMap ξ hξ i p) v : ℝ) : ℂ)) + (t : ℂ) • fun v => (W v : ℂ)) := by
    unfold contractedF
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← eval_real_row]
    rw [show (fun v => (((PartialAction.pack (preMap ξ hξ i p) + t • W) v : ℝ) : ℂ)) =
      ((fun v => ((PartialAction.pack (preMap ξ hξ i p) v : ℝ) : ℂ)) + (t : ℂ) • fun v => (W v : ℂ))
      from by funext v; simp]
  rw [he, ellRaw, contractedF_transport, stateAct_add]
  exact contractedF_line_eq_quadratic_at_anchor Pbase (NativeH.weightC i a) i
    Pbase_solution (Pbase_equilibrium i a) (NativeH.hasAnchorSupport Pbase i a) _
    (raw_transported_anchor ξ hξ i p) _ (t : ℂ)

/-- Genuine all-column annihilation at every point of the native raw family,
not merely the derivative at its phase basepoint. -/
theorem raw_H_annihilates (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (i : Fin 4) (a : Fin 3) (p : PreParam) :
    (stressCovector (ellH ξ hξ i a)).comp
      (fderiv ℝ AnalyticDerivative.originalF (preMap ξ hξ i p)) = 0 := by
  have hraw := comp_fderiv_zero_of_lines _ originalF_ambient_differentiable
    (stressCovector (ellRaw ξ hξ i a)) (PartialAction.pack (preMap ξ hξ i p)) _
    (raw_quadratic_line ξ hξ i a p)
  have hpack : AnalyticDerivative.originalF = Option2.NativeStress.originalF ∘ packCLM := rfl
  rw [hpack, fderiv_comp _ (originalF_ambient_differentiable _)
    packCLM.differentiableAt, packCLM.fderiv]
  change (stressCovector (fun r => mono (Ux ξ hξ) (HTPhaseKron.Ex.neg (cExp i a)) *
    ellRaw ξ hξ i a r)).comp _ = 0
  rw [stressCovector_smul, ContinuousLinearMap.smul_comp,
    ← ContinuousLinearMap.comp_assoc, packCLM_apply, hraw, ContinuousLinearMap.zero_comp]
  ext v
  simp

def rawSlice (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) (p : SliceParam) : Cfg :=
  preMap ξ hξ i (p.1, 0, p.2)

def groupCoordinate (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) (p : SliceParam) : derC :=
  ((slicePH ξ hξ).symm (rawSlice ξ hξ i p)).1

def componentField (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) (a : Fin 3)
    (p : SliceParam) : RealResiduals →L[ℝ] ℂ :=
  (stressCovector (ellH ξ hξ i a)).comp (rowAction (groupChart (groupCoordinate ξ hξ i p)))

@[simp] theorem rawSlice_zero (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) :
    rawSlice ξ hξ i 0 = literalCfg ξ := preMap_zero hξ i

@[simp] theorem groupCoordinate_zero (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) :
    groupCoordinate ξ hξ i 0 = 0 := by
  simp [groupCoordinate, slicePH_symm_literalCfg]

@[simp] theorem componentField_zero (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) (a : Fin 3) :
    componentField ξ hξ i a 0 = stressCovector (ellH ξ hξ i a) := by
  rw [componentField, groupCoordinate_zero, groupChart_zero, rowAction_one]
  rfl

theorem rawSlice_analytic (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) :
    AnalyticAt ℝ (rawSlice ξ hξ i) 0 := by
  let J : SliceParam →L[ℝ] PreParam :=
    (ContinuousLinearMap.fst ℝ (Fin 8 → ℝ) (Fin 2 → ℝ)).prod
      ((0 : SliceParam →L[ℝ] (Fin 8 → ℝ)).prod
        (ContinuousLinearMap.snd ℝ (Fin 8 → ℝ) (Fin 2 → ℝ)))
  exact (analyticAt_preMap hξ i).comp_of_eq (J.analyticAt 0) (map_zero J)

theorem componentField_analytic (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) (a : Fin 3) :
    AnalyticAt ℝ (componentField ξ hξ i a) 0 := by
  have hg : AnalyticAt ℝ (groupCoordinate ξ hξ i) 0 :=
    analyticAt_fst.comp ((analyticAt_slicePH_symm ξ hξ).comp_of_eq
      (rawSlice_analytic ξ hξ i) (rawSlice_zero ξ hξ i))
  exact ((ContinuousLinearMap.compL ℝ RealResiduals RealResiduals ℂ
    (stressCovector (ellH ξ hξ i a))).analyticAt _).comp
      ((analyticAt_rowAction _).comp ((analyticAt_groupChart _).comp hg))

theorem componentField_annihilates (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (i : Fin 4) (a : Fin 3) (p : SliceParam)
    (hp : rawSlice ξ hξ i p ∈ (slicePH ξ hξ).target) :
    (componentField ξ hξ i a p).comp
      (fderiv ℝ AnalyticDerivative.originalF (literalCfg ξ + (sliceFam ξ hξ i p : Cfg))) = 0 := by
  have he : rawSlice ξ hξ i p = actC (groupChart (groupCoordinate ξ hξ i p))
      (literalCfg ξ + (sliceFam ξ hξ i p : Cfg)) := ((slicePH ξ hξ).right_inv hp).symm
  have hn := raw_H_annihilates ξ hξ i a (p.1, 0, p.2)
  change (stressCovector (ellH ξ hξ i a)).comp
    (fderiv ℝ AnalyticDerivative.originalF (rawSlice ξ hξ i p)) = 0 at hn
  rw [he] at hn
  ext v
  have hc := congrArg (fun L : Cfg →L[ℝ] RealResiduals => L v)
    (BookHT.SheetHStress.derivative_covariance
      (groupChart_mem_autC (groupCoordinate ξ hξ i p))
      (literalCfg ξ + (sliceFam ξ hξ i p : Cfg)))
  simp only [ContinuousLinearMap.comp_apply] at hc
  change stressCovector (ellH ξ hξ i a)
    (rowAction (groupChart (groupCoordinate ξ hξ i p))
      (fderiv ℝ AnalyticDerivative.originalF (literalCfg ξ + (sliceFam ξ hξ i p : Cfg)) v)) = 0
  rw [← hc]
  exact congrArg (fun L : Cfg →L[ℝ] ℂ => L (actC (groupChart (groupCoordinate ξ hξ i p)) v)) hn

/-- One genuine parameter neighborhood carries continuous fields with full
ambient annihilation. Neither good-phase rank nor a reproduction premise is needed. -/
theorem along_sheet_H_fields (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) :
    ∃ V : Set SliceParam, IsOpen V ∧ (0 : SliceParam) ∈ V ∧
      ∀ a : Fin 3, ContinuousOn (componentField ξ hξ i a) V ∧
        (∀ p ∈ V, (componentField ξ hξ i a p).comp
          (fderiv ℝ AnalyticDerivative.originalF (literalCfg ξ + (sliceFam ξ hξ i p : Cfg))) = 0) ∧
        componentField ξ hξ i a 0 = stressCovector (ellH ξ hξ i a) := by
  have ht : ∀ᶠ p in 𝓝 (0 : SliceParam), rawSlice ξ hξ i p ∈ (slicePH ξ hξ).target :=
    (rawSlice_analytic ξ hξ i).continuousAt.preimage_mem_nhds (by
      rw [rawSlice_zero]
      exact (slicePH ξ hξ).open_target.mem_nhds (literalCfg_mem_slicePH_target ξ hξ))
  have hc : ∀ᶠ p in 𝓝 (0 : SliceParam), ∀ a : Fin 3,
      ContinuousAt (componentField ξ hξ i a) p :=
    Filter.eventually_all.mpr (fun a => (componentField_analytic ξ hξ i a).eventually_analyticAt.mono
      (fun _ h => h.continuousAt))
  obtain ⟨V, hV, hVo, hV0⟩ := mem_nhds_iff.mp (ht.and hc)
  refine ⟨V, hVo, hV0, fun a => ⟨?_, ?_, componentField_zero ξ hξ i a⟩⟩
  · intro p hp
    exact ((hV hp).2 a).continuousWithinAt
  · intro p hp
    exact componentField_annihilates ξ hξ i a p (hV hp).1

end Option2.NativeStress.PhaseAlongSheetH

#print axioms Option2.NativeStress.PhaseAlongSheetH.raw_H_annihilates
#print axioms Option2.NativeStress.PhaseAlongSheetH.along_sheet_H_fields

module

public import BookNativeSheetReduction

@[expose] public section

/-! Exact native common/four-family germ identities before and after residual-range elimination.
The neighborhood-image helper is reused from the accepted first-party A5Chart construction. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.BookHT.SheetReduction
open TangentCoordinates NativeNormalKernelBridge
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeSliceNormalSplitting CKM.NativeSliceImplicitReduction
open NativePolynomial QuadraticCertificate.ExactCKMConfiguration
open Filter Topology

private theorem germImage_of_native_param {X Y Z P : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace P]
    (Φ : OpenPartialHomeomorph X Y) {a : X} (ha : a ∈ Φ.source) (B : Set X)
    (j : Z → X) (π : X → Z) (h : Z → P) (g : P → Y) {z₀ : Z} {p : P}
    (hj : ContinuousAt j z₀) (hja : j z₀ = a) (hjB : ∀ z, j z ∈ B)
    (hπ : ContinuousAt π a) (hπa : π a = z₀) (hπB : ∀ x ∈ B, j (π x) = x)
    (hh : ContinuousAt h z₀) (hhp : h z₀ = p) (hopen : ∀ W ∈ 𝓝 z₀, h '' W ∈ 𝓝 p)
    (hg : ∀ᶠ z in 𝓝 z₀, g (h z) = Φ (j z)) :
    IsGermImage (Φ '' (Φ.source ∩ B)) (Φ a) g p := by
  set W : Set Z := {z | j z ∈ Φ.source ∧ g (h z) = Φ (j z)} with hWdef
  have hW : W ∈ 𝓝 z₀ := by
    have h1 : ∀ᶠ z in 𝓝 z₀, j z ∈ Φ.source :=
      hj.preimage_mem_nhds (by rw [hja]; exact Φ.open_source.mem_nhds ha)
    exact h1.and hg
  refine ⟨h '' W, hopen W hW, fun U hU hUW => ?_⟩
  rw [Filter.eventuallyEqSet_iff]
  have hN : ∀ᶠ y in 𝓝 (Φ a), y ∈ Φ.target ∧ π (Φ.symm y) ∈ W ∩ h ⁻¹' U := by
    refine Filter.Eventually.and (Φ.open_target.mem_nhds (Φ.map_source ha)) ?_
    have hc : ContinuousAt (fun y => π (Φ.symm y)) (Φ a) := by
      refine ContinuousAt.comp (f := Φ.symm) (g := π) ?_ (Φ.continuousAt_symm (Φ.map_source ha))
      rw [Φ.left_inv ha]; exact hπ
    refine hc.preimage_mem_nhds ?_
    rw [Φ.left_inv ha, hπa]
    exact Filter.inter_mem hW (hh.preimage_mem_nhds (by rw [hhp]; exact hU))
  filter_upwards [hN] with y hy
  constructor
  · rintro ⟨x, hxU, rfl⟩
    obtain ⟨z, hzW, rfl⟩ := hUW hxU
    exact ⟨j z, ⟨hzW.1, hjB z⟩, hzW.2.symm⟩
  · rintro ⟨x, ⟨hxs, hxB⟩, rfl⟩
    have hx : Φ.symm (Φ x) = x := Φ.left_inv hxs
    have h2 := hy.2
    rw [hx] at h2
    refine ⟨h (π x), h2.2, ?_⟩
    rw [h2.1.2, hπB x hxB]

def nativeCommonBlock (R : Type*) [Zero R] : Set (KernelModel × R) :=
  {q | q.1.2 = 0 ∧ q.2 = 0}
def nativeFamilyBlock (R : Type*) [Zero R] (H : Fin 4) : Set (KernelModel × R) :=
  {q | (∀ J, J ≠ H → q.1.2 J = 0) ∧ q.2 = 0}

private theorem common_germ_from_param {R : Type*}
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (Φ : OpenPartialHomeomorph (KernelModel × R) Normal)
    (h0 : (0 : KernelModel × R) ∈ Φ.source) (hz : Φ 0 = 0)
    (hc : (fun c : Common => Φ ((c, 0), 0)) =ᶠ[𝓝 0] commonSheet) :
    IsGermImage (Φ '' (Φ.source ∩ nativeCommonBlock R)) 0
      (sliceCommon exactPhases exactPhases_unit) 0 := by
  rw [← hz]
  refine germImage_of_native_param Φ h0 _
    (fun c : Common => (((c, 0), 0) : KernelModel × R))
    (fun q => q.1.1) commonLinearEquiv.symm (sliceCommon exactPhases exactPhases_unit)
    (by fun_prop) rfl (fun _ => ⟨rfl, rfl⟩) (by fun_prop) rfl ?_
    commonLinearEquiv.symm.continuous.continuousAt (map_zero _) ?_ hc.symm
  · rintro q ⟨h1, h2⟩
    exact Prod.ext (Prod.ext rfl h1.symm) h2.symm
  · intro W hW
    have hh := commonLinearEquiv.symm.hasStrictFDerivAt.map_nhds_eq_of_equiv (a := (0 : Common))
    rw [map_zero] at hh
    rw [← hh]
    exact Filter.image_mem_map hW

private theorem family_germ_from_param {R : Type*}
    [NormedAddCommGroup R] [NormedSpace ℝ R]
    (Φ : OpenPartialHomeomorph (KernelModel × R) Normal)
    (h0 : (0 : KernelModel × R) ∈ Φ.source) (hz : Φ 0 = 0) (H : Fin 4)
    (hf : (fun p : Common × Triple => Φ ((p.1, Pi.single H p.2), 0)) =ᶠ[𝓝 0] familySheet H) :
    IsGermImage (Φ '' (Φ.source ∩ nativeFamilyBlock R H)) 0
      (sliceFam exactPhases exactPhases_unit H) 0 := by
  rw [← hz]
  have hd : HasStrictFDerivAt (familyParam H) (familyParamEquiv H : (Common × Triple) →L[ℝ] SliceParam) 0 :=
    (familyParam_analytic H).hasStrictFDerivAt
  refine germImage_of_native_param Φ h0 _
    (fun p : Common × Triple => (((p.1, Pi.single H p.2), 0) : KernelModel × R))
    (fun q => (q.1.1, q.1.2 H)) (familyParam H) (sliceFam exactPhases exactPhases_unit H)
    ((continuous_fst.prodMk
      ((ContinuousLinearMap.single ℝ (fun _ : Fin 4 => Triple) H).continuous.comp continuous_snd)).prodMk
      continuous_const).continuousAt ?_ (fun _ => ⟨fun J hJ => by simp [hJ], rfl⟩) (by fun_prop) rfl ?_
    hd.continuousAt (familyParam_zero H) ?_ hf.symm
  · ext <;> simp
  · rintro q ⟨h1, h2⟩
    refine Prod.ext (Prod.ext rfl (funext fun J => ?_)) h2.symm
    by_cases hJ : J = H
    · subst J; simp
    · simp [hJ, h1 J hJ]
  · intro W hW
    have hh := hd.map_nhds_eq_of_equiv
    rw [familyParam_zero] at hh
    rw [← hh]
    exact Filter.image_mem_map hW

theorem sheetPH_common_native_germ :
    IsGermImage (sheetPH '' (sheetPH.source ∩ nativeCommonBlock Complement)) 0
      (sliceCommon exactPhases exactPhases_unit) 0 :=
by
  apply common_germ_from_param (R := ↥Complement) sheetPH zero_mem_sheetPH_source sheetPH_zero
  convert sheetMap_common_germ using 1
  rw [sheetPH_coe]
  rfl

theorem sheetPH_family_native_germ (H : Fin 4) :
    IsGermImage (sheetPH '' (sheetPH.source ∩ nativeFamilyBlock Complement H)) 0
      (sliceFam exactPhases exactPhases_unit H) 0 :=
by
  apply family_germ_from_param (R := ↥Complement) sheetPH zero_mem_sheetPH_source sheetPH_zero H
  convert sheetMap_family_germ H using 1
  rw [sheetPH_coe]
  rfl

theorem eliminated_common_germ :
    (fun c : Common => reducedEmbedding (c, 0)) =ᶠ[𝓝 0] commonSheet := by
  have ht : Tendsto (fun c : Common => (c, (0 : Triple))) (𝓝 0) (𝓝 0) :=
    (continuous_id.prodMk continuous_const).continuousAt.tendsto
  filter_upwards [ht.eventually (eliminated_family_germ 0), familySheet_common_germ 0] with c hc hs
  simpa using hc.trans hs

theorem reducedPH_common_native_germ :
    IsGermImage (reducedPH '' (reducedPH.source ∩ nativeCommonBlock (normalRange exactPhases))) 0
      (sliceCommon exactPhases exactPhases_unit) 0 :=
  common_germ_from_param reducedPH zero_mem_reducedPH_source reducedPH_zero eliminated_common_germ

theorem reducedPH_family_native_germ (H : Fin 4) :
    IsGermImage (reducedPH '' (reducedPH.source ∩ nativeFamilyBlock (normalRange exactPhases) H)) 0
      (sliceFam exactPhases exactPhases_unit H) 0 :=
  family_germ_from_param reducedPH zero_mem_reducedPH_source reducedPH_zero H (eliminated_family_germ H)

theorem reducedResidual_common_zero :
    ∀ᶠ c in 𝓝 (0 : Common), sheetResidual (c, 0) = 0 := by
  have ht : Tendsto (fun c : Common => (c, (0 : Triple))) (𝓝 0) (𝓝 0) :=
    (continuous_id.prodMk continuous_const).continuousAt.tendsto
  simpa using ht.eventually (sheetResidual_family_zero 0)

/-- A neighborhood on which the actual initial chart and its inverse are both C². -/
theorem sheetPH_C2_neighborhood :
    ∀ᶠ p in 𝓝 (0 : Model), p ∈ sheetPH.source ∧
      ContDiffAt ℝ 2 sheetPH p ∧ ContDiffAt ℝ 2 sheetPH.symm (sheetPH p) := by
  have ht : Tendsto sheetPH (𝓝 (0 : Model)) (𝓝 (0 : Normal)) := by
    simpa only [sheetPH_zero] using sheetPH_C2.continuousAt.tendsto
  exact Filter.Eventually.and (sheetPH.open_source.mem_nhds zero_mem_sheetPH_source)
    ((sheetPH_C2.eventually (by norm_num)).and
      (ht.eventually (sheetPH_symm_C2.eventually (by norm_num))))

/-- A neighborhood on which the actual reduced chart and its inverse are both C². -/
theorem reducedPH_C2_neighborhood :
    ∀ᶠ q in 𝓝 (0 : ReducedCoordinates), q ∈ reducedPH.source ∧
      ContDiffAt ℝ 2 reducedPH q ∧ ContDiffAt ℝ 2 reducedPH.symm (reducedPH q) := by
  have ht : Tendsto reducedPH (𝓝 (0 : ReducedCoordinates)) (𝓝 (0 : Normal)) := by
    simpa only [reducedPH_zero] using reducedPH_C2.continuousAt.tendsto
  exact Filter.Eventually.and (reducedPH.open_source.mem_nhds zero_mem_reducedPH_source)
    ((reducedPH_C2.eventually (by norm_num)).and
      (ht.eventually (reducedPH_symm_C2.eventually (by norm_num))))

end Option2.NativeStress.BookHT.SheetReduction
#print axioms Option2.NativeStress.BookHT.SheetReduction.sheetPH_family_native_germ
#print axioms Option2.NativeStress.BookHT.SheetReduction.reducedPH_common_native_germ
#print axioms Option2.NativeStress.BookHT.SheetReduction.reducedPH_family_native_germ

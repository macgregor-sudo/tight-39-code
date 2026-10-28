module

public import HTPhaseCompleteGeometry

@[expose] public section

/-!
Full raw tangent coordinates at good phases, preserving the actual Book map Vxi.
The orbit correction occurs only in the surjectivity proof; the forward map is
exactly o+c+unpackNative(Vxi z), with no normal projection on its Book component.
The raw-family geometry is imported.
No H/T values, mixed terms, Laurent coefficients or uniform bounds are asserted.
-/

noncomputable section
set_option maxRecDepth 2000
namespace Option2.NativeStress.PhaseRawBookA6
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open HTPhaseComplete BookHT
open BookHT.NativeNormalKernelBridge (unpackNative axisParameters finrank_blocks_real)

abbrev Common (ξ : Fin 4 → ℂ) := orbitC ξ × fixQK ξ
abbrev Model (ξ : Fin 4 → ℂ) := Common ξ × Blocks

theorem unpack_Vxi_mem_tangent {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (z : Blocks) :
    unpackNative (Vxi ξ hξ z) ∈ tangentSpace ξ := by
  rw [← phaseV_eq_Vxi, unpack_phaseV]
  exact familyDirection_mem_tangent hξ z

/-- The actual raw ambient map; the Book component is not projected. -/
def rawBookAmbient {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) : Model ξ →L[ℝ] Cfg :=
  ((orbitC ξ).subtypeL.coprod (fixQK ξ).subtypeL).coprod (unpackNative.comp (Vxi ξ hξ))

def rawBookMap {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) : Model ξ →L[ℝ] tangentSpace ξ :=
  (rawBookAmbient hξ).codRestrict (tangentSpace ξ) (by
    rintro ⟨⟨o,c⟩,z⟩
    exact (tangentSpace ξ).add_mem
      ((tangentSpace ξ).add_mem (klin_orbitC_le hξ o.property) c.property.1.1.1)
      (unpack_Vxi_mem_tangent hξ z))

theorem rawBookMap_coe {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ)
    (o : orbitC ξ) (c : fixQK ξ) (z : Blocks) :
    (rawBookMap hξ ((o,c),z) : Cfg) =
      (o : Cfg) + (c : Cfg) + unpackNative (Vxi ξ hξ z) := rfl

/-- The normal component of the raw map is exactly the proved normal Book equivalence. -/
theorem rawBookMap_project {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (o : orbitC ξ) (c : fixQK ξ) (z : Blocks) :
    (normalProjXi ξ hξ.1 (rawBookMap hξ.1 ((o,c),z) : Cfg) : Cfg) =
      (bookPhaseEquiv hξ (c,z) : Cfg) := by
  have ho : normalProjXi ξ hξ.1 (o : Cfg) = 0 :=
    (normalProj_eq_zero_iff hξ.1 _).mpr o.property
  have hc : normalProjXi ξ hξ.1 (c : Cfg) = ⟨c, c.property.1.1.2⟩ :=
    normalProj_normal hξ.1 ⟨c, c.property.1.1.2⟩
  rw [rawBookMap_coe, map_add, map_add, ho, zero_add, hc,
    bookPhaseEquiv_apply, phaseV_eq_Vxi]
  rfl

theorem rawBookMap_injective {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    Function.Injective (rawBookMap hξ.1) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  rintro ⟨⟨o,c⟩,z⟩ hp
  have he : (bookPhaseEquiv hξ (c,z) : Cfg) = 0 := by
    rw [← rawBookMap_project hξ o c z, hp]
    simp
  have hcz : (c,z) = (0 : fixQK ξ × Blocks) := by
    apply (bookPhaseEquiv hξ).injective
    exact (Subtype.ext he).trans (map_zero _).symm
  have hc : c = 0 := congrArg Prod.fst hcz
  have hz : z = 0 := congrArg Prod.snd hcz
  subst c
  subst z
  have ho : o = 0 := by
    apply Subtype.ext
    have h := congrArg Subtype.val hp
    simpa only [rawBookMap_coe, Submodule.coe_zero, map_zero, add_zero] using h
  exact Prod.ext (Prod.ext ho rfl) rfl

/-- The orbit correction is (x−Πx)−(Vxi z−ΠVxi z), preserving the raw Vxi forward map. -/
theorem rawBookMap_surjective {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    Function.Surjective (rawBookMap hξ.1) := by
  intro x
  let n : tanN ξ := ⟨(normalProjXi ξ hξ.1 (x : Cfg) : Cfg),
    normalProj_mem_tangent hξ.1 x.property, (normalProjXi ξ hξ.1 (x : Cfg)).property⟩
  obtain ⟨⟨c,z⟩, he⟩ := (bookPhaseEquiv hξ).surjective n
  let v := unpackNative (Vxi ξ hξ.1 z)
  have hcz : (c : Cfg) + (normalProjXi ξ hξ.1 v : Cfg) =
      (normalProjXi ξ hξ.1 (x : Cfg) : Cfg) := by
    have h := congrArg Subtype.val he
    rw [bookPhaseEquiv_apply, phaseV_eq_Vxi] at h
    exact h
  let o : orbitC ξ := ⟨(x : Cfg) - (normalProjXi ξ hξ.1 (x : Cfg) : Cfg) -
      (v - (normalProjXi ξ hξ.1 v : Cfg)),
    (orbitC ξ).sub_mem (sub_normalProj_mem_orbit hξ.1 (x : Cfg))
      (sub_normalProj_mem_orbit hξ.1 v)⟩
  refine ⟨((o,c),z), Subtype.ext ?_⟩
  rw [rawBookMap_coe]
  change ((x : Cfg) - (normalProjXi ξ hξ.1 (x : Cfg) : Cfg) -
    (v - (normalProjXi ξ hξ.1 v : Cfg))) + (c : Cfg) + v = (x : Cfg)
  calc
    _ = (x : Cfg) - (normalProjXi ξ hξ.1 (x : Cfg) : Cfg) +
        ((c : Cfg) + (normalProjXi ξ hξ.1 v : Cfg)) := by abel
    _ = _ := by rw [hcz]; abel

/-- Actual good-phase continuous-linear equivalence onto the FULL tangent kernel. -/
def rawBookEquiv {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) : Model ξ ≃L[ℝ] tangentSpace ξ :=
  (LinearEquiv.ofBijective (rawBookMap hξ.1).toLinearMap
    ⟨rawBookMap_injective hξ, rawBookMap_surjective hξ⟩).toContinuousLinearEquiv

theorem rawBookEquiv_coe {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (o : orbitC ξ) (c : fixQK ξ) (z : Blocks) :
    (rawBookEquiv hξ ((o,c),z) : Cfg) =
      (o : Cfg) + (c : Cfg) + unpackNative (Vxi ξ hξ.1 z) := rfl

theorem rawBookEquiv_common {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (o : orbitC ξ) (c : fixQK ξ) :
    (rawBookEquiv hξ ((o,c),0) : Cfg) = (o : Cfg) + (c : Cfg) := by
  rw [rawBookEquiv_coe, map_zero, map_zero, add_zero]

theorem rawBookEquiv_book {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (z : Blocks) :
    (rawBookEquiv hξ ((0,0),z) : Cfg) = unpackNative (Vxi ξ hξ.1 z) := by
  rw [rawBookEquiv_coe]
  simp only [Submodule.coe_zero, zero_add]

theorem rawBookEquiv_axis {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (H : Fin 4) (u : Triple) :
    (rawBookEquiv hξ ((0,0),Pi.single H u) : Cfg) =
      preDer ξ hξ.1 H (axisParameters H u, axisParameters H u, 0) := by
  rw [rawBookEquiv_book, ← phaseV_eq_Vxi, unpack_phaseV, familyDirection_single]

theorem finrank_common {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    Module.finrank ℝ (Common ξ) = 56 := by
  change Module.finrank ℝ (orbitC ξ × fixQK ξ) = 56
  rw [Module.finrank_prod, finrank_orbitC ξ hξ.1, finrank_fixQK hξ]

theorem finrank_model {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    Module.finrank ℝ (Model ξ) = 80 := by
  change Module.finrank ℝ (Common ξ × Blocks) = 80
  rw [Module.finrank_prod, finrank_common hξ, finrank_blocks_real]

end Option2.NativeStress.PhaseRawBookA6

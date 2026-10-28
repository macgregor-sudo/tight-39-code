module

public import NativePhaseRawBook

@[expose] public section

/-! Actual family-range membership of raw common-plus-Book-axis directions.
The correction is an exhibited orbit direction, without any H/T value claim. -/

noncomputable section
set_option maxRecDepth 2000
namespace Option2.NativeStress.PhaseRawBookA6
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open HTPhaseComplete BookHT
open BookHT.NativeNormalKernelBridge (unpackNative)

theorem rawBook_axis_mem_rawDer_range {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (H : Fin 4) (o : orbitC ξ) (c : fixQK ξ) (u : Triple) :
    (rawBookEquiv hξ ((o,c),Pi.single H u) : Cfg) ∈
      LinearMap.range (rawDer ξ hξ.1 H).toLinearMap := by
  obtain ⟨φ, hφ⟩ := axis_slice_binding hξ H
  let p := φ (c,u)
  let v : Cfg := rawBookEquiv hξ ((o,c),Pi.single H u)
  let q : Cfg := preDer ξ hξ.1 H (p.1,0,p.2)
  have hq : (normalProjXi ξ hξ.1 q : Cfg) =
      (c : Cfg) + (normalProjXi ξ hξ.1 (unpackNative (Vxi ξ hξ.1 (Pi.single H u))) : Cfg) := by
    have h := hφ c u
    rw [sliceFamDer_apply] at h
    exact h
  have hv : (normalProjXi ξ hξ.1 v : Cfg) =
      (c : Cfg) + (normalProjXi ξ hξ.1 (unpackNative (Vxi ξ hξ.1 (Pi.single H u))) : Cfg) := by
    have h := rawBookMap_project hξ o c (Pi.single H u)
    rw [bookPhaseEquiv_apply, phaseV_eq_Vxi] at h
    exact h
  have hproj : normalProjXi ξ hξ.1 v = normalProjXi ξ hξ.1 q :=
    Subtype.ext (hv.trans hq.symm)
  have hd : v-q ∈ orbitC ξ :=
    (normalProj_eq_zero_iff hξ.1 _).mp (by rw [map_sub, hproj, sub_self])
  obtain ⟨D, hD, hDv⟩ := hd
  refine ⟨(⟨D,hD⟩,(p.1,0,p.2)), ?_⟩
  change rawDer ξ hξ.1 H (⟨D,hD⟩,(p.1,0,p.2)) = v
  rw [rawDer_apply hξ.1 H]
  change orbitMapC ξ D + q = v
  exact (eq_sub_iff_add_eq).mp hDv

end Option2.NativeStress.PhaseRawBookA6

module

public import A5SliceB
public import A5Chart

@[expose] public section

/-!
# The simultaneous slice chart (piece SCHART)

Apply `exists_simultaneous_chart` in `E = N` (dimension 1001) with `fC = sliceCommon`
(`Pc = ℝ⁴`), `m H = sliceFam H` (`M = ℝ⁸ × ℝ²`), `ψ` from `exists_slice_inclusion`, `U = ℝ⁶`,
`R = ℝ⁹⁷³`. The transversality hypothesis is `dim (Σ_H Q^H) = 28 = 4 + 4·6` (`range_sliceFamDer`,
`iSup_fixQ`, `finrank_tanN`).
-/

noncomputable section

open CKM.NativeFirstOrder CKM.NativeGroupSlice CompactAlbert UnitaryErrorBases
open scoped Matrix Topology

namespace CKM.NativeFourFamily

/-- One analytic chart `ℝ⁴ × (ℝ⁶)⁴ × ℝ⁹⁷³ → N` straightening the four ten-dimensional slice family
germs to the blocks `ℝ⁴ × ℝ⁶_H` and the common four-dimensional germ to `ℝ⁴`. -/
theorem exists_slice_chart {ξ₀ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ₀) :
    ∃ Φ : OpenPartialHomeomorph SliceModel ↥(normalC ξ₀),
      (0 : SliceModel) ∈ Φ.source ∧ Φ 0 = 0 ∧
      AnalyticOnNhd ℝ Φ Φ.source ∧ AnalyticOnNhd ℝ Φ.symm Φ.target ∧
      IsGermImage (Φ '' (Φ.source ∩ commonBlock (Fin 4) (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ))) 0
        (sliceCommon ξ₀ hξ.1) 0 ∧
      (∀ H, IsGermImage (Φ '' (Φ.source ∩ familyBlock (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H)) 0
        (sliceFam ξ₀ hξ.1 H) 0) ∧
      (∀ H H', H ≠ H' →
        Φ '' (Φ.source ∩ familyBlock (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H) ∩
            Φ '' (Φ.source ∩ familyBlock (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ) H') =
          Φ '' (Φ.source ∩ commonBlock (Fin 4) (Fin 4 → ℝ) (Fin 6 → ℝ) (Fin 973 → ℝ))) := by
  have hψ := fun H => exists_slice_inclusion hξ.1 H
  let ψ : Fin 4 → (Fin 4 → ℝ) → SliceParam := fun H => Classical.choose (hψ H)
  have hψs : ∀ H, AnalyticAt ℝ (ψ H) 0 ∧ ψ H 0 = 0 ∧
      ∀ᶠ θ in 𝓝 (0 : Fin 4 → ℝ), sliceFam ξ₀ hξ.1 H (ψ H θ) = sliceCommon ξ₀ hξ.1 θ :=
    fun H => Classical.choose_spec (hψ H)
  -- transversality: the four tangent images span `T ∩ N`, of dimension `28 = 4 + 4 · 6`
  have hmap : (⨆ H, LinearMap.range
      ((sliceFamDer ξ₀ hξ.1 H : SliceParam →L[ℝ] ↥(normalC ξ₀)) :
        SliceParam →ₗ[ℝ] ↥(normalC ξ₀))).map (normalC ξ₀).subtype = tanN ξ₀ := by
    rw [Submodule.map_iSup]
    simp_rw [range_sliceFamDer hξ]
    exact iSup_fixQ hξ.1
  have h28 : Module.finrank ℝ ↥(⨆ H, LinearMap.range
      ((sliceFamDer ξ₀ hξ.1 H : SliceParam →L[ℝ] ↥(normalC ξ₀)) :
        SliceParam →ₗ[ℝ] ↥(normalC ξ₀))) = 28 := by
    rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (normalC ξ₀).subtype
      Subtype.val_injective _), hmap, finrank_tanN hξ]
  have hdimU : Module.finrank ℝ (Fin 4 → ℝ) + Module.finrank ℝ (Fin 6 → ℝ) =
      Module.finrank ℝ SliceParam := by
    simp [Module.finrank_prod]
  have hdimR : Module.finrank ℝ (Fin 4 → ℝ) + Fintype.card (Fin 4) * Module.finrank ℝ (Fin 6 → ℝ) +
      Module.finrank ℝ (Fin 973 → ℝ) = Module.finrank ℝ ↥(normalC ξ₀) := by
    rw [finrank_normalC ξ₀ hξ.1]
    simp
  have htrans : Module.finrank ℝ ↥(⨆ H, LinearMap.range
      ((sliceFamDer ξ₀ hξ.1 H : SliceParam →L[ℝ] ↥(normalC ξ₀)) :
        SliceParam →ₗ[ℝ] ↥(normalC ξ₀))) =
      Module.finrank ℝ (Fin 4 → ℝ) + Fintype.card (Fin 4) * Module.finrank ℝ (Fin 6 → ℝ) := by
    rw [h28]
    simp
  obtain ⟨Φ, h0, hΦ0, hA, hAs, hC, hF, hI⟩ :=
    exists_simultaneous_chart (ι := Fin 4) (U := Fin 6 → ℝ) (R := Fin 973 → ℝ)
      (sliceCommon ξ₀ hξ.1) (sliceFam ξ₀ hξ.1) ψ (sliceCommonDer ξ₀ hξ.1) (sliceFamDer ξ₀ hξ.1)
      (analyticAt_sliceCommon hξ.1) (hasStrictFDerivAt_sliceCommon hξ.1)
      (sliceCommonDer_injective hξ.1) (analyticAt_sliceFam hξ.1) (hasStrictFDerivAt_sliceFam hξ.1)
      (sliceFamDer_injective hξ.1) (fun H => (hψs H).1) (fun H => (hψs H).2.1)
      (fun H => (hψs H).2.2) hdimU hdimR htrans
  rw [sliceCommon_zero hξ.1] at hΦ0 hC hF
  exact ⟨Φ, h0, hΦ0, hA, hAs, hC, hF, hI⟩

end CKM.NativeFourFamily

#print axioms CKM.NativeFourFamily.exists_slice_chart

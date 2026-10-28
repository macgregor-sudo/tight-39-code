module

public import NativePhasePivot
public import A3Main
public import MatrixRankSpecialization

@[expose] public section

noncomputable section
namespace Option2.NativeStress.PhaseRankA6
open PhasePivotA6 CKM.NativeFirstOrder
open NativePolynomial NativePolynomial.ConfigurationResiduals
open PolynomialJets QuarticCertificate.PipelineNaturality
open scoped BigOperators

/-- The exact original translated-row Jacobian before complexification. -/
def realJ (ξ : Fin 4 → ℂ) : Matrix (Fin 2184) (Fin 1053) ℝ :=
  Matrix.of fun r c => equationLinearMatrix
    (fun r => translate (PartialAction.pack (literalCfg ξ)) (fRow (1/2 : ℝ) (1/3 : ℝ) r)) r c

/-- Literal1053 packing, with its actual inverse in39×27 coordinates. -/
def packEquiv : PartialAction.Configuration ℝ ≃ₗ[ℝ] (Fin 1053 → ℝ) where
  toFun := PartialAction.pack
  invFun v i k := v (ConfigurationResiduals.variableIndex i k)
  left_inv C := by
    funext i k
    exact PartialAction.pack_variableIndex C i k
  right_inv v := by
    funext n
    change v (ConfigurationResiduals.variableIndex ⟨n.val/27,by omega⟩ ⟨n.val%27,by omega⟩) = v n
    congr 1
    apply Fin.ext
    rw [ConfigurationResiduals.variableIndex_val]
    change 27 * (n.val/27) + n.val%27 = n.val
    omega
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem packEquiv_apply (u : PartialAction.Configuration ℝ) : packEquiv u = PartialAction.pack u := rfl

 theorem mem_ker_realJ (ξ : Fin 4 → ℂ) (u : PartialAction.Configuration ℝ) :
    packEquiv u ∈ LinearMap.ker (realJ ξ).mulVecLin ↔ u ∈ tangentSpace ξ := by
  rw [tangentSpace,mem_ker_fderiv_originalF_iff_linearCoefficients]
  rw [LinearMap.mem_ker,funext_iff]
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, realJ, Matrix.of_apply,
    packEquiv_apply, Pi.zero_apply]

def tangentKernelEquiv (ξ : Fin 4 → ℂ) :
    tangentSpace ξ ≃ₗ[ℝ] LinearMap.ker (realJ ξ).mulVecLin :=
  packEquiv.ofSubmodules _ _ (by
    ext v
    rw [Submodule.mem_map_equiv]
    exact (mem_ker_realJ ξ (packEquiv.symm v)).symm.trans
      (by rw [packEquiv.apply_symm_apply]))

 theorem realJ_rank_nullity (ξ : Fin 4 → ℂ) :
    (realJ ξ).rank + Module.finrank ℝ (tangentSpace ξ) = 1053 := by
  rw [(tangentKernelEquiv ξ).finrank_eq]
  have h := (realJ ξ).mulVecLin.finrank_range_add_finrank_ker
  simpa only [Matrix.rank, Module.finrank_pi, Fintype.card_fin] using h

 theorem realJ_rank_le (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : (realJ ξ).rank ≤ 973 := by
  have h := realJ_rank_nullity ξ
  rw [finrank_tangentSpace ξ hξ] at h
  omega

/-- Every entry is the faithful real-to-complex image of the SAME original row. -/
 theorem realJ_map_complex (ξ : Fin 4 → ℂ) :
    (realJ ξ).map Complex.ofRealHom = nativeJ ξ := by
  ext r c
  change Complex.ofRealHom (equationLinearMatrix
    (fun r => translate (PartialAction.pack (literalCfg ξ)) (fRow (1/2 : ℝ) (1/3 : ℝ) r)) r c) = _
  rw [map_equationLinearMatrix]
  simp only [PolynomialJets.map_translate, FourSheets.PointBridge.Rows.map_fRow,
    map_div₀, map_one, map_ofNat]
  rfl

/-- Scalar extension rank equality is proved from determinant specialization in
both directions. Real and complex kernel dimensions are never identified. -/
 theorem nativeJ_rank_eq_real (ξ : Fin 4 → ℂ) : (nativeJ ξ).rank = (realJ ξ).rank := by
  rw [← realJ_map_complex]
  have hid : (realJ ξ).map (RingHom.id ℝ) = realJ ξ := by ext r c; rfl
  apply le_antisymm
  · have h := Matrix.rank_map_le_rank_map_of_injective (realJ ξ) Complex.ofRealHom
      (RingHom.id ℝ) Function.injective_id
    rw [hid] at h
    exact h
  · have h := Matrix.rank_map_le_rank_map_of_injective (realJ ξ) (RingHom.id ℝ)
      Complex.ofRealHom Complex.ofReal_injective
    rw [hid] at h
    exact h

/-- All unit phases, including every resonance. -/
 theorem nativeJ_rank_le (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Matrix.rank (PhasePivotA6.nativeJ ξ) ≤ 973 := by
  rw [nativeJ_rank_eq_real]
  exact realJ_rank_le ξ hξ

#print axioms Option2.NativeStress.PhaseRankA6.nativeJ_rank_le
end Option2.NativeStress.PhaseRankA6

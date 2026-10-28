module

public import NativePhaseNormalForm
public import EuclideanUpperBoundActual

@[expose] public section

/-! Dimension upper bound for the complete native normal zero germ. Each
closed model sheet has the actual Common/axis inherited norm and linear
dimension ten; finite closed sum and the exact nonlinear zero homeomorphism
transfer the bound to all sufficiently small prescribed normal neighborhoods. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.PhaseNormalDimension
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeSliceNormalSplitting CKM.NativeSliceImplicitReduction
open BookHT PhaseSheetChart PhaseRangeReduction PhaseNormalForm
open Topology Set
variable {ξ : Fin 4 → ℂ}

/-- One complete linear sheet of the native zero model. -/
def sheetSpace (ξ : Fin 4 → ℂ) (i : Fin 4) : Submodule ℝ (ReducedCoordinates ξ) where
  carrier := {q | q.2 = 0 ∧ FourBlock.OnAxis i q.1.2}
  zero_mem' := ⟨rfl,by intro j hj; rfl⟩
  add_mem' := by
    intro q r hq hr
    refine ⟨by simp only [Prod.fst_add,Prod.snd_add,hq.1,hr.1,add_zero],?_⟩
    intro j hj
    simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,hq.2 j hj,hr.2 j hj,add_zero]
  smul_mem' := by
    intro a q hq
    constructor
    · change a • q.2 = 0
      rw [hq.1,smul_zero]
    · intro j hj
      change a • q.1.2 j = 0
      rw [hq.2 j hj,smul_zero]

/-- Actual common-plus-axis coordinates on each model sheet. -/
def sheetEquiv (ξ : Fin 4 → ℂ) (i : Fin 4) :
    (Common ξ × axisSpace i) ≃ₗ[ℝ] sheetSpace ξ i where
  toFun p := ⟨((p.1,p.2.1),0),rfl,p.2.2⟩
  invFun q := (q.1.1.1,⟨q.1.1.2,q.2.2⟩)
  left_inv p := rfl
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact q.2.1.symm
  map_add' p q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (zero_add _).symm
  map_smul' a p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (smul_zero a).symm

theorem sheet_finrank (hξ : IsGoodPhase ξ) (i : Fin 4) :
    Module.finrank ℝ (sheetSpace ξ i) = 10 := by
  rw [← (sheetEquiv ξ i).finrank_eq]
  exact sheet_model_finrank hξ i

theorem sheet_dimension_le (hξ : IsGoodPhase ξ) (i : Fin 4) :
    HasSmallInductiveDimensionLE (sheetSpace ξ i) 10 := by
  let e : sheetSpace ξ i ≃L[ℝ] (Fin 10 → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := sheetSpace ξ i) (F := Fin 10 → ℝ) (by rw [sheet_finrank hξ i,Module.finrank_fin_fun])
  exact e.toHomeomorph.isInducing.hasSmallInductiveDimensionLE
    (SmallInductiveEuclideanA7.pi_smallInductiveDimensionLE
      SmallInductiveEuclideanA7.finiteClosedSumContract_proved 10)

/-- The full union, with its inherited native norm topology, has ind≤10. -/
theorem zero_model_dimension_le (hξ : IsGoodPhase ξ) :
    HasSmallInductiveDimensionLE ↥(zeroModel ξ) 10 := by
  let F : Fin 4 → Set (zeroModel ξ) := fun i => Subtype.val ⁻¹' (sheetSpace ξ i : Set _)
  have hFc (i : Fin 4) : IsClosed (F i) :=
    (Submodule.closed_of_finiteDimensional (sheetSpace ξ i)).preimage continuous_subtype_val
  have hFd (i : Fin 4) : HasSmallInductiveDimensionLE ↥(F i) 10 :=
    SmallInductiveClosedSum.subtype_preimage_dimension_le (zeroModel ξ) (sheetSpace ξ i) 10
      (sheet_dimension_le hξ i)
  apply SmallInductiveClosedSum.finite_closed_sum 10 F hFc hFd
  apply eq_univ_of_forall
  intro q
  obtain ⟨i,hi⟩ := q.2.2
  exact mem_iUnion.mpr ⟨i,q.2.1,hi⟩

/-- Complete native original-equation zero neighborhoods have dimension at most
ten. Every smaller prescribed open neighborhood retains the bound. -/
theorem normal_zero_dimension_le (hξ : IsGoodPhase ξ) : ∃ δ : ℝ, 0 < δ ∧
    ∀ V : Set (Normal ξ), IsOpen V → (0 : Normal ξ) ∈ V → V ⊆ Metric.ball 0 δ →
      HasSmallInductiveDimensionLE ↥(V ∩ nativeZeros ξ) 10 := by
  obtain ⟨δ,hδ,hchart⟩ := normal_form_homeomorph hξ
  refine ⟨δ,hδ,?_⟩
  intro V hV hV0 hsmall
  obtain ⟨_,_,_,_,e,_,_⟩ := hchart V hV hV0 hsmall
  have hsource : HasSmallInductiveDimensionLE ↥(chartDomain hξ V ∩ zeroModel ξ) 10 :=
    (Topology.IsInducing.id.restrict (show MapsTo id (chartDomain hξ V ∩ zeroModel ξ)
      (zeroModel ξ) from inter_subset_right)).hasSmallInductiveDimensionLE
        (zero_model_dimension_le hξ)
  exact e.symm.isInducing.hasSmallInductiveDimensionLE hsource

end Option2.NativeStress.PhaseNormalDimension
#print axioms Option2.NativeStress.PhaseNormalDimension.normal_zero_dimension_le

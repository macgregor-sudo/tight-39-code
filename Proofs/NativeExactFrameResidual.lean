module

public import GSResidual
public import EFLiteral

@[expose] public section

/-! Native original-residual control on the canonical exact-frame locus.
All 2184 original rows, original half/third normalization and native coordinate
sup norm are retained. No relabelling or residual-zero premise is introduced. -/
set_option Elab.async false
noncomputable section
namespace CKM.NativeOverlapLossHook
open Glennie NativePolynomial CKM.NativeGroupSlice CKM.NativeTightCode
open CKM.NativeExactFrameEnergy SupportedStress.NativeFrames
open ConfigurationResiduals ConfigurationResidualIndices CoordinateMaps
open Option2.NativeStress.AnalyticDerivative

/-- The actual thirteen canonical labelled native frames. -/
def ExactFrames (y : Cfg) : Prop :=
  ∀ h, Frame (framesOf literalLabel (codePoint y) h)

private theorem coords_point (y : Cfg) (i : Fin 39) :
    y i = upperCoordinates (codePoint y i) := by
  exact (upperCoordinates_fromUpperCoordinates (y i)).symm

private theorem pairing_points (y : Cfg) (i j : Fin 39) :
    coordinatePairing (y i) (y j) = inner (codePoint y i) (codePoint y j) := by
  rw [coords_point y i,coords_point y j,coordinatePairing_upperCoordinates_eq_native_trace]
  rfl

private theorem frame_point (y : Cfg) (i : Fin 39) :
    framesOf literalLabel (codePoint y) (literalLabel i).1 (literalLabel i).2 = codePoint y i := by
  simp only [framesOf,Prod.mk.eta,Equiv.symm_apply_apply]

private theorem point_pure (y : Cfg) (hy : ExactFrames y) (i : Fin 39) :
    IsPure (codePoint y i) := by
  have hi := (hy (literalLabel i).1).idempotent (literalLabel i).2
  have ht := (hy (literalLabel i).1).trace_one (literalLabel i).2
  rw [frame_point] at hi ht
  exact ⟨hi,ht⟩

private theorem coord_idempotent (y : Cfg) (hy : ExactFrames y) (i : Fin 39) :
    coordinateProduct (1/2 : ℝ) (y i) (y i) = y i := by
  rw [← prodC_apply,coords_point y i,prodC_upperCoordinates,(point_pure y hy i).1]

private theorem coord_trace (y : Cfg) (hy : ExactFrames y) (i : Fin 39) :
    coordinateTrace (y i) = 1 := by
  have ht : coordinateTrace (y i) = trace (codePoint y i) := by
    rw [coordinateTrace_apply]
    rfl
  exact ht.trans (point_pure y hy i).2

private theorem coord_sum (y : Cfg) (hy : ExactFrames y) (f : Fin 13) :
    ∑ a : Fin 3, y (framePointIndex f a) = (coordinateUnit : Fin 27 → ℝ) := by
  have hunit : upperCoordinateEquiv (1 : Albert) = (coordinateUnit : Fin 27 → ℝ) := by
    funext k
    fin_cases k <;> rfl
  have hs : ∑ a : Fin 3, y (framePointIndex f a) =
      upperCoordinateEquiv (∑ a : Fin 3, codePoint y (framePointIndex f a)) := by
    rw [map_sum]
    simp only [codePoint,LinearEquiv.apply_symm_apply]
  rw [hs,← hunit,upperCoordinateEquiv.injective.eq_iff,Fin.sum_univ_three]
  exact (hy f).sum_unit

private theorem within_pair_zero (y : Cfg) (hy : ExactFrames y) {i j : Fin 39}
    (hij : i ≠ j) (hblock : i.val / 3 = j.val / 3) :
    inner (codePoint y i) (codePoint y j) = 0 := by
  have hb : (literalLabel i).1 = (literalLabel j).1 := Fin.ext hblock
  have ha : (literalLabel i).2 ≠ (literalLabel j).2 :=
    fun h => hij (literalLabel.injective (Prod.ext hb h))
  have ho := (hy (literalLabel i).1).orthogonal (literalLabel i).2 (literalLabel j).2 ha
  have hj : framesOf literalLabel (codePoint y) (literalLabel i).1 (literalLabel j).2 =
      codePoint y j := by rw [hb]; exact frame_point y j
  rw [frame_point,hj] at ho
  unfold Glennie.inner
  rw [ho]
  simp [Glennie.trace]

private theorem square_le_sum_squares {ι : Type*} [Fintype ι] (f : ι → ℝ) (i : ι) :
    (f i)^2 ≤ ∑ j, (f j)^2 :=
  Finset.single_le_sum (fun j _ => sq_nonneg (f j)) (Finset.mem_univ i)

private theorem cross_pair_sq_le (y : Cfg) (ij : Pair 39)
    (hne : ij.1.1.val / 3 ≠ ij.1.2.val / 3) :
    (inner (codePoint y ij.1.1) (codePoint y ij.1.2) - 1/3)^2 ≤
      D (framesOf literalLabel (codePoint y)) := by
  have hlt : (literalLabel ij.1.1).1 < (literalLabel ij.1.2).1 := by
    change ij.1.1.val / 3 < ij.1.2.val / 3
    have hh := ij.2
    change ij.1.1.val < ij.1.2.val at hh
    omega
  let k : ThirteenCrossPair :=
    (⟨((literalLabel ij.1.1).1,(literalLabel ij.1.2).1),hlt⟩,
      ((literalLabel ij.1.1).2,(literalLabel ij.1.2).2))
  have he : thirteenCrossOverlap (framesOf literalLabel (codePoint y)) k =
      inner (codePoint y ij.1.1) (codePoint y ij.1.2) := by
    change trace (jordan
      (framesOf literalLabel (codePoint y) (literalLabel ij.1.1).1 (literalLabel ij.1.1).2)
      (framesOf literalLabel (codePoint y) (literalLabel ij.1.2).1 (literalLabel ij.1.2).2)) = _
    rw [frame_point,frame_point]
    rfl
  have h := square_le_sum_squares
    (fun l => thirteenCrossOverlap (framesOf literalLabel (codePoint y)) l - 1/3) k
  rw [he] at h
  exact h

/-- Every original row is bounded by the actual squared cross defect. -/
theorem originalF_row_sq_le_cross_defect (y : Cfg) (hy : ExactFrames y) (r : Fin 2184) :
    (originalF y r)^2 ≤ D (framesOf literalLabel (codePoint y)) := by
  have hD : 0 ≤ D (framesOf literalLabel (codePoint y)) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold originalF
  rw [PartialAction.eval_fRow]
  rcases fNumber.symm r with ⟨i,k⟩ | i | ⟨f,k⟩ | ij
  · simp only [PartialAction.originalValue,coord_idempotent y hy,sub_self,zero_pow (by decide : 2 ≠ 0)]
    exact hD
  · simp only [PartialAction.originalValue,coord_trace y hy,sub_self,zero_pow (by decide : 2 ≠ 0)]
    exact hD
  · have hs := congrFun (coord_sum y hy f) k
    simp only [Finset.sum_apply] at hs
    simp only [PartialAction.originalValue,hs,sub_self,zero_pow (by decide : 2 ≠ 0)]
    exact hD
  · simp only [PartialAction.originalValue,pairing_points]
    by_cases hb : ij.1.1.val / 3 = ij.1.2.val / 3
    · rw [if_pos hb,within_pair_zero y hy (ne_of_lt ij.2) hb,sub_self,zero_pow (by decide : 2 ≠ 0)]
      exact hD
    · rw [if_neg hb]
      exact cross_pair_sq_le y ij hb

/-- The native finite-Pi sup norm satisfies the requested bound with b=1. -/
theorem originalF_norm_sq_le_cross_defect (y : Cfg) (hy : ExactFrames y) :
    ‖originalF y‖^2 ≤ D (framesOf literalLabel (codePoint y)) := by
  have hD : 0 ≤ D (framesOf literalLabel (codePoint y)) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : ‖originalF y‖ ≤ Real.sqrt (D (framesOf literalLabel (codePoint y))) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro r
    rw [Real.norm_eq_abs]
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs,Real.sq_sqrt hD]
    exact originalF_row_sq_le_cross_defect y hy r
  have hs := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hb
  rwa [Real.sq_sqrt hD] at hs

end CKM.NativeOverlapLossHook
#print axioms CKM.NativeOverlapLossHook.originalF_norm_sq_le_cross_defect

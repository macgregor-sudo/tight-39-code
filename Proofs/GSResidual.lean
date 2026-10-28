module

public import GSSlice

@[expose] public section

/-!
# Equivariance of all 2184 original residuals, off shell

`F = originalF` (accepted; all 2184 rows, literal constants `1/2` and `1/3`, existing numbering
`fNumber`: idempotency rows `27 i + k`, trace rows `1053 + i`, frame-sum rows `1092 + 27 f + k`,
pair-overlap rows `1443 + lexRank (i, j)`).

* `rowAction A`: the row action on residual vectors; it applies `A` to each 27-row block of the
  idempotency and frame-sum vector blocks and is the identity on the trace and pair-overlap scalar
  rows (`rowAction_id`, `rowAction_sum`, `rowAction_trace`, `rowAction_pair`).
* `originalF_actC`: for every `A ∈ G` and **every** configuration `C`,
  `F (A • C) = rowAction A (F C)` (vector equality, not only zero sets). Route: per block, the
  accepted `PartialAction.eval_fRow`, `prodC` = native product, `A` fixes the unit, preserves the
  coordinate trace and the pairing (`GSGroup`).
* `rowAction` is multiplicative and unital; for `A ∈ G` it is invertible with inverse
  `rowAction (Ring.inverse A)`; it depends analytically (affinely) on `A`.
* `originalF_sliceChart`, `originalF_sliceChart_eq_zero_iff`: the zero-set product
  `F(Θ(D, n)) = 0 ↔ F(P + n) = 0`.
-/

noncomputable section

namespace CKM.NativeGroupSlice

open Glennie NativePolynomial CKM.NativeFirstOrder ConfigurationResidualIndices
open Option2.NativeStress.AnalyticDerivative (originalF)

/-- The row action on one typed residual label. -/
def rowActionLabel (A : CEnd) (y : Fin 2184 → ℝ) : FLabel → ℝ
  | .inl (i, k) => A (fun k' => y (fNumber (fId i k'))) k
  | .inr (.inl i) => y (fNumber (fTrace i))
  | .inr (.inr (.inl (f, k))) => A (fun k' => y (fNumber (fSum f k'))) k
  | .inr (.inr (.inr ij)) => y (fNumber (fPair ij))

/-- Additivity of the row action on one label (helper). -/
theorem res_rowActionLabel_add (A : CEnd) (y z : Fin 2184 → ℝ) (q : FLabel) :
    rowActionLabel A (y + z) q = rowActionLabel A y q + rowActionLabel A z q := by
  rcases q with ⟨i, k⟩ | i | ⟨f, k⟩ | ij
  · change A ((fun k' => y (fNumber (fId i k'))) + (fun k' => z (fNumber (fId i k')))) k = _
    rw [map_add]
    rfl
  · rfl
  · change A ((fun k' => y (fNumber (fSum f k'))) + (fun k' => z (fNumber (fSum f k')))) k = _
    rw [map_add]
    rfl
  · rfl

/-- Homogeneity of the row action on one label (helper). -/
theorem res_rowActionLabel_smul (A : CEnd) (c : ℝ) (y : Fin 2184 → ℝ) (q : FLabel) :
    rowActionLabel A (c • y) q = c * rowActionLabel A y q := by
  rcases q with ⟨i, k⟩ | i | ⟨f, k⟩ | ij
  · change A (c • (fun k' => y (fNumber (fId i k')))) k = _
    rw [map_smul]
    rfl
  · rfl
  · change A (c • (fun k' => y (fNumber (fSum f k')))) k = _
    rw [map_smul]
    rfl
  · rfl

/-- The row action on the 2184 original residual coordinates. -/
def rowAction (A : CEnd) : (Fin 2184 → ℝ) →L[ℝ] (Fin 2184 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y r => rowActionLabel A y (fNumber.symm r)
      map_add' := fun y z => funext fun r => res_rowActionLabel_add A y z (fNumber.symm r)
      map_smul' := fun c y => funext fun r => res_rowActionLabel_smul A c y (fNumber.symm r) }

/-- Unfolding the row action at a typed label (helper). -/
theorem rowAction_fNumber (A : CEnd) (y : Fin 2184 → ℝ) (q : FLabel) :
    rowAction A y (fNumber q) = rowActionLabel A y q := by
  change rowActionLabel A y (fNumber.symm (fNumber q)) = _
  rw [Equiv.symm_apply_apply]

theorem rowAction_id (A : CEnd) (y : Fin 2184 → ℝ) (i : Fin 39) (k : Fin 27) :
    rowAction A y (fNumber (fId i k)) = A (fun k' => y (fNumber (fId i k'))) k := by
  rw [rowAction_fNumber]
  rfl

theorem rowAction_trace (A : CEnd) (y : Fin 2184 → ℝ) (i : Fin 39) :
    rowAction A y (fNumber (fTrace i)) = y (fNumber (fTrace i)) := by
  rw [rowAction_fNumber]
  rfl

theorem rowAction_sum (A : CEnd) (y : Fin 2184 → ℝ) (f : Fin 13) (k : Fin 27) :
    rowAction A y (fNumber (fSum f k)) = A (fun k' => y (fNumber (fSum f k'))) k := by
  rw [rowAction_fNumber]
  rfl

theorem rowAction_pair (A : CEnd) (y : Fin 2184 → ℝ) (ij : Pair 39) :
    rowAction A y (fNumber (fPair ij)) = y (fNumber (fPair ij)) := by
  rw [rowAction_fNumber]
  rfl

theorem rowAction_one : rowAction 1 = 1 := by
  refine ContinuousLinearMap.ext fun y => funext fun r => ?_
  obtain ⟨q, rfl⟩ := fNumber.surjective r
  rcases q with ⟨i, k⟩ | i | ⟨f, k⟩ | ij
  · exact rowAction_id 1 y i k
  · exact rowAction_trace 1 y i
  · exact rowAction_sum 1 y f k
  · exact rowAction_pair 1 y ij

theorem rowAction_mul (A B : CEnd) : rowAction (A * B) = rowAction A * rowAction B := by
  refine ContinuousLinearMap.ext fun y => funext fun r => ?_
  obtain ⟨q, rfl⟩ := fNumber.surjective r
  rw [mul_apply_eq_comp]
  rcases q with ⟨i, k⟩ | i | ⟨f, k⟩ | ij
  · change rowAction (A * B) y (fNumber (fId i k)) = rowAction A (rowAction B y) (fNumber (fId i k))
    simp only [rowAction_id, mul_apply_eq_comp]
  · change rowAction (A * B) y (fNumber (fTrace i)) =
      rowAction A (rowAction B y) (fNumber (fTrace i))
    simp only [rowAction_trace]
  · change rowAction (A * B) y (fNumber (fSum f k)) =
      rowAction A (rowAction B y) (fNumber (fSum f k))
    simp only [rowAction_sum, mul_apply_eq_comp]
  · change rowAction (A * B) y (fNumber (fPair ij)) =
      rowAction A (rowAction B y) (fNumber (fPair ij))
    simp only [rowAction_pair]

theorem rowAction_inverse {A : CEnd} (hA : A ∈ autC) :
    rowAction A * rowAction (Ring.inverse A) = 1 ∧ rowAction (Ring.inverse A) * rowAction A = 1 := by
  obtain ⟨h₁, h₂⟩ := mul_inverse_of_mem_autOf hA
  exact ⟨by rw [← rowAction_mul, h₁, rowAction_one], by rw [← rowAction_mul, h₂, rowAction_one]⟩

/-- The linear part `A ↦ rowAction A - rowAction 0` of the affine map `rowAction` (helper). -/
private def res_rowLin : CEnd →ₗ[ℝ] ((Fin 2184 → ℝ) →L[ℝ] (Fin 2184 → ℝ)) where
  toFun A := rowAction A - rowAction 0
  map_add' A B := by
    refine ContinuousLinearMap.ext fun y => funext fun r => ?_
    obtain ⟨q, rfl⟩ := fNumber.surjective r
    rcases q with ⟨i, k⟩ | i | ⟨f, k⟩ | ij <;>
      simp only [sub_apply, add_apply, Pi.sub_apply,
        Pi.add_apply, rowAction_fNumber, rowActionLabel, zero_apply,
        Pi.zero_apply] <;> ring
  map_smul' c A := by
    refine ContinuousLinearMap.ext fun y => funext fun r => ?_
    obtain ⟨q, rfl⟩ := fNumber.surjective r
    rcases q with ⟨i, k⟩ | i | ⟨f, k⟩ | ij <;>
      simp only [sub_apply, smul_apply, Pi.sub_apply,
        Pi.smul_apply, rowAction_fNumber, rowActionLabel, zero_apply,
        Pi.zero_apply, RingHom.id_apply, smul_eq_mul] <;> ring

theorem analyticAt_rowAction (A : CEnd) : AnalyticAt ℝ rowAction A := by
  have h : rowAction = fun B => LinearMap.toContinuousLinearMap res_rowLin B + rowAction 0 := by
    funext B
    change rowAction B = (rowAction B - rowAction 0) + rowAction 0
    rw [sub_add_cancel]
  rw [h]
  exact (ContinuousLinearMap.analyticAt _ _).add analyticAt_const

/-- **Off-shell equivariance of all original residuals.** -/
theorem originalF_actC {A : CEnd} (hA : A ∈ autC) (C : Cfg) :
    originalF (actC A C) = rowAction A (originalF C) := by
  have hF : ∀ (X : Cfg) (q : FLabel),
      originalF X (fNumber q) = PartialAction.originalValue (1 / 2 : ℝ) (1 / 3 : ℝ) X q := by
    intro X q
    change MvPolynomial.eval (PartialAction.pack X)
      (ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) (fNumber q)) = _
    rw [PartialAction.eval_fRow, Equiv.symm_apply_apply]
  funext r
  obtain ⟨q, rfl⟩ := fNumber.surjective r
  rw [rowAction_fNumber, hF]
  rcases q with ⟨i, k⟩ | i | ⟨f, k⟩ | ij
  · have hfun : (fun k' => originalF C (fNumber (fId i k'))) = prodC (C i) (C i) - C i := by
      funext k'
      rw [hF, prodC_apply]
      rfl
    change _ = A (fun k' => originalF C (fNumber (fId i k'))) k
    rw [hfun, map_sub, hA.2, prodC_apply]
    simp only [PartialAction.originalValue, actC_apply, Pi.sub_apply]
  · change _ = originalF C (fNumber (fTrace i))
    rw [hF]
    simp only [fTrace, PartialAction.originalValue, actC_apply, autC_trace hA]
  · have hfun : (fun k' => originalF C (fNumber (fSum f k'))) =
        (∑ a : Fin 3, C (ConfigurationResiduals.framePointIndex f a)) -
          CoordinateMaps.coordinateUnit := by
      funext k'
      rw [hF]
      simp only [fSum, PartialAction.originalValue, Pi.sub_apply, Finset.sum_apply]
    change _ = A (fun k' => originalF C (fNumber (fSum f k'))) k
    rw [hfun, map_sub, map_sum, autC_unit hA]
    simp only [PartialAction.originalValue, actC_apply, Pi.sub_apply, Finset.sum_apply]
  · change _ = originalF C (fNumber (fPair ij))
    rw [hF]
    simp only [fPair, PartialAction.originalValue, actC_apply, autC_pairing hA]

theorem originalF_actC_eq_zero_iff {A : CEnd} (hA : A ∈ autC) (C : Cfg) :
    originalF (actC A C) = 0 ↔ originalF C = 0 := by
  rw [originalF_actC hA]
  constructor
  · intro h
    have h₂ := (rowAction_inverse hA).2
    calc originalF C = (rowAction (Ring.inverse A) * rowAction A) (originalF C) := by rw [h₂]; rfl
      _ = rowAction (Ring.inverse A) (rowAction A (originalF C)) := rfl
      _ = 0 := by rw [h, map_zero]
  · intro h
    rw [h, map_zero]

/-- The vector form along the product chart. -/
theorem originalF_sliceChart (ξ : Fin 4 → ℂ) (p : derC × normalC ξ) :
    originalF (sliceChart ξ p) = rowAction (groupChart p.1) (originalF (literalCfg ξ + p.2)) := by
  exact originalF_actC (groupChart_mem_autC p.1) _

/-- **Local zero-set product:** `F(Θ(D, n)) = 0 ↔ F(P + n) = 0`. -/
theorem originalF_sliceChart_eq_zero_iff (ξ : Fin 4 → ℂ) (p : derC × normalC ξ) :
    originalF (sliceChart ξ p) = 0 ↔ originalF (literalCfg ξ + p.2) = 0 := by
  exact originalF_actC_eq_zero_iff (groupChart_mem_autC p.1) _

/-- The literal configuration is a zero of all 2184 original rows at every unit phase. -/
theorem originalF_literalCfg (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : originalF (literalCfg ξ) = 0 := by
  exact funext fun r => literalCfg_all_original_F ξ hξ r

end CKM.NativeGroupSlice

#print axioms CKM.NativeGroupSlice.rowAction
#print axioms CKM.NativeGroupSlice.rowAction_fNumber
#print axioms CKM.NativeGroupSlice.rowAction_id
#print axioms CKM.NativeGroupSlice.rowAction_trace
#print axioms CKM.NativeGroupSlice.rowAction_sum
#print axioms CKM.NativeGroupSlice.rowAction_pair
#print axioms CKM.NativeGroupSlice.rowAction_one
#print axioms CKM.NativeGroupSlice.rowAction_mul
#print axioms CKM.NativeGroupSlice.rowAction_inverse
#print axioms CKM.NativeGroupSlice.analyticAt_rowAction
#print axioms CKM.NativeGroupSlice.originalF_actC
#print axioms CKM.NativeGroupSlice.originalF_actC_eq_zero_iff
#print axioms CKM.NativeGroupSlice.originalF_sliceChart
#print axioms CKM.NativeGroupSlice.originalF_sliceChart_eq_zero_iff
#print axioms CKM.NativeGroupSlice.originalF_literalCfg

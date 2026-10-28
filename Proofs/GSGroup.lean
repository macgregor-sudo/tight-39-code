module

public import GSCoord

@[expose] public section

/-!
# The full native automorphism group `G`: closed description, compactness, chart

* `autC = autOf prodC`: **all** bijective real-linear maps of the coordinate space preserving the
  native product; `mem_autC_iff` identifies it with all bijective real-linear native maps preserving
  `Glennie.jordan` (no unit, trace or metric condition imposed), and `autCEquiv` with the native
  type `{f : Albert ≃ₗ[ℝ] Albert // f preserves jordan}`.
* Unit, trace and trace-pairing preservation are derived (`autC_unit`, `autC_trace`,
  `autC_pairing`): trace from the accepted `Glennie.trace_preserved_of_jordan_equiv`.
* `autC_eq_closed`: `G` is the set of product- and pairing-preserving maps (pairing preservation
  forces injectivity, hence bijectivity); this is a finite system of closed polynomial equations.
* `isCompact_autC`: `G` is closed and bounded in `CEnd`: the pairing has weights `1` and `2`, so
  `‖a‖² ≤ coordinatePairing a a ≤ 51 ‖a‖²` (sup norm) and `‖A‖` is bounded on `G`.
* The identity chart `groupChart = expChart prodC` and its local properties (dimension 52,
  tangent `derC`, full group near the identity, analytic inverse), specialized from `GSAutChart`.
-/

noncomputable section

namespace CKM.NativeGroupSlice

open Glennie NativePolynomial CKM.NativeDerivationTriality

/-- `coordEnd.symm A` on a reconstructed point. -/
private theorem group_symm_from (A : CEnd) (v : Coord) :
    coordEnd.symm A (fromUpperCoordinates v) = fromUpperCoordinates (A v) := by
  rw [coordEnd_symm_apply, upperCoordinates_fromUpperCoordinates]

/-- The native product of reconstructed points is the reconstructed coordinate product. -/
private theorem group_jordan_from (u v : Coord) :
    jordan (fromUpperCoordinates u) (fromUpperCoordinates v) = fromUpperCoordinates (prodC u v) := by
  rw [prodC_eq_native, fromUpperCoordinates_upperCoordinates]

/-- `coordEnd.symm A` is `A` conjugated by the upper-coordinate equivalence. -/
private theorem group_coe_symm (A : CEnd) :
    ⇑(coordEnd.symm A) = upperCoordinateEquiv.symm ∘ ⇑A ∘ upperCoordinateEquiv := by
  funext x
  exact coordEnd_symm_apply A x

/-- The full native automorphism group, in coordinates. -/
abbrev autC : Set CEnd := autOf prodC

/-- `G` is exactly the set of bijective real-linear native maps preserving the native product. -/
theorem mem_autC_iff (A : CEnd) :
    A ∈ autC ↔ Function.Bijective (coordEnd.symm A) ∧
      ∀ x y, coordEnd.symm A (jordan x y) = jordan (coordEnd.symm A x) (coordEnd.symm A y) := by
  have hbij : Function.Bijective (coordEnd.symm A) ↔ Function.Bijective A := by
    rw [group_coe_symm, EquivLike.comp_bijective, EquivLike.bijective_comp]
  refine and_congr hbij.symm ⟨fun h x y => ?_, fun h a b => ?_⟩
  · rw [coordEnd_symm_apply, coordEnd_symm_apply, coordEnd_symm_apply, ← prodC_upperCoordinates,
      h, group_jordan_from]
  · have h' := h (fromUpperCoordinates a) (fromUpperCoordinates b)
    rw [group_symm_from, group_symm_from, group_jordan_from, group_symm_from,
      group_jordan_from] at h'
    simpa using congrArg upperCoordinates h'

/-- The same group, as A3's native automorphisms (product and trace preserving) that are bijective;
the trace condition is a consequence, not an extra restriction. -/
theorem mem_autC_iff_isNativeAut (A : CEnd) :
    A ∈ autC ↔ Function.Bijective (coordEnd.symm A) ∧ CKM.NativeFirstOrder.IsNativeAut (coordEnd.symm A) := by
  rw [mem_autC_iff]
  refine ⟨fun ⟨hb, hj⟩ => ⟨hb, ⟨hj, fun x => ?_⟩⟩, fun ⟨hb, hn⟩ => ⟨hb, hn.jordan⟩⟩
  exact trace_preserved_of_jordan_equiv (LinearEquiv.ofBijective (coordEnd.symm A) hb) hj x

/-- The equivalence with the native linear-equivalence automorphism type. -/
def autCEquiv : autC ≃ {f : Albert ≃ₗ[ℝ] Albert // ∀ x y, f (jordan x y) = jordan (f x) (f y)} where
  toFun A := ⟨LinearEquiv.ofBijective (coordEnd.symm A.1) ((mem_autC_iff A.1).1 A.2).1,
    ((mem_autC_iff A.1).1 A.2).2⟩
  invFun f := ⟨coordEnd f.1.toLinearMap, by
    rw [mem_autC_iff, AlgEquiv.symm_apply_apply]
    exact ⟨f.1.bijective, f.2⟩⟩
  left_inv A := by
    apply Subtype.ext
    change coordEnd (LinearEquiv.ofBijective (coordEnd.symm A.1)
      ((mem_autC_iff A.1).1 A.2).1).toLinearMap = A.1
    have h : (LinearEquiv.ofBijective (coordEnd.symm A.1)
        ((mem_autC_iff A.1).1 A.2).1).toLinearMap = coordEnd.symm A.1 :=
      LinearMap.ext fun _ => rfl
    rw [h, AlgEquiv.apply_symm_apply]
  right_inv f := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change coordEnd.symm (coordEnd f.1.toLinearMap) x = f.1 x
    rw [AlgEquiv.symm_apply_apply]
    rfl

theorem autCEquiv_apply (A : autC) (x : Albert) : (autCEquiv A).1 x = coordEnd.symm A.1 x := by
  rfl

/-- The native unit in upper coordinates (same statement and proof as the accepted
`upperCoordinates_unit_eq_coordinateUnit` of `NativeExactCKMFrameValueRows`, which is not in this
import closure). -/
private theorem group_upper_unit :
    upperCoordinates (1 : Albert) = (CoordinateMaps.coordinateUnit : Coord) := by
  funext k
  fin_cases k <;> rfl

/-- Coordinate trace is native trace of the reconstructed point. -/
private theorem group_coordTrace (v : Coord) :
    CoordinateMaps.coordinateTrace v = trace (fromUpperCoordinates v) := by
  rw [CoordinateMaps.coordinateTrace_apply]
  rfl

theorem autC_unit {A : CEnd} (hA : A ∈ autC) :
    A CoordinateMaps.coordinateUnit = CoordinateMaps.coordinateUnit := by
  obtain ⟨hb, hj⟩ := (mem_autC_iff A).1 hA
  set g := coordEnd.symm A
  have hleft : ∀ z, jordan (g 1) z = z := by
    intro z
    obtain ⟨y, rfl⟩ := hb.2 z
    rw [← hj, jordan_unit_left]
  have hg1 : g 1 = 1 := by
    rw [← jordan_unit_right (g 1), hleft]
  have h := congrArg upperCoordinates hg1
  rw [coordEnd_symm_apply, upperCoordinates_fromUpperCoordinates, group_upper_unit] at h
  exact h

theorem autC_trace {A : CEnd} (hA : A ∈ autC) (a : Coord) :
    CoordinateMaps.coordinateTrace (A a) = CoordinateMaps.coordinateTrace a := by
  have h := ((mem_autC_iff_isNativeAut A).1 hA).2.trace (fromUpperCoordinates a)
  rw [group_symm_from] at h
  rw [group_coordTrace, group_coordTrace, h]

theorem autC_pairing {A : CEnd} (hA : A ∈ autC) (a b : Coord) :
    CoordinateMaps.coordinatePairing (A a) (A b) = CoordinateMaps.coordinatePairing a b := by
  have hbj := (mem_autC_iff A).1 hA
  have h := trace_pairing_preserved_of_jordan_equiv (LinearEquiv.ofBijective (coordEnd.symm A) hbj.1)
    hbj.2 (fromUpperCoordinates a) (fromUpperCoordinates b)
  simp only [LinearEquiv.ofBijective_apply, group_symm_from] at h
  rw [← upperCoordinates_fromUpperCoordinates (A a), ← upperCoordinates_fromUpperCoordinates (A b),
    CoordinateMaps.coordinatePairing_upperCoordinates_eq_native_trace, h,
    ← CoordinateMaps.coordinatePairing_upperCoordinates_eq_native_trace,
    upperCoordinates_fromUpperCoordinates, upperCoordinates_fromUpperCoordinates]

private theorem group_weight_ge (i : Fin 27) :
    (1 : ℝ) ≤ (IntegralStructureConstants.coordinateTraceWeight i : ℝ) := by
  unfold IntegralStructureConstants.coordinateTraceWeight
  split_ifs <;> norm_num

private theorem group_weight_le (i : Fin 27) :
    (IntegralStructureConstants.coordinateTraceWeight i : ℝ) ≤ 2 := by
  unfold IntegralStructureConstants.coordinateTraceWeight
  split_ifs <;> norm_num

/-- Each squared coordinate is bounded by the pairing (all weights are at least `1`). -/
private theorem group_sq_le_pairing (a : Coord) (j : Fin 27) :
    a j * a j ≤ CoordinateMaps.coordinatePairing a a := by
  unfold CoordinateMaps.coordinatePairing
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin 27)),
      0 ≤ (IntegralStructureConstants.coordinateTraceWeight i : ℝ) * a i * a i := by
    intro i _
    rw [mul_assoc]
    exact mul_nonneg (le_trans zero_le_one (group_weight_ge i)) (mul_self_nonneg _)
  refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ j))
  rw [mul_assoc]
  exact le_mul_of_one_le_left (mul_self_nonneg _) (group_weight_ge j)

/-- The pairing is bounded by `54 ‖a‖²` for the sup norm (all weights are at most `2`). -/
private theorem group_pairing_le (a : Coord) :
    CoordinateMaps.coordinatePairing a a ≤ 54 * (‖a‖ * ‖a‖) := by
  unfold CoordinateMaps.coordinatePairing
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin 27)),
      (IntegralStructureConstants.coordinateTraceWeight i : ℝ) * a i * a i ≤ 2 * (‖a‖ * ‖a‖) := by
    intro i _
    have hi : |a i| ≤ ‖a‖ := by
      have := norm_le_pi_norm a i
      rwa [Real.norm_eq_abs] at this
    have hsq : a i * a i ≤ ‖a‖ * ‖a‖ := by
      rw [← abs_mul_abs_self (a i)]
      exact mul_self_le_mul_self (abs_nonneg _) hi
    rw [mul_assoc]
    exact mul_le_mul (group_weight_le i) hsq (mul_self_nonneg _) (by norm_num)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  linarith

/-- The closed polynomial description of `G`. -/
theorem autC_eq_closed : autC = {A : CEnd | (∀ a b, A (prodC a b) = prodC (A a) (A b)) ∧
    ∀ a b, CoordinateMaps.coordinatePairing (A a) (A b) = CoordinateMaps.coordinatePairing a b} := by
  ext A
  refine ⟨fun hA => ⟨hA.2, autC_pairing hA⟩, fun ⟨hprod, hpair⟩ => ⟨?_, hprod⟩⟩
  have hinj : Function.Injective A := by
    rw [← ContinuousLinearMap.coe_coe, injective_iff_map_eq_zero]
    intro a ha
    rw [ContinuousLinearMap.coe_coe] at ha
    have h0 : CoordinateMaps.coordinatePairing a a = 0 := by
      rw [← hpair, ha]
      simp [CoordinateMaps.coordinatePairing]
    funext j
    have := group_sq_le_pairing a j
    rw [h0] at this
    exact mul_self_eq_zero.1 (le_antisymm this (mul_self_nonneg _))
  have hsurj : Function.Surjective A := by
    have h := (LinearMap.injective_iff_surjective (f := (A : Coord →ₗ[ℝ] Coord))).1
      (by rwa [ContinuousLinearMap.coe_coe])
    rwa [ContinuousLinearMap.coe_coe] at h
  exact ⟨hinj, hsurj⟩

theorem isClosed_autC : IsClosed autC := by
  rw [autC_eq_closed, Set.ofPred_and]
  refine IsClosed.inter ?_ ?_
  · simp only [Set.ofPred_forall]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq ?_ ?_
    · exact continuous_eval_const _
    · exact (prodC.continuous.comp (continuous_eval_const a)).clm_apply (continuous_eval_const b)
  · simp only [Set.ofPred_forall]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq ?_ continuous_const
    unfold CoordinateMaps.coordinatePairing
    refine continuous_finsetSum _ fun i _ => ?_
    have hi : Continuous fun v : Coord => v i := continuous_apply i
    exact (continuous_const.mul (hi.comp (continuous_eval_const a))).mul
      (hi.comp (continuous_eval_const b))

theorem isCompact_autC : IsCompact autC := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_autC
    ((Metric.isBounded_iff_subset_closedBall 0).2 ⟨8, fun A hA => mem_closedBall_zero_iff.2 ?_⟩)
  refine ContinuousLinearMap.opNorm_le_bound A (by norm_num) fun a => ?_
  have hn : 0 ≤ ‖a‖ := norm_nonneg a
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  rw [Real.norm_eq_abs]
  have h1 := group_sq_le_pairing (A a) j
  rw [autC_pairing hA] at h1
  have h2 := group_pairing_le a
  refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith

/-! ## The identity chart -/

/-- The identity chart of `G`: `D ↦ exp D` on the 52-dimensional native derivations. -/
abbrev groupChart : derC → CEnd := expChart prodC

theorem groupChart_mem_autC (D : derC) : groupChart D ∈ autC := expChart_mem_autOf prodC D

theorem groupChart_zero : groupChart 0 = 1 := expChart_zero prodC

theorem analyticAt_groupChart (D : derC) : AnalyticAt ℝ groupChart D := analyticAt_expChart prodC D

theorem hasStrictFDerivAt_groupChart : HasStrictFDerivAt groupChart derC.subtypeL 0 :=
  hasStrictFDerivAt_expChart prodC

/-- **The chart covers the full group near the identity**, with an analytic inverse. -/
theorem exists_groupChart_local :
    ∃ U : Set derC, ∃ W : Set CEnd, ∃ inv : CEnd → derC,
      IsOpen U ∧ (0 : derC) ∈ U ∧ IsOpen W ∧ (1 : CEnd) ∈ W ∧
      Set.InjOn groupChart U ∧ groupChart '' U = autC ∩ W ∧
      (∀ g ∈ autC ∩ W, inv g ∈ U ∧ groupChart (inv g) = g) ∧
      (∀ D ∈ U, inv (groupChart D) = D) ∧
      AnalyticOnNhd ℝ inv W :=
  exists_expChart_local prodC

end CKM.NativeGroupSlice

#print axioms CKM.NativeGroupSlice.mem_autC_iff
#print axioms CKM.NativeGroupSlice.mem_autC_iff_isNativeAut
#print axioms CKM.NativeGroupSlice.autCEquiv
#print axioms CKM.NativeGroupSlice.autCEquiv_apply
#print axioms CKM.NativeGroupSlice.autC_unit
#print axioms CKM.NativeGroupSlice.autC_trace
#print axioms CKM.NativeGroupSlice.autC_pairing
#print axioms CKM.NativeGroupSlice.autC_eq_closed
#print axioms CKM.NativeGroupSlice.isClosed_autC
#print axioms CKM.NativeGroupSlice.isCompact_autC

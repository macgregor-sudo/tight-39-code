module

public import NativeOriginalFIdealTangentTransfer

@[expose] public section

/-!
# Native first-order system (A3 core interface)

Definition: The pointwise native first-order system of an arbitrary labelled
configuration `p : Fin 39 → Glennie.Albert`, written exactly as the right-hand side of the reviewed
transfer theorem `original_all_fRows_linearMatrix_zero_iff_native`: tangent idempotency, within-frame
orthogonality, frame sums and cross-frame trace overlaps. No phase or anchor data enters.
-/

noncomputable section

namespace CKM.NativeFirstOrder

open NativePolynomial.ConfigurationResiduals ConfigurationResidualIndices

/-- The four native first-order families at `p`, for a variation `u`. -/
def IsFirstOrder (p u : Fin 39 → Glennie.Albert) : Prop :=
  (∀ i : Fin 39, (2 : ℝ) • Glennie.jordan (p i) (u i) = u i) ∧
  (∀ (f : Fin 13) (s : Fin 3),
    Glennie.jordan (p (framePointIndex f (withinPair s).val.1))
        (u (framePointIndex f (withinPair s).val.2)) +
      Glennie.jordan (u (framePointIndex f (withinPair s).val.1))
        (p (framePointIndex f (withinPair s).val.2)) = 0) ∧
  (∀ f : Fin 13, (∑ a : Fin 3, u (framePointIndex f a)) = 0) ∧
  (∀ (fg : Pair 13) (a b : Fin 3),
    Glennie.trace (Glennie.jordan (p (framePointIndex fg.val.1 a)) (u (framePointIndex fg.val.2 b))) +
      Glennie.trace (Glennie.jordan (u (framePointIndex fg.val.1 a))
        (p (framePointIndex fg.val.2 b))) = 0)

/-- The native first-order system as a real subspace of all variations of the 39 points. -/
def firstOrderSystem (p : Fin 39 → Glennie.Albert) : Submodule ℝ (Fin 39 → Glennie.Albert) where
  carrier := {u | IsFirstOrder p u}
  add_mem' := by
    rintro u v ⟨hu1, hu2, hu3, hu4⟩ ⟨hv1, hv2, hv3, hv4⟩
    refine ⟨fun i => ?_, fun f s => ?_, fun f => ?_, fun fg a b => ?_⟩
    · simp only [Pi.add_apply, Glennie.jordan_add_right, smul_add, hu1 i, hv1 i]
    · simp only [Pi.add_apply, Glennie.jordan_add_right, Glennie.jordan_add_left]
      rw [add_add_add_comm, hu2 f s, hv2 f s, add_zero]
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hu3 f, hv3 f, add_zero]
    · simp only [Pi.add_apply, Glennie.jordan_add_right, Glennie.jordan_add_left,
        ← Glennie.traceLinear_apply, map_add] at hu4 hv4 ⊢
      rw [add_add_add_comm, hu4 fg a b, hv4 fg a b, add_zero]
  zero_mem' := by
    have h0 : ∀ x : Glennie.Albert, Glennie.jordan x 0 = 0 := fun x => by
      simpa using Glennie.jordan_smul_right (0 : ℝ) x 0
    have h0' : ∀ x : Glennie.Albert, Glennie.jordan 0 x = 0 := fun x => by
      simpa using Glennie.jordan_smul_left (0 : ℝ) 0 x
    refine ⟨fun i => ?_, fun f s => ?_, fun f => ?_, fun fg a b => ?_⟩
    · simp only [Pi.zero_apply, h0, smul_zero]
    · simp only [Pi.zero_apply, h0, h0', add_zero]
    · simp only [Pi.zero_apply, Finset.sum_const_zero]
    · simp only [Pi.zero_apply, h0, h0', ← Glennie.traceLinear_apply, map_zero, add_zero]
  smul_mem' := by
    rintro c u ⟨hu1, hu2, hu3, hu4⟩
    refine ⟨fun i => ?_, fun f s => ?_, fun f => ?_, fun fg a b => ?_⟩
    · simp only [Pi.smul_apply, Glennie.jordan_smul_right, smul_comm (2 : ℝ) c, hu1 i]
    · simp only [Pi.smul_apply, Glennie.jordan_smul_right, Glennie.jordan_smul_left, ← smul_add,
        hu2 f s, smul_zero]
    · simp only [Pi.smul_apply, ← Finset.smul_sum, hu3 f, smul_zero]
    · simp only [Pi.smul_apply, Glennie.jordan_smul_right, Glennie.jordan_smul_left,
        ← Glennie.traceLinear_apply, map_smul, smul_eq_mul] at hu4 ⊢
      rw [← mul_add, hu4 fg a b, mul_zero]

theorem mem_firstOrderSystem {p u : Fin 39 → Glennie.Albert} :
    u ∈ firstOrderSystem p ↔ IsFirstOrder p u := Iff.rfl

end CKM.NativeFirstOrder

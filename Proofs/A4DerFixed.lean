module

public import A4Cartan

@[expose] public section

/-!
# Fixed derivations: `dim Der(J)^H = 16`, `Der(J)^K = t` of dimension four

From the `K`-equivariant splitting `Der ≃ O³ × s` (`derDecompKEquiv`): the slotwise `H`-fixed
directions have dimension six and `s^H` has dimension ten; nothing slotwise is `K`-fixed and `s^K = t`.
-/

noncomputable section

namespace CKM.NativeIntrinsicTriality

open Glennie CKM.NativeDerivationTriality CKM.NativeFirstOrder

attribute [local instance 100] LieRing.ofAssociativeRing

/-- For `g³ = 1`, `g D g² = D` iff `g` commutes with `D`. -/
theorem conj_eq_iff_comm {g D : Module.End ℝ Albert} (hg : g ^ 3 = 1) :
    g * D * g ^ 2 = D ↔ g * D = D * g := by
  constructor
  · intro h
    calc g * D = g * D * g ^ 3 := by rw [hg, mul_one]
      _ = g * D * g ^ 2 * g := by rw [pow_succ, mul_assoc (g * D)]
      _ = D * g := by rw [h]
  · intro h
    calc g * D * g ^ 2 = D * g * g ^ 2 := by rw [h]
      _ = D * g ^ 3 := by rw [mul_assoc, ← pow_succ']
      _ = D := by rw [hg, mul_one]

theorem finrank_derAction_fixH (H : Fin 4) : Module.finrank ℝ (derAction.fixH H) = 16 := by
  rw [derDecompKEquiv.finrank_fixH_eq H, finrank_fixH_prod, finrank_slotAction_fixH,
    finrank_sAction_fixH]

theorem finrank_derAction_fixK : Module.finrank ℝ derAction.fixK = 4 := by
  rw [derDecompKEquiv.finrank_fixK_eq, finrank_fixK_prod, finrank_slotAction_fixK,
    finrank_sAction_fixK]

/-- `Der(J)^K` is exactly the common Cartan. -/
theorem mem_derAction_fixK_iff (D : jordanDerivations) :
    D ∈ derAction.fixK ↔ (D : Module.End ℝ Albert) ∈ commonCartan := by
  rw [mem_commonCartan, KAction.fixK, Submodule.mem_inf, mem_fixedSpace, mem_fixedSpace]
  have h0 : derAction.g0 D = D ↔ R0 * (D : Module.End ℝ Albert) = D * R0 := by
    rw [← Subtype.coe_inj, derAction_g0_apply]
    exact conj_eq_iff_comm R0_cube
  have h1 : derAction.g1 D = D ↔ R1 * (D : Module.End ℝ Albert) = D * R1 := by
    rw [← Subtype.coe_inj, derAction_g1_apply]
    exact conj_eq_iff_comm R1_cube
  rw [h0, h1]
  exact ⟨fun h => ⟨D.2, h⟩, fun h => h.2⟩

end CKM.NativeIntrinsicTriality

#print axioms CKM.NativeIntrinsicTriality.finrank_derAction_fixH
#print axioms CKM.NativeIntrinsicTriality.finrank_derAction_fixK
#print axioms CKM.NativeIntrinsicTriality.mem_derAction_fixK_iff

module

public import A3Family
public import A3Automorphisms
public import A3Quartet
public import A3Action
public import A3Anchor2Form

@[expose] public section

/-!
# Anchor H2: the native binding at every unit phase

Construct the transport, relabelling, quartet and nine representative matrices for anchor H2 and prove
every `AnchorBinding` field, at arbitrary unit phases (resonant ones included).
-/

noncomputable section

namespace CKM.NativeFirstOrder

theorem anchorBinding2_nonempty (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Nonempty (AnchorBinding (anchorGenerator 2) (anchorShift 2) (literalPoint ξ) (anchorTriple ξ hξ 2)) := by
  have hinj : Function.Injective (transportTinv 1) := by
    intro x y h
    have hx := LinearMap.congr_fun (transportT_comp_transportTinv 1) x
    have hy := LinearMap.congr_fun (transportT_comp_transportTinv 1) y
    rw [LinearMap.comp_apply, LinearMap.id_apply] at hx hy
    rw [← hx, ← hy, h]
  exact ⟨
    { Ψ := transportTinv 1
      Ψ_aut := transportTinv_isNativeAut 1
      Ψ_injective := hinj
      conj := transportTinv_one_conj
      fperm := Anchor2.fperm2
      τ := Anchor2.τ2
      shift_compat := Anchor2.anchor2_shift_compat
      q := Anchor2.q2 ξ
      q_idem := Anchor2.q2_idem ξ hξ
      q_finrank := Anchor2.q2_finrank ξ hξ
      W := Anchor2.anchor2W ξ hξ
      W_ueb := Anchor2.anchor2W_ueb ξ hξ
      W_finrank := Anchor2.anchor2W_finrank ξ hξ
      form := Anchor2.anchor2_form ξ hξ }⟩

end CKM.NativeFirstOrder

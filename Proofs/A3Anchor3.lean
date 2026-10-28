module

public import A3Family
public import A3Automorphisms
public import A3Quartet
public import A3Action
public import A3Anchor3Gauge

@[expose] public section

/-!
# Anchor H3: the native binding at every unit phase

Construct the transport, relabelling, quartet and nine representative matrices for anchor H3 and prove
every `AnchorBinding` field, at arbitrary unit phases (resonant ones included).
-/

noncomputable section

namespace CKM.NativeFirstOrder

namespace Anchor3

open UnitaryErrorBases NativePolynomial NativePolynomial.ConfigurationResiduals
open CompactAlbert UnitaryErrorBases.ComplexQuartet

/-- Frame relabelling of anchor H3 (standard frame ↦ literal frame). -/
def fperm3 : Equiv.Perm (Fin 13) where
  toFun := ![0, 10, 11, 12, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  invFun := ![0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 1, 2, 3]
  left_inv := by intro f; revert f; decide
  right_inv := by intro f; revert f; decide

/-- Outcome relabelling of anchor H3: identity on standard frames 0 and 7–9, negation elsewhere. -/
def τ3 (f : Fin 13) : Equiv.Perm (Fin 3) :=
  if f.val = 0 ∨ (7 ≤ f.val ∧ f.val ≤ 9) then Equiv.refl _ else Equiv.neg (Fin 3)

theorem pointRelabel_apply (fperm : Equiv.Perm (Fin 13)) (τ : Fin 13 → Equiv.Perm (Fin 3))
    (f : Fin 13) (a : Fin 3) :
    pointRelabel fperm τ (finProdFinEquiv (f, a)) = finProdFinEquiv (fperm f, τ f a) := by
  simp [pointRelabel, Equiv.prodShear]

theorem zval3 (x : ZMod 3) : ZMod.val x = (x : Fin 3).val := rfl

theorem framePointIndex_eq (f : Fin 13) (a : Fin 3) :
    framePointIndex f a = finProdFinEquiv (f, a) := by
  apply Fin.ext
  rw [finProdFinEquiv_apply_val]
  show 3 * f.val + a.val = _
  ring

theorem fpi_div_mod (i : Fin 39) :
    framePointIndex ⟨i.val / 3, by omega⟩ ⟨i.val % 3, by omega⟩ = i :=
  Fin.ext (by
    show 3 * (i.val / 3) + i.val % 3 = i.val
    omega)

theorem shift_compat3 (i : Fin 39) :
    outcomeShift (anchorShift 3) (pointRelabel fperm3 τ3 i) = pointRelabel fperm3 τ3 (stdShift i) := by
  obtain ⟨f, a, rfl⟩ : ∃ f a, framePointIndex f a = i := ⟨_, _, fpi_div_mod i⟩
  simp only [stdShift, outcomeShift, pointRelabel_framePointIndex, Equiv.refl_apply,
    Equiv.coe_addRight]
  congr 1
  revert f a
  decide

theorem stdAnchored_vis (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : UnitaryErrorBases.Family) (k : Fin 4) (a : Fin 3) :
    stdAnchored q W (framePointIndex (Fin.castLE (show 4 ≤ 13 by decide) k) a) =
      includeHermitianMatrix (q k a) := by
  have h12 : (framePointIndex (Fin.castLE (show 4 ≤ 13 by decide) k) a).val < 12 := by
    rw [framePointIndex_val]; simp; omega
  rw [stdAnchored, dite_eq_left_of_eq_true (eq_true h12)]
  congr 2 <;> ext <;> simp [framePointIndex_val]; omega

theorem stdAnchored_hid (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : UnitaryErrorBases.Family) (l : Label) (a : Fin 3) :
    stdAnchored q W (framePointIndex (hiddenFrame l) a) =
      nativeComplementaryPoint ((UnitaryErrorBases.ThreeCycleFourier.omega ^ (a : Fin 3).val) • W l) := by
  have hfe : (hiddenFrameEquiv l).val = 3 * (l.1 : Fin 3).val + (l.2 : Fin 3).val := by
    obtain ⟨l1, l2⟩ := l; revert l1 l2; decide
  have hl : (hiddenFrame l).val = 4 + 3 * (l.1 : Fin 3).val + (l.2 : Fin 3).val := by
    show 4 + (hiddenFrameEquiv l).val = _
    rw [hfe]; ring
  have h12 : ¬ (framePointIndex (hiddenFrame l) a).val < 12 := by
    rw [framePointIndex_val, hl]; omega
  rw [stdAnchored, dite_eq_right_of_eq_false (eq_false h12)]
  have hmod : (framePointIndex (hiddenFrame l) a).val % 3 = (a : Fin 3).val := by
    rw [framePointIndex_val, hl]; omega
  have hlab : hiddenFrameEquiv.symm
      ⟨(framePointIndex (hiddenFrame l) a).val / 3 - 4, by
        have := (framePointIndex (hiddenFrame l) a).isLt; omega⟩ = l := by
    rw [Equiv.symm_apply_eq]
    ext; rw [hfe]; simp only [framePointIndex_val, hl]; omega
  rw [hmod, hlab]

theorem Ψ3_injective : Function.Injective (transportTinv 2) := by
  intro x y h
  have hx := LinearMap.congr_fun (transportT_comp_transportTinv 2) x
  have hy := LinearMap.congr_fun (transportT_comp_transportTinv 2) y
  rw [LinearMap.comp_apply, LinearMap.id_apply] at hx hy
  rw [← hx, ← hy, h]

theorem q3_finrank (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ (quartetFirstOrder fun k t => (q3 ξ k t).val) = 8 :=
  (finrank_quartetFirstOrder_conj (fun k t => (stdQuartet k t).val) (g3 ξ) (g3_unitary ξ hξ)
    (Equiv.refl _) (fun _ => Equiv.refl _)).trans finrank_quartetFirstOrder_std

theorem fr_g0 (s : ZMod 3) : fperm3 (hiddenFrame (0, s)) =
    Fin.castLE (by omega) (⟨s.val + 1, by have := ZMod.val_lt s; omega⟩ : Fin 4) := by
  revert s; decide
theorem fr_g1 (s : ZMod 3) : fperm3 (hiddenFrame (1, s)) =
    ⟨4 + 3 * (0 : Fin 3).val + s.val, by have := ZMod.val_lt s; omega⟩ := by
  revert s; decide
theorem fr_g2 (s : ZMod 3) : fperm3 (hiddenFrame (2, s)) =
    ⟨4 + 3 * (1 : Fin 3).val + s.val, by have := ZMod.val_lt s; omega⟩ := by
  revert s; decide
theorem tau_g0 (s : ZMod 3) (a : Fin 3) : τ3 (hiddenFrame (0, s)) a = -a := by revert s a; decide
theorem tau_g1 (s : ZMod 3) (a : Fin 3) : τ3 (hiddenFrame (1, s)) a = a := by revert s a; decide
theorem tau_g2 (s : ZMod 3) (a : Fin 3) : τ3 (hiddenFrame (2, s)) a = -a := by revert s a; decide

theorem k4_cases (k : Fin 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 :=
  (by decide : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) k

theorem negZ (a : Fin 3) : (-a : Fin 3) = ((-(a : ZMod 3) : ZMod 3) : Fin 3) := rfl

theorem form3 (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 39) :
    transportTinv 2 (literalPoint ξ (pointRelabel fperm3 τ3 i)) = stdAnchored (q3 ξ) (W3 ξ) i := by
  obtain ⟨f, a, rfl⟩ : ∃ f a, framePointIndex f a = i := ⟨_, _, fpi_div_mod i⟩
  rw [pointRelabel_framePointIndex]
  by_cases hf : f.val < 4
  · have hex : ∃ k : Fin 4, Fin.castLE (show 4 ≤ 13 by decide) k = f := ⟨⟨f.val, hf⟩, Fin.ext rfl⟩
    clear hf
    obtain ⟨k, rfl⟩ := hex
    rw [stdAnchored_vis]
    rcases k4_cases k with rfl | rfl | rfl | rfl
    · have h1 : fperm3 (Fin.castLE (show 4 ≤ 13 by decide) 0) = Fin.castLE (show 4 ≤ 13 by decide) 0 := by
        decide
      have h2 : τ3 (Fin.castLE (show 4 ≤ 13 by decide) 0) a = a := by revert a; decide
      rw [h1, h2, literalPoint_quartet]
      exact tinv_coord ξ hξ a
    · have h1 : fperm3 (Fin.castLE (show 4 ≤ 13 by decide) 1) =
          ⟨4 + 3 * (2 : Fin 3).val + (0 : ZMod 3).val, by decide⟩ := by decide
      have h2 : τ3 (Fin.castLE (show 4 ≤ 13 by decide) 1) a = -a := by revert a; decide
      rw [h1, h2]
      exact (congrArg (transportTinv 2) (literalPoint_hidden ξ hξ 2 0 (-(a : ZMod 3)))).trans
        (tinv_hidden2 ξ hξ 0 a 1 rfl)
    · have h1 : fperm3 (Fin.castLE (show 4 ≤ 13 by decide) 2) =
          ⟨4 + 3 * (2 : Fin 3).val + (1 : ZMod 3).val, by decide⟩ := by decide
      have h2 : τ3 (Fin.castLE (show 4 ≤ 13 by decide) 2) a = -a := by revert a; decide
      rw [h1, h2]
      exact (congrArg (transportTinv 2) (literalPoint_hidden ξ hξ 2 1 (-(a : ZMod 3)))).trans
        (tinv_hidden2 ξ hξ 1 a 2 rfl)
    · have h1 : fperm3 (Fin.castLE (show 4 ≤ 13 by decide) 3) =
          ⟨4 + 3 * (2 : Fin 3).val + (2 : ZMod 3).val, by decide⟩ := by decide
      have h2 : τ3 (Fin.castLE (show 4 ≤ 13 by decide) 3) a = -a := by revert a; decide
      rw [h1, h2]
      exact (congrArg (transportTinv 2) (literalPoint_hidden ξ hξ 2 2 (-(a : ZMod 3)))).trans
        (tinv_hidden2 ξ hξ 2 a 3 rfl)
  · obtain ⟨l, rfl⟩ : ∃ l, hiddenFrame l = f := by
      refine ⟨hiddenFrameEquiv.symm ⟨f.val - 4, by omega⟩, ?_⟩
      ext; simp only [hiddenFrame, Equiv.apply_symm_apply]; omega
    rw [stdAnchored_hid]
    obtain ⟨g, s⟩ := l
    rcases idx_cases g with rfl | rfl | rfl
    · rw [fr_g0, tau_g0]
      rcases idx_cases s with rfl | rfl | rfl
      · rw [literalPoint_quartet]; exact tinv_phase ξ 0 a _ rfl
      · rw [literalPoint_quartet]; exact tinv_phase ξ 1 a _ rfl
      · rw [literalPoint_quartet]; exact tinv_phase ξ 2 a _ rfl
    · rw [fr_g1, tau_g1]
      exact (congrArg (transportTinv 2) (literalPoint_hidden ξ hξ 0 s a)).trans (tinv_hidden0 ξ s a)
    · rw [fr_g2, tau_g2]
      exact (congrArg (transportTinv 2) (literalPoint_hidden ξ hξ 1 s (-(a : ZMod 3)))).trans
        (tinv_hidden1 ξ s a)

end Anchor3

theorem anchorBinding3_nonempty (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Nonempty (AnchorBinding (anchorGenerator 3) (anchorShift 3) (literalPoint ξ) (anchorTriple ξ hξ 3)) := by
  exact
    ⟨{ Ψ := transportTinv 2
       Ψ_aut := transportTinv_isNativeAut 2
       Ψ_injective := Anchor3.Ψ3_injective
       conj := transportTinv_two_conj
       fperm := Anchor3.fperm3
       τ := Anchor3.τ3
       shift_compat := Anchor3.shift_compat3
       q := Anchor3.q3 ξ
       q_idem := Anchor3.q3_idem ξ hξ
       q_finrank := Anchor3.q3_finrank ξ hξ
       W := Anchor3.W3 ξ
       W_ueb := Anchor3.W3_ueb ξ hξ
       W_finrank := Anchor3.W3_finrank ξ hξ
       form := Anchor3.form3 ξ hξ }⟩

end CKM.NativeFirstOrder

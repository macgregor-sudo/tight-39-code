module

public import A3Family
public import A3Automorphisms
public import A3Quartet
public import A3Action
public import A3Anchor0Gauge

@[expose] public section

/-!
# Anchor H0: the native binding at every unit phase

Construct the transport, relabelling, quartet and nine representative matrices for anchor H0 and prove
every `AnchorBinding` field, at arbitrary unit phases (resonant ones included).
-/

noncomputable section

namespace CKM.NativeFirstOrder

namespace Anchor0

open UnitaryErrorBases NativePolynomial NativePolynomial.ConfigurationResiduals
open CompactAlbert UnitaryErrorBases.ComplexQuartet

/-- Outcome relabelling of anchor H0: identity on frames 0–3, negation on hidden frames 4–12. -/
def anchor0τ (f : Fin 13) : Equiv.Perm (Fin 3) :=
  if f.val < 4 then Equiv.refl _ else Equiv.neg (Fin 3)

theorem pointRelabel_apply (fperm : Equiv.Perm (Fin 13)) (τ : Fin 13 → Equiv.Perm (Fin 3))
    (f : Fin 13) (a : Fin 3) :
    pointRelabel fperm τ (finProdFinEquiv (f, a)) = finProdFinEquiv (fperm f, τ f a) := by
  simp [pointRelabel, Equiv.prodShear]

theorem anchor0_shift_compat (i : Fin 39) :
    outcomeShift (anchorShift 0) (pointRelabel (Equiv.refl _) anchor0τ i) =
      pointRelabel (Equiv.refl _) anchor0τ (stdShift i) := by
  obtain ⟨⟨f, a⟩, rfl⟩ := (finProdFinEquiv : Fin 13 × Fin 3 ≃ Fin 39).surjective i
  simp only [stdShift, outcomeShift, pointRelabel_apply, Equiv.refl_apply, Equiv.coe_addRight,
    anchorShift, shift0, anchor0τ]
  by_cases hf : f.val < 4
  · simp [hf]
  · simp only [hf, ite_false, Equiv.neg_apply]
    congr 2
    revert a
    decide

theorem zval (x : ZMod 3) : ZMod.val x = Fin.val (n := 3) x := rfl

theorem fpf_val (f : Fin 13) (a : Fin 3) :
    ((finProdFinEquiv (f, a) : Fin 39) : ℕ) = a.val + 3 * f.val := rfl

theorem hiddenFrame_val (l : Label) :
    (hiddenFrame l).val = 4 + (Fin.val (n := 3) l.2 + 3 * Fin.val (n := 3) l.1) := rfl

theorem anchor0_form (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 39) :
    (LinearMap.id : Glennie.Albert →ₗ[ℝ] Glennie.Albert)
        (literalPoint ξ (pointRelabel (Equiv.refl _) anchor0τ i)) =
      stdAnchored stdQuartet (anchor0W ξ) i := by
  obtain ⟨⟨f, a⟩, rfl⟩ := (finProdFinEquiv : Fin 13 × Fin 3 ≃ Fin 39).surjective i
  rw [pointRelabel_apply, LinearMap.id_apply, Equiv.refl_apply]
  by_cases hf : f.val < 4
  · have hτ : anchor0τ f a = a := by simp [anchor0τ, hf]
    rw [hτ]
    have hidx : (finProdFinEquiv (f, a) : Fin 39) =
        framePointIndex (Fin.castLE (by omega) (⟨f.val, hf⟩ : Fin 4)) a := by
      ext; simp only [framePointIndex, fpf_val, Fin.val_castLE]; omega
    rw [hidx, literalPoint_quartet]
    have h12 : (framePointIndex (Fin.castLE (by omega) (⟨f.val, hf⟩ : Fin 4)) a).val < 12 := by
      simp [framePointIndex]; omega
    rw [stdAnchored]
    simp only [h12, ↓reduceDIte]
    congr 2 <;> ext <;> simp [framePointIndex] <;> omega
  · obtain ⟨l, rfl⟩ : ∃ l, hiddenFrame l = f := by
      refine ⟨hiddenFrameEquiv.symm ⟨f.val - 4, by omega⟩, ?_⟩
      ext; simp only [hiddenFrame, Equiv.apply_symm_apply]; omega
    have hτ : anchor0τ (hiddenFrame l) a = -a := by simp [anchor0τ, hf]
    rw [hτ]
    have hl : (hiddenFrame l).val = 4 + 3 * Fin.val (n := 3) l.1 + Fin.val (n := 3) l.2 := by
      rw [hiddenFrame_val]; omega
    have hidx : (finProdFinEquiv (hiddenFrame l, -a) : Fin 39) =
        framePointIndex ⟨4 + 3 * Fin.val (n := 3) l.1 + ZMod.val l.2, by
          have := ZMod.val_lt l.2; omega⟩ (-a) := by
      ext; simp only [framePointIndex, fpf_val, hl, zval]; omega
    rw [hidx]
    refine (literalPoint_hidden ξ hξ l.1 l.2 (-(a : ZMod 3))).trans ?_
    have h12 : ¬ (finProdFinEquiv (hiddenFrame l, a) : Fin 39).val < 12 := by
      simp only [fpf_val, hl]; omega
    rw [stdAnchored]
    simp only [h12, ↓reduceDIte]
    have hmod : (finProdFinEquiv (hiddenFrame l, a) : Fin 39).val % 3 = (a : Fin 3).val := by
      simp only [fpf_val, hl]; omega
    have hlab : hiddenFrameEquiv.symm
        ⟨(finProdFinEquiv (hiddenFrame l, a) : Fin 39).val / 3 - 4, by
          have := (finProdFinEquiv (hiddenFrame l, a)).isLt; omega⟩ = l := by
      rw [Equiv.symm_apply_eq]
      ext
      have hfe : (hiddenFrameEquiv l).val = Fin.val (n := 3) l.2 + 3 * Fin.val (n := 3) l.1 := rfl
      show (finProdFinEquiv (hiddenFrame l, a) : Fin 39).val / 3 - 4 = (hiddenFrameEquiv l).val
      rw [fpf_val, hl, hfe]; omega
    rw [hmod, hlab]
    congr 1
    exact hiddenMatrix_neg ξ l.1 l.2 a

end Anchor0

theorem anchorBinding0_nonempty (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Nonempty (AnchorBinding (anchorGenerator 0) (anchorShift 0) (literalPoint ξ) (anchorTriple ξ hξ 0)) := by
  exact ⟨
    { Ψ := LinearMap.id
      Ψ_aut := ⟨fun _ _ => by simp only [LinearMap.id_apply], fun _ => by rw [LinearMap.id_apply]⟩
      Ψ_injective := Function.injective_id
      conj := by rw [LinearMap.id_comp, LinearMap.comp_id]; rfl
      fperm := Equiv.refl _
      τ := Anchor0.anchor0τ
      shift_compat := Anchor0.anchor0_shift_compat
      q := stdQuartet
      q_idem := stdQuartet_idem
      q_finrank := finrank_quartetFirstOrder_std
      W := Anchor0.anchor0W ξ
      W_ueb := Anchor0.anchor0W_ueb ξ hξ
      W_finrank := Anchor0.anchor0W_finrank ξ hξ
      form := Anchor0.anchor0_form ξ hξ }⟩

end CKM.NativeFirstOrder

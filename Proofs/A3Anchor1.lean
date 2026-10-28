module

public import A3Family
public import A3Automorphisms
public import A3Quartet
public import A3Action
public import A3Anchor1Gauge

@[expose] public section

/-!
# Anchor H1: the native binding at every unit phase

Construct the transport, relabelling, quartet and nine representative matrices for anchor H1 and prove
every `AnchorBinding` field, at arbitrary unit phases (resonant ones included).
-/

noncomputable section

namespace CKM.NativeFirstOrder

open NativePolynomial NativePolynomial.ConfigurationResiduals CompactAlbert
open UnitaryErrorBases.ComplexQuartet

namespace Anchor1

/-! ## Relabelling data -/

/-- Standard frame ↦ original frame: quartet frames `1,2,3 ↔ 4,5,6`, all others fixed. -/
def fperm1 : Equiv.Perm (Fin 13) := Equiv.swap 1 4 * Equiv.swap 2 5 * Equiv.swap 3 6

/-- Standard outcome ↦ original outcome. -/
def tau1 (F : Fin 13) : Equiv.Perm (Fin 3) :=
  if F.val = 0 then Equiv.refl _
  else if F.val < 7 then Equiv.neg PhaseIndex
  else if F.val < 10 then Equiv.subRight (((F.val - 7 : ℕ)) : PhaseIndex)
  else Equiv.subLeft (((F.val - 10 : ℕ)) : PhaseIndex)

/-! ## Reading the standard anchored form and the literal family frame by frame -/

theorem stdAnchored_quartet (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : UnitaryErrorBases.Family) (F : Fin 13) (k : Fin 4) (hF : F.val = k.val) (a : Fin 3) :
    stdAnchored q W (framePointIndex F a) = includeHermitianMatrix (q k a) := by
  have hv : (framePointIndex F a).val = 3 * F.val + a.val := framePointIndex_val F a
  have hk := k.isLt
  have ha := a.isLt
  unfold stdAnchored
  split_ifs with h
  · congr 2 <;> apply Fin.ext <;> simp only [hv] <;> omega
  · omega

theorem stdAnchored_hidden (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : UnitaryErrorBases.Family) (l : UnitaryErrorBases.Label) (F : Fin 13) (hF : hiddenFrame l = F)
    (a : Fin 3) :
    stdAnchored q W (framePointIndex F a) =
      nativeComplementaryPoint (UnitaryErrorBases.ThreeCycleFourier.character a • W l) := by
  subst hF
  have hk := (hiddenFrameEquiv l).isLt
  have ha := a.isLt
  have hv : (framePointIndex (hiddenFrame l) a).val = 3 * (4 + (hiddenFrameEquiv l).val) + a.val :=
    framePointIndex_val _ a
  unfold stdAnchored
  split_ifs with h
  · omega
  congr 2
  · change UnitaryErrorBases.ThreeCycleFourier.omega ^ _ =
      UnitaryErrorBases.ThreeCycleFourier.omega ^ a.val
    congr 1
    rw [hv]
    omega
  · congr 1
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    simp only [hv]
    omega

theorem lit_quartet (ξ : Fin 4 → ℂ) (k : Fin 4) (F : Fin 13) (hF : F.val = k.val) (t : Fin 3) :
    literalPoint ξ (framePointIndex F t) = includeHermitianMatrix (stdQuartet k t) := by
  rw [show F = Fin.castLE (by omega) k from Fin.ext (by simpa using hF)]
  exact literalPoint_quartet ξ k t

theorem lit_hidden (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (g : Fin 3) (s : PhaseIndex) (F : Fin 13)
    (hF : F.val = 4 + 3 * g.val + s.val) (t : Fin 3) (t' : PhaseIndex) (ht : idx t = t') :
    literalPoint ξ (framePointIndex F t) = nativeComplementaryPoint (hiddenMatrix ξ g s t') := by
  subst ht
  rw [show F = ⟨4 + 3 * g.val + s.val, by have := ZMod.val_lt s; omega⟩ from Fin.ext hF]
  exact literalPoint_hidden ξ hξ g s (idx t)

theorem stdQuartet_succ (s : PhaseIndex) (k : Fin 4) (hk : k.val = s.val + 1) (t : Fin 3) :
    (stdQuartet k t).val = phaseProjector s t := by
  rw [show k = ⟨s.val + 1, by have := ZMod.val_lt s; omega⟩ from Fin.ext hk]
  simp [stdQuartet]

/-! ## The form, group by group -/

theorem form_zero (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (a : Fin 3) :
    transportTinv 0 (literalPoint ξ (framePointIndex (fperm1 0) (tau1 0 a))) =
      stdAnchored q1 (W1 ξ hξ) (framePointIndex 0 a) := by
  rw [show fperm1 0 = 0 by decide, show tau1 0 a = a by simp [tau1],
    lit_quartet ξ 0 0 rfl, quartet_frame_zero, stdAnchored_quartet _ _ 0 0 rfl]

/-- Standard frames `1 + s`: original quartet frames `4 + s`, outcome `t ↦ −t`. -/
theorem form_quartet (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (s : PhaseIndex) (F : Fin 13) (k : Fin 4)
    (hF : F.val = s.val + 1) (hk : k.val = s.val + 1) (hperm : (fperm1 F).val = 4 + 3 * 0 + s.val)
    (hτ : ∀ a : Fin 3, idx (tau1 F a) = -idx a) (a : Fin 3) :
    transportTinv 0 (literalPoint ξ (framePointIndex (fperm1 F) (tau1 F a))) =
      stdAnchored q1 (W1 ξ hξ) (framePointIndex F a) := by
  rw [lit_hidden ξ hξ 0 s (fperm1 F) hperm (tau1 F a) _ (hτ a), quartet_frame_phase ξ s (idx a),
    stdAnchored_quartet _ _ F k (by omega)]
  congr 1
  apply Subtype.ext
  change _ = gQ * (stdQuartet k a).val * gQ.conjTranspose
  rw [stdQuartet_succ s k hk]
  rfl

/-- Standard frames `4 + s`: original frames `1 + s` (phase projectors), outcome `t ↦ −t`. -/
theorem form_A (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (s : PhaseIndex) (F : Fin 13) (k : Fin 4)
    (hF : hiddenFrame (0, s) = F) (hk : k.val = s.val + 1) (hperm : (fperm1 F).val = k.val)
    (hτ : ∀ a : Fin 3, idx (tau1 F a) = -idx a) (a : Fin 3) :
    transportTinv 0 (literalPoint ξ (framePointIndex (fperm1 F) (tau1 F a))) =
      stdAnchored q1 (W1 ξ hξ) (framePointIndex F a) := by
  rw [lit_quartet ξ k (fperm1 F) hperm (tau1 F a), stdAnchored_hidden _ _ (0, s) F hF a]
  have hP : stdQuartet k (tau1 F a) =
      ⟨phaseProjector s (-idx a), phaseProjector_isHermitian _ _⟩ := by
    apply Subtype.ext
    rw [stdQuartet_succ s k hk]
    change phaseProjector s (idx (tau1 F a)) = _
    rw [hτ a]
  rw [hP, hidden_frames_A ξ hξ s (idx a)]
  rfl

/-- Standard frames `7 + s`: original frames `7 + s`, outcome `t ↦ t − s`. -/
theorem form_B (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (s : PhaseIndex) (F : Fin 13)
    (hF : hiddenFrame (1, s) = F) (hperm : (fperm1 F).val = 4 + 3 * 1 + s.val)
    (hτ : ∀ a : Fin 3, idx (tau1 F a) = idx a - s) (a : Fin 3) :
    transportTinv 0 (literalPoint ξ (framePointIndex (fperm1 F) (tau1 F a))) =
      stdAnchored q1 (W1 ξ hξ) (framePointIndex F a) := by
  rw [lit_hidden ξ hξ 1 s (fperm1 F) hperm (tau1 F a) _ (hτ a), hidden_frames_B ξ hξ s (idx a),
    stdAnchored_hidden _ _ (1, s) F hF a]
  rfl

/-- Standard frames `10 + s`: original frames `10 + s`, outcome `t ↦ s − t`. -/
theorem form_C (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (s : PhaseIndex) (F : Fin 13)
    (hF : hiddenFrame (2, s) = F) (hperm : (fperm1 F).val = 4 + 3 * 2 + s.val)
    (hτ : ∀ a : Fin 3, idx (tau1 F a) = s - idx a) (a : Fin 3) :
    transportTinv 0 (literalPoint ξ (framePointIndex (fperm1 F) (tau1 F a))) =
      stdAnchored q1 (W1 ξ hξ) (framePointIndex F a) := by
  rw [lit_hidden ξ hξ 2 s (fperm1 F) hperm (tau1 F a) _ (hτ a), hidden_frames_C ξ hξ s (idx a),
    stdAnchored_hidden _ _ (2, s) F hF a]
  rfl

theorem form_frame (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (F : Fin 13) (a : Fin 3) :
    transportTinv 0 (literalPoint ξ (framePointIndex (fperm1 F) (tau1 F a))) =
      stdAnchored q1 (W1 ξ hξ) (framePointIndex F a) := by
  fin_cases F
  · exact form_zero ξ hξ a
  · exact form_quartet ξ hξ 0 _ 1 rfl rfl (by decide) (by decide) a
  · exact form_quartet ξ hξ 1 _ 2 rfl rfl (by decide) (by decide) a
  · exact form_quartet ξ hξ 2 _ 3 rfl rfl (by decide) (by decide) a
  · exact form_A ξ hξ 0 _ 1 (by decide) rfl (by decide) (by decide) a
  · exact form_A ξ hξ 1 _ 2 (by decide) rfl (by decide) (by decide) a
  · exact form_A ξ hξ 2 _ 3 (by decide) rfl (by decide) (by decide) a
  · exact form_B ξ hξ 0 _ (by decide) (by decide) (by decide) a
  · exact form_B ξ hξ 1 _ (by decide) (by decide) (by decide) a
  · exact form_B ξ hξ 2 _ (by decide) (by decide) (by decide) a
  · exact form_C ξ hξ 0 _ (by decide) (by decide) (by decide) a
  · exact form_C ξ hξ 1 _ (by decide) (by decide) (by decide) a
  · exact form_C ξ hξ 2 _ (by decide) (by decide) (by decide) a

theorem framePointIndex_eq_finProd (f : Fin 13) (a : Fin 3) :
    framePointIndex f a = (finProdFinEquiv : Fin 13 × Fin 3 ≃ Fin 39) (f, a) := by
  apply Fin.ext
  simp only [framePointIndex_val, finProdFinEquiv_apply_val]
  omega

theorem shift_compat1 (i : Fin 39) :
    outcomeShift shift1 (pointRelabel fperm1 tau1 i) = pointRelabel fperm1 tau1 (stdShift i) := by
  revert i
  decide

theorem q1_idem (k : Fin 4) (t : Fin 3) : (q1 k t).val * (q1 k t).val = (q1 k t).val := by
  have hg : gQ.conjTranspose * gQ = 1 := mul_eq_one_comm.mp gQ_unitary
  change gQ * (stdQuartet k t).val * gQ.conjTranspose * (gQ * (stdQuartet k t).val * gQ.conjTranspose) =
    gQ * (stdQuartet k t).val * gQ.conjTranspose
  calc _ = gQ * ((stdQuartet k t).val * (gQ.conjTranspose * gQ) * (stdQuartet k t).val) *
        gQ.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, Matrix.mul_one, stdQuartet_idem]

theorem q1_finrank : Module.finrank ℝ (quartetFirstOrder fun k t => (q1 k t).val) = 8 := by
  have h := finrank_quartetFirstOrder_conj (fun k t => (stdQuartet k t).val) gQ gQ_unitary
    (Equiv.refl _) (fun _ => Equiv.refl _)
  rw [finrank_quartetFirstOrder_std] at h
  exact h

end Anchor1

open Anchor1 in
theorem anchorBinding1_nonempty (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Nonempty (AnchorBinding (anchorGenerator 1) (anchorShift 1) (literalPoint ξ) (anchorTriple ξ hξ 1)) := by
  refine ⟨{
    Ψ := transportTinv 0
    Ψ_aut := transportTinv_isNativeAut 0
    Ψ_injective := ?_
    conj := ?_
    fperm := fperm1
    τ := tau1
    shift_compat := shift_compat1
    q := q1
    q_idem := q1_idem
    q_finrank := q1_finrank
    W := W1 ξ hξ
    W_ueb := W1_ueb ξ hξ
    W_finrank := W1_finrank ξ hξ
    form := ?_ }⟩
  · intro x y h
    have hx := LinearMap.congr_fun (transportT_comp_transportTinv 0) x
    have hy := LinearMap.congr_fun (transportT_comp_transportTinv 0) y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hx hy
    rw [← hx, ← hy, h]
  · change transportTinv 0 ∘ₗ (transportT 0 ∘ₗ R0 ∘ₗ transportTinv 0) = R0 ∘ₗ transportTinv 0
    rw [← LinearMap.comp_assoc, transportTinv_comp_transportT, LinearMap.id_comp]
  · intro i
    obtain ⟨⟨F, a⟩, rfl⟩ := (finProdFinEquiv : Fin 13 × Fin 3 ≃ Fin 39).surjective i
    rw [← framePointIndex_eq_finProd, pointRelabel_framePointIndex]
    exact form_frame ξ hξ F a

end CKM.NativeFirstOrder

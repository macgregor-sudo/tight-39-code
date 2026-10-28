module

public import KfixStdMain

@[expose] public section

/-!
# KFIX helper: the anchor-0 relabelling of the literal family

Negating the outcomes of the nine hidden frames turns `literalPoint ξ` into
`stdAnchored stdQuartet (kfW ξ)`, the shift of `R0` into `stdShift` and the shift of `R1` into
`kfShift1`.
-/

noncomputable section

namespace CKM.NativeFirstOrder

open NativePolynomial NativePolynomial.ConfigurationResiduals CompactAlbert
open UnitaryErrorBases.ComplexQuartet

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega
local notation "χ" => UnitaryErrorBases.ThreeCycleFourier.character

/-- Index reinterpretation `Fin 3 = ZMod 3`. -/
def kfToZ (a : Fin 3) : PhaseIndex := a

/-- Outcome relabelling: identity on frames 0–3, negation on frames 4–12. -/
def kfTau (f : Fin 13) : Equiv.Perm (Fin 3) :=
  if f.val < 4 then Equiv.refl _ else Equiv.neg (Fin 3)

/-- The anchor-0 point relabelling. -/
def kfPi : Equiv.Perm (Fin 39) := pointRelabel (Equiv.refl _) kfTau

theorem kfPi_apply (f : Fin 13) (a : Fin 3) :
    kfPi (framePointIndex f a) = framePointIndex f (kfTau f a) := by
  rw [kfPi, pointRelabel_framePointIndex]
  rfl

theorem kf_tau_shift0 : ∀ (f : Fin 13) (a : Fin 3),
    kfTau f (a + (fun f : Fin 13 => if f.val < 4 then (0 : Fin 3) else 2) f) = kfTau f a + shift0 f := by
  decide

theorem kf_tau_shift1 : ∀ (f : Fin 13) (a : Fin 3), kfTau f (a + kfShift1 f) = kfTau f a + shift1 f := by
  decide

theorem kfPi_shift (σ σ' : Fin 13 → Fin 3) (h : ∀ f a, kfTau f (a + σ' f) = kfTau f a + σ f)
    (i : Fin 39) : kfPi (outcomeShift σ' i) = outcomeShift σ (kfPi i) := by
  obtain ⟨f, a, rfl⟩ := kf_index_split i
  rw [kf_shift_apply, kfPi_apply, kfPi_apply, kf_shift_apply, h]

theorem kf_hiddenFrame_eq (l : UnitaryErrorBases.Label) :
    hiddenFrame l = ⟨4 + 3 * (kfToFin l.1).val + (l.2 : PhaseIndex).val, by
      have h1 := (kfToFin l.1).isLt; have h2 := ZMod.val_lt l.2; omega⟩ := by
  apply Fin.ext
  show 4 + ((kfToFin l.2).val + 3 * (kfToFin l.1).val) = 4 + 3 * (kfToFin l.1).val + ZMod.val l.2
  rw [show ZMod.val l.2 = (kfToFin l.2).val from rfl]
  omega

/-- The relabelled literal family is the standard anchored configuration, at every unit phase. -/
theorem kf_literal_std (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 39) :
    literalPoint ξ (kfPi i) = stdAnchored stdQuartet (kfW ξ) i := by
  obtain ⟨f, a, rfl⟩ := kf_index_split i
  rw [kfPi_apply]
  by_cases hf : f.val < 4
  · rw [kfTau, ite_eq_left hf, Equiv.refl_apply, kf_std_visible _ _ _ hf]
    exact literalPoint_quartet ξ ⟨f.val, hf⟩ a
  · obtain ⟨l, rfl⟩ := kf_exists_hidden f (by omega)
    rw [kfTau, ite_eq_right hf, kf_std_hidden]
    have h := literalPoint_hidden ξ hξ (kfToFin l.1) l.2 (-(kfToZ a))
    have h2 := kf_hidden_neg ξ (kfToFin l.1) l.2 (kfToZ a)
    rw [← kf_hiddenFrame_eq] at h
    calc _ = nativeComplementaryPoint (hiddenMatrix ξ (kfToFin l.1) l.2 (-(kfToZ a))) := h
      _ = nativeComplementaryPoint (χ (kfToZ a) • hiddenMatrix ξ (kfToFin l.1) l.2 0) := by rw [h2]
      _ = _ := rfl

/-- The relabelling transports the jointly fixed first-order spaces. -/
theorem kf_finrank_literal_eq (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ ↥(fixedSpace (compensated R0 (outcomeShift shift0)) ⊓
      fixedSpace (compensated R1 (outcomeShift shift1)) ⊓ firstOrderSystem (literalPoint ξ)) =
      Module.finrank ℝ (kfXstd ξ) := by
  let Φ : (Fin 39 → Glennie.Albert) ≃ₗ[ℝ] (Fin 39 → Glennie.Albert) :=
    LinearEquiv.funCongrLeft ℝ Glennie.Albert kfPi
  have hΦ : ∀ δ i, Φ δ i = δ (kfPi i) := fun _ _ => rfl
  have hcomm : ∀ (g : Glennie.Albert →ₗ[ℝ] Glennie.Albert) (σ σ' : Fin 13 → Fin 3),
      (∀ f a, kfTau f (a + σ' f) = kfTau f a + σ f) → ∀ δ,
      compensated g (outcomeShift σ') (Φ δ) = Φ (compensated g (outcomeShift σ) δ) := by
    intro g σ σ' h δ
    funext i
    rw [compensated_apply, hΦ, hΦ, compensated_apply, kfPi_shift σ σ' h]
  have hstd : (fun i => literalPoint ξ (kfPi i)) = stdAnchored stdQuartet (kfW ξ) :=
    funext (kf_literal_std ξ hξ)
  have key : ∀ δ, Φ δ ∈ kfXstd ξ ↔ δ ∈ fixedSpace (compensated R0 (outcomeShift shift0)) ⊓
      fixedSpace (compensated R1 (outcomeShift shift1)) ⊓ firstOrderSystem (literalPoint ξ) := by
    intro δ
    simp only [kfXstd, Submodule.mem_inf, mem_fixedSpace]
    rw [stdShift, hcomm R0 shift0 _ kf_tau_shift0, hcomm R1 shift1 kfShift1 kf_tau_shift1,
      Φ.injective.eq_iff, Φ.injective.eq_iff, ← hstd]
    have hrel := relabel_mem_firstOrderSystem_iff (Equiv.refl _) kfTau (literalPoint ξ) δ
    rw [show (fun i => δ (pointRelabel (Equiv.refl _) kfTau i)) = Φ δ from rfl] at hrel
    rw [show (fun i => literalPoint ξ (pointRelabel (Equiv.refl _) kfTau i)) =
      (fun i => literalPoint ξ (kfPi i)) from rfl] at hrel
    rw [hrel]
  have hmap : Submodule.map (Φ : (Fin 39 → Glennie.Albert) →ₗ[ℝ] (Fin 39 → Glennie.Albert))
      (fixedSpace (compensated R0 (outcomeShift shift0)) ⊓
        fixedSpace (compensated R1 (outcomeShift shift1)) ⊓ firstOrderSystem (literalPoint ξ)) =
      kfXstd ξ := by
    ext ε
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      exact (key δ).2 hδ
    · intro hε
      obtain ⟨δ, rfl⟩ := Φ.surjective ε
      exact ⟨δ, (key δ).1 hε, rfl⟩
  rw [← hmap]
  exact (Φ.submoduleMap _).finrank_eq

end CKM.NativeFirstOrder

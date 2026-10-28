module

public import KfixStd

@[expose] public section

/-!
# KFIX helper: the jointly fixed space of the standard anchor-0 configuration has dimension eight
-/

noncomputable section

namespace CKM.NativeFirstOrder

open NativePolynomial NativePolynomial.ConfigurationResiduals CompactAlbert
open UnitaryErrorBases.ComplexQuartet

local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega
local notation "χ" => UnitaryErrorBases.ThreeCycleFourier.character

theorem kfG_right_unitary : kfG * kfG.conjTranspose = 1 := mul_eq_one_comm.mp kfG_left_unitary

/-- `R1` with the shift `kfShift1` fixes the standard anchored configuration of the literal family. -/
theorem kf_R1_std (ξ : Fin 4 → ℂ) (i : Fin 39) :
    R1 (stdAnchored stdQuartet (kfW ξ) (outcomeShift kfShift1 i)) = stdAnchored stdQuartet (kfW ξ) i := by
  obtain ⟨f, a, rfl⟩ := kf_index_split i
  rw [kf_shift_apply]
  by_cases hf : f.val < 4
  · have hs : kfShift1 f = if (⟨f.val, hf⟩ : Fin 4) = 0 then 0 else 1 :=
      kf_shift_visible ⟨f.val, hf⟩
    rw [kf_std_visible _ _ _ hf, kf_std_visible _ _ _ hf]
    apply nativeTitsMatrixPair_injective
    rw [kf_pair_R1, includeHermitianMatrix_pair, includeHermitianMatrix_pair, Matrix.mul_zero,
      Matrix.zero_mul, hs]
    exact Prod.ext (kf_quartet_cov _ a) rfl
  · obtain ⟨l, rfl⟩ := kf_exists_hidden f (by omega)
    rw [kf_std_hidden, kf_std_hidden, kf_shift_hidden]
    show R1 (nativeComplementaryPoint (ω ^ (a + kfToFin l.1).val • kfWt ξ l)) =
      nativeComplementaryPoint (ω ^ a.val • kfWt ξ l)
    apply nativeTitsMatrixPair_injective
    rw [kf_pair_R1, nativeComplementaryPoint_pair, nativeComplementaryPoint_pair]
    refine Prod.ext ?_ ?_
    · show kfG * ((1 / 3 : ℂ) • (1 : TitsComplexMatrix)) * kfG.conjTranspose = _
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, kfG_right_unitary]
    · show kfG * ((1 / 3 : ℂ) • (ω ^ (a + kfToFin l.1).val • kfWt ξ l)) * kfH.conjTranspose =
        (1 / 3 : ℂ) • (ω ^ a.val • kfWt ξ l)
      have hadd : ω ^ (a + kfToFin l.1).val = ω ^ a.val * ω ^ (l.1).val :=
        kf_char_add (a : PhaseIndex) l.1
      conv_rhs => rw [kfW_cov ξ l]
      rw [hadd, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, smul_smul,
        smul_smul, smul_smul]
      congr 1
      ring

/-- The jointly fixed first-order space of the standard anchored configuration. -/
def kfXstd (ξ : Fin 4 → ℂ) : Submodule ℝ (Fin 39 → Glennie.Albert) :=
  fixedSpace (compensated R0 stdShift) ⊓ fixedSpace (compensated R1 (outcomeShift kfShift1)) ⊓
    firstOrderSystem (stdAnchored stdQuartet (kfW ξ))

theorem kf_comm (δ : Fin 39 → Glennie.Albert) :
    compensated R0 stdShift (compensated R1 (outcomeShift kfShift1) δ) =
      compensated R1 (outcomeShift kfShift1) (compensated R0 stdShift δ) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, compensated_mul, compensated_mul,
    R0_mul_R1_comm, stdShift, outcomeShift_mul, outcomeShift_mul, add_comm]

theorem kf_fst_mem (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (δ : kfXstd ξ) :
    (elimForward (δ : Fin 39 → Glennie.Albert)).1 ∈ quartetClockFixed := by
  have hδ : (δ : Fin 39 → Glennie.Albert) ∈ (fixedSpace (compensated R0 stdShift) ⊓ fixedSpace (compensated R1 (outcomeShift kfShift1)) ⊓
      firstOrderSystem (stdAnchored stdQuartet (kfW ξ))) := δ.2
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_fixedSpace (g := compensated R1 _)] at hδ
  obtain ⟨⟨h0, h1⟩, hfo⟩ := hδ
  refine ⟨(elimForward_mem stdQuartet (kfW ξ) stdQuartet_idem (kfW_ueb ξ hξ) h0 hfo).1, ?_⟩
  intro k t
  conv_lhs => rw [← h1]
  rw [kf_elim_R1_fst, kfG_eq_clockInv]

theorem kf_snd_mem (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (δ : kfXstd ξ) :
    (elimForward (δ : Fin 39 → Glennie.Albert)).2 ∈ kfS6 ξ := by
  have hδ : (δ : Fin 39 → Glennie.Albert) ∈ (fixedSpace (compensated R0 stdShift) ⊓ fixedSpace (compensated R1 (outcomeShift kfShift1)) ⊓
      firstOrderSystem (stdAnchored stdQuartet (kfW ξ))) := δ.2
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_fixedSpace (g := compensated R1 _)] at hδ
  obtain ⟨⟨h0, h1⟩, hfo⟩ := hδ
  refine ⟨(elimForward_mem stdQuartet (kfW ξ) stdQuartet_idem (kfW_ueb ξ hξ) h0 hfo).2, ?_⟩
  intro l
  conv_lhs => rw [← h1]
  rw [kf_elim_R1_snd h0]

/-- The elimination map on the jointly fixed space. -/
def kfE (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : kfXstd ξ →ₗ[ℝ] quartetClockFixed × kfS6 ξ :=
  LinearMap.prod
    (((LinearMap.fst ℝ _ _).comp (elimForward.comp (kfXstd ξ).subtype)).codRestrict _
      (kf_fst_mem ξ hξ))
    (((LinearMap.snd ℝ _ _).comp (elimForward.comp (kfXstd ξ).subtype)).codRestrict _
      (kf_snd_mem ξ hξ))

theorem kfE_injective (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Function.Injective (kfE ξ hξ) := by
  intro δ δ' h
  have hδ : (δ : Fin 39 → Glennie.Albert) ∈ (fixedSpace (compensated R0 stdShift) ⊓ fixedSpace (compensated R1 (outcomeShift kfShift1)) ⊓
      firstOrderSystem (stdAnchored stdQuartet (kfW ξ))) := δ.2
  have hδ' : (δ' : Fin 39 → Glennie.Albert) ∈ (fixedSpace (compensated R0 stdShift) ⊓ fixedSpace (compensated R1 (outcomeShift kfShift1)) ⊓
      firstOrderSystem (stdAnchored stdQuartet (kfW ξ))) := δ'.2
  rw [Submodule.mem_inf, Submodule.mem_inf] at hδ hδ'
  obtain ⟨⟨h0, _⟩, hfo⟩ := hδ
  obtain ⟨⟨h0', _⟩, hfo'⟩ := hδ'
  apply Subtype.ext
  refine elimForward_injOn stdQuartet (kfW ξ) stdQuartet_idem (kfW_ueb ξ hξ) h0 hfo h0' hfo' ?_
  exact Prod.ext (congrArg (fun z => (z.1 : Fin 4 → Fin 3 → TitsComplexMatrix)) h)
    (congrArg (fun z => (z.2 : UnitaryErrorBases.Family)) h)

theorem kfE_surjective (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Function.Surjective (kfE ξ hξ) := by
  rintro ⟨⟨x, hx⟩, ⟨V, hV⟩⟩
  obtain ⟨δ, h0, hfo, he⟩ := elimForward_surjOn stdQuartet (kfW ξ) stdQuartet_idem (kfW_ueb ξ hξ)
    (x, V) hx.1 hV.1
  set δ' := compensated R1 (outcomeShift kfShift1) δ with hδ'
  have h0' : δ' ∈ fixedSpace (compensated R0 stdShift) := by
    rw [mem_fixedSpace, hδ', kf_comm]
    rw [mem_fixedSpace] at h0
    rw [h0]
  have hfo' : δ' ∈ firstOrderSystem (stdAnchored stdQuartet (kfW ξ)) :=
    compensated_mem_firstOrderSystem R1 R1_isNativeAut kfShift1 _ (kf_R1_std ξ) hfo
  have he' : elimForward δ' = elimForward δ := by
    refine Prod.ext ?_ ?_
    · funext k t
      rw [kf_elim_R1_fst, he]
      exact (hx.2 k t).symm
    · funext l
      show kfT ((elimForward δ').2 l) = kfT ((elimForward δ).2 l)
      rw [kf_elim_R1_snd h0, he]
      exact (hV.2 l).symm
  have hδ : δ' = δ :=
    elimForward_injOn stdQuartet (kfW ξ) stdQuartet_idem (kfW_ueb ξ hξ) h0' hfo' h0 hfo he'
  have h1 : δ ∈ fixedSpace (compensated R1 (outcomeShift kfShift1)) := by
    rw [mem_fixedSpace]
    exact hδ
  refine ⟨⟨δ, ⟨h0, h1⟩, hfo⟩, ?_⟩
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · exact congrArg Prod.fst he
  · exact congrArg Prod.snd he

theorem kf_finrank_std (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Module.finrank ℝ (kfXstd ξ) = 8 := by
  rw [(LinearEquiv.ofBijective (kfE ξ hξ) ⟨kfE_injective ξ hξ, kfE_surjective ξ hξ⟩).finrank_eq,
    Module.finrank_prod, finrank_quartetClockFixed, kf_finrank_S6 ξ hξ]

end CKM.NativeFirstOrder

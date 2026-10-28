module

public import A5Misc

@[expose] public section

/-!
# The compensated `K`-action on configurations: invariance and fixed dimensions (piece KLIN)

`kAct H` (A4's `confGen`) fixes `P` at every unit phase (A3's `AnchorBinding.generator_fixes`),
intertwines the `G`-action with conjugation `kConj H`, and preserves `T` (A3/A4 `tanAction`),
`O` (`confGen_R0/R1_evalDer`) and `N = O^⊥` (native automorphisms preserve the trace pairing).
Hence `T = O ⊕ (T ∩ N)` `K`-stably and `dim Q^H = (26 + 2r_H) - 16`, `dim Q^K = 8 - 4`
(A4 `finrank_tanAction_fixH/K`, `finrank_orbit_fixH/K`), `dim (T ∩ N) = 80 - 52` at good phases.
Averaging projectors `P_H = (1 + k_H + k_H²)/3`, `P_K = (1/9) Σ k` satisfy `Σ_H P_H = 1 + 3 P_K`, so
`T ∩ N = Σ_H Q^H` (A3's `A3Averaging` projectors are private; build local ones).
-/

noncomputable section

open CKM.NativeFirstOrder CKM.NativeGroupSlice CompactAlbert UnitaryErrorBases
open scoped Matrix Topology

namespace CKM.NativeFourFamily

open CKM.NativeIntrinsicTriality NativePolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Helpers (piece KLIN) -/

theorem klin_R_commute : Commute R0 R1 := R0_mul_R1_comm

/-- Each anchor generator has order dividing three. -/
theorem klin_anchorGenerator_cube (H : Fin 4) : anchorGenerator H ^ 3 = 1 := by
  have h2 : ∀ m n : ℕ, (R0 ^ m * R1 ^ n) ^ 3 = 1 := fun m n => by
    rw [(klin_R_commute.pow_pow m n).mul_pow, ← pow_mul, ← pow_mul, mul_comm m 3, mul_comm n 3,
      pow_mul, pow_mul, R0_cube, R1_cube, one_pow, one_pow, one_mul]
  match H with
  | 0 => exact R0_cube
  | 1 => exact R1_cube
  | 2 => exact h2 2 2
  | 3 =>
    have h := h2 2 1
    rw [pow_one] at h
    exact h

theorem klin_kAct_apply (H : Fin 4) (C : Cfg) (i : Fin 39) :
    kAct H C i = coordEnd (anchorGenerator H) (C (outcomeShift (anchorShift H) i)) := rfl

theorem klin_coordEnd_sq_mul (H : Fin 4) :
    coordEnd (anchorGenerator H ^ 2) * coordEnd (anchorGenerator H) = 1 := by
  rw [← map_mul, ← pow_succ, klin_anchorGenerator_cube, map_one]

theorem klin_coordEnd_mul_sq (H : Fin 4) :
    coordEnd (anchorGenerator H) * coordEnd (anchorGenerator H ^ 2) = 1 := by
  rw [← map_mul, ← pow_succ', klin_anchorGenerator_cube, map_one]

theorem klin_coordEnd_mem_autC {g : Module.End ℝ Glennie.Albert} (hg : IsNativeAut g)
    (hg3 : g ^ 3 = 1) : coordEnd g ∈ autC := by
  rw [mem_autC_iff_isNativeAut, AlgEquiv.symm_apply_apply]
  refine ⟨⟨fun x y hxy => ?_, fun y => ⟨(g ^ 2) y, ?_⟩⟩, hg⟩
  · have := congrArg (fun z => (g ^ 2) z) hxy
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_succ, hg3] at this
  · rw [← Module.End.mul_apply, ← pow_succ', hg3, Module.End.one_apply]

theorem klin_isNativeAut_sq (H : Fin 4) : IsNativeAut (anchorGenerator H ^ 2) := by
  rw [pow_two]
  exact isNativeAut_mul (isNativeAut_anchorGenerator H) (isNativeAut_anchorGenerator H)

theorem klin_sq_cube (H : Fin 4) : (anchorGenerator H ^ 2) ^ 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, klin_anchorGenerator_cube, one_pow]

theorem klin_fixes {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) (i : Fin 39) :
    anchorGenerator H (literalPoint ξ (outcomeShift (anchorShift H) i)) = literalPoint ξ i :=
  (anchorBinding_nonempty ξ hξ H).some.generator_fixes i

/-- The compensated action preserves the configuration trace pairing. -/
theorem klin_cfgPairing_kAct (H : Fin 4) (C C' : Cfg) :
    cfgPairing (kAct H C) (kAct H C') = cfgPairing C C' := by
  have hg := isNativeAut_anchorGenerator H
  rw [cfgPairing_eq_trace, cfgPairing_eq_trace]
  have h : ∀ i, Glennie.trace (Glennie.jordan (fromUpperCoordinates (kAct H C i))
      (fromUpperCoordinates (kAct H C' i))) =
      Glennie.trace (Glennie.jordan (fromUpperCoordinates (C (outcomeShift (anchorShift H) i)))
        (fromUpperCoordinates (C' (outcomeShift (anchorShift H) i)))) := fun i => by
    rw [klin_kAct_apply, klin_kAct_apply, coordEnd_apply, coordEnd_apply,
      fromUpperCoordinates_upperCoordinates, fromUpperCoordinates_upperCoordinates, ← hg.jordan,
      hg.trace]
  rw [Finset.sum_congr rfl fun i _ => h i]
  exact Equiv.sum_comp (outcomeShift (anchorShift H)) (fun j => Glennie.trace (Glennie.jordan
    (fromUpperCoordinates (C j)) (fromUpperCoordinates (C' j))))

theorem klin_kAct_mem_orbitC {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) {C : Cfg}
    (hC : C ∈ orbitC ξ) : kAct H C ∈ orbitC ξ := by
  rw [orbitC_eq_orbitSpace] at hC ⊢
  obtain ⟨D, hD, rfl⟩ := hC
  refine ⟨conjAct (anchorGenerator H) D, conjAct_mem_jordanDerivations
    (isNativeAut_anchorGenerator H) (klin_anchorGenerator_cube H) hD, ?_⟩
  exact (confGen_evalDer_of_fixes ξ (klin_anchorGenerator_cube H) (klin_fixes hξ H) D).symm

theorem klin_kAct_cube_apply (H : Fin 4) (C : Cfg) : kAct H (kAct H (kAct H C)) = C := by
  have h : kAct H ^ 3 = 1 := confGen_cube _ _ (klin_anchorGenerator_cube H)
  have := LinearMap.congr_fun h C
  rwa [pow_three, Module.End.mul_apply, Module.End.mul_apply, Module.End.one_apply] at this


theorem kAct_literalCfg {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    kAct H (literalCfg ξ) = literalCfg ξ := by
  funext i
  rw [klin_kAct_apply, coordEnd_apply]
  show upperCoordinates (anchorGenerator H (fromUpperCoordinates
    (upperCoordinates (literalPoint ξ _)))) = upperCoordinates (literalPoint ξ i)
  rw [fromUpperCoordinates_upperCoordinates, klin_fixes hξ H i]

theorem kAct_actC (H : Fin 4) (A : CEnd) (C : Cfg) :
    kAct H (actC A C) = actC (kConj H A) (kAct H C) := by
  funext i
  have h : ∀ c, coordEnd (anchorGenerator H ^ 2) (coordEnd (anchorGenerator H) c) = c := fun c =>
    congrArg (fun F : CEnd => F c) (klin_coordEnd_sq_mul H)
  rw [klin_kAct_apply, actC_apply, actC_apply, klin_kAct_apply]
  change _ = coordEnd (anchorGenerator H) (A (coordEnd (anchorGenerator H ^ 2)
    (coordEnd (anchorGenerator H) (C (outcomeShift (anchorShift H) i)))))
  rw [h]

theorem kConj_mem_autC (H : Fin 4) {A : CEnd} (hA : A ∈ autC) : kConj H A ∈ autC :=
  mul_mem_autOf (mul_mem_autOf (klin_coordEnd_mem_autC (isNativeAut_anchorGenerator H)
    (klin_anchorGenerator_cube H)) hA) (klin_coordEnd_mem_autC (klin_isNativeAut_sq H)
    (klin_sq_cube H))

theorem kConj_one (H : Fin 4) : kConj H 1 = 1 := by
  rw [kConj, mul_one, klin_coordEnd_mul_sq]

theorem continuous_kConj (H : Fin 4) : Continuous (kConj H) :=
  (continuous_const.mul continuous_id).mul continuous_const

theorem kAct_mem_normalC {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) {C : Cfg}
    (hC : C ∈ normalC ξ) : kAct H C ∈ normalC ξ := by
  rw [mem_normalC_iff] at hC ⊢
  intro u hu
  have hu' : kAct H (kAct H u) ∈ orbitC ξ :=
    klin_kAct_mem_orbitC hξ H (klin_kAct_mem_orbitC hξ H hu)
  rw [← klin_kAct_cube_apply H u, klin_cfgPairing_kAct]
  exact hC _ hu' 

theorem kAct_mem_orbitC {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) {C : Cfg}
    (hC : C ∈ orbitC ξ) : kAct H C ∈ orbitC ξ :=
  klin_kAct_mem_orbitC hξ H hC

theorem kAct_mem_tangentSpace {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) {C : Cfg}
    (hC : C ∈ tangentSpace ξ) : kAct H C ∈ tangentSpace ξ :=
  confGen_anchor_mem ξ hξ H hC

theorem kAct_cube (H : Fin 4) : kAct H ^ 3 = 1 := confGen_cube _ _ (klin_anchorGenerator_cube H)

theorem kAct_comm : kAct 0 * kAct 1 = kAct 1 * kAct 0 := confGen_comm

theorem kAct_two : kAct 2 = kAct 0 ^ 2 * kAct 1 ^ 2 := (confGen_word 2 2 compensated_anchor2).symm

theorem kAct_three : kAct 3 = kAct 0 ^ 2 * kAct 1 := by
  rw [← pow_one (kAct 1)]
  exact (confGen_word 2 1 compensated_anchor3).symm

/-! ## Linear-algebra helpers (piece KLIN) -/

/-- Unnormalised averaging operator `1 + g + g²`. -/
def klinAvg {V : Type*} [AddCommGroup V] [Module ℝ V] (g : Module.End ℝ V) : Module.End ℝ V :=
  1 + g + g ^ 2

theorem klinAvg_fixed {V : Type*} [AddCommGroup V] [Module ℝ V] {g : Module.End ℝ V}
    (hg : g ^ 3 = 1) (v : V) : g (klinAvg g v) = klinAvg g v := by
  have h3 : g * g ^ 2 = 1 := by rw [← pow_succ']; exact hg
  rw [← Module.End.mul_apply, klinAvg, mul_add, mul_add, mul_one, ← pow_two, h3]
  congr 1
  abel

theorem klinAvg_of_fixed {V : Type*} [AddCommGroup V] [Module ℝ V] {g : Module.End ℝ V} {v : V}
    (hv : g v = v) : klinAvg g v = (3 : ℝ) • v := by
  rw [klinAvg, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, pow_two,
    Module.End.mul_apply, hv, hv, show (3 : ℝ) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]

theorem klinAvg_mem {V : Type*} [AddCommGroup V] [Module ℝ V] {g : Module.End ℝ V}
    {S : Submodule ℝ V} (hS : ∀ x ∈ S, g x ∈ S) {v : V} (hv : v ∈ S) : klinAvg g v ∈ S := by
  rw [klinAvg, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, pow_two,
    Module.End.mul_apply]
  exact S.add_mem (S.add_mem hv (hS _ hv)) (hS _ (hS _ hv))

theorem klinAvg_commute {V : Type*} [AddCommGroup V] [Module ℝ V] {g h : Module.End ℝ V}
    (hc : Commute g h) : Commute (klinAvg g) h :=
  ((Commute.one_left h).add_left hc).add_left (hc.pow_left 2)

/-- Splitting the fixed part of an invariant subspace along an invariant complement, given an
idempotent-like averaging map `P` onto the fixed space `F`. -/
theorem klin_finrank_split {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (F U W S : Submodule ℝ V) (P : Module.End ℝ V) (hPF : ∀ v, P v ∈ F)
    (hPid : ∀ v ∈ F, P v = v) (hPU : ∀ v ∈ U, P v ∈ U) (hPS : ∀ v ∈ S ⊓ W, P v ∈ S ⊓ W)
    (hUS : U ≤ S) (hc : IsCompl U W) :
    Module.finrank ℝ ↥(F ⊓ S) = Module.finrank ℝ ↥(F ⊓ U) + Module.finrank ℝ ↥(F ⊓ (S ⊓ W)) := by
  have hsup : F ⊓ U ⊔ F ⊓ (S ⊓ W) = F ⊓ S := by
    refine le_antisymm (sup_le (inf_le_inf_left _ hUS) (inf_le_inf_left _ inf_le_left)) ?_
    intro v hv
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1
      (hc.sup_eq_top.symm ▸ Submodule.mem_top : v ∈ U ⊔ W)
    have hwS : w ∈ S := by
      have := S.sub_mem hv.2 (hUS hu)
      rwa [add_sub_cancel_left] at this
    rw [← hPid _ hv.1, map_add]
    exact Submodule.add_mem_sup ⟨hPF u, hPU u hu⟩ ⟨hPF w, hPS w ⟨hwS, hw⟩⟩
  have hinf : F ⊓ U ⊓ F ⊓ (S ⊓ W) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    exact (Submodule.disjoint_def.1 hc.disjoint) v hv.1.1.2 hv.2.2
  have h := Submodule.finrank_sup_add_finrank_inf_eq (F ⊓ U) (F ⊓ (S ⊓ W))
  rw [hsup, ← inf_assoc, hinf, finrank_bot, add_zero] at h
  exact h

theorem klin_orbitC_le {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) : orbitC ξ ≤ tangentSpace ξ := by
  rw [orbitC_eq_orbitSpace]
  exact orbitSpace_le_tangentSpace ξ hξ

theorem klin_tanN_mem {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) {C : Cfg}
    (hC : C ∈ tanN ξ) : kAct H C ∈ tanN ξ :=
  ⟨kAct_mem_tangentSpace hξ H hC.1, kAct_mem_normalC hξ H hC.2⟩

theorem klin_finrank_fixT {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    Module.finrank ℝ ↥(fixedSpace (kAct H) ⊓ tangentSpace ξ) =
      26 + 2 * resonanceCount (anchorTriple ξ hξ H) := by
  have h := finrank_tanAction_fixH ξ hξ H
  rw [KAction.fixH, tanAction_gen_eq, finrank_fixedSpace_restrict] at h
  exact h

theorem klin_finrank_fixO {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    Module.finrank ℝ ↥(fixedSpace (kAct H) ⊓ orbitC ξ) = 16 := by
  have h := finrank_orbit_fixH ξ hξ H
  rw [finrank_fixH_restrict, KAction.fixH, tanAction_gen_eq, fixedSpace_restrict_eq, orbitInT,
    ← Submodule.comap_inf, inf_assoc, inf_of_le_right (orbitSpace_le_tangentSpace ξ hξ)] at h
  rw [orbitC_eq_orbitSpace, ← h]
  exact ((Submodule.comapSubtypeEquivOfLe
    (inf_le_right.trans (orbitSpace_le_tangentSpace ξ hξ) :
      fixedSpace (kAct H) ⊓ orbitSpace ξ ≤ tangentSpace ξ)).finrank_eq).symm

theorem klin_finrank_fixKT {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ ↥(fixedSpace (kAct 0) ⊓ fixedSpace (kAct 1) ⊓ tangentSpace ξ) = 8 := by
  have h := finrank_tanAction_fixK ξ hξ
  rw [KAction.fixK, tanAction_g0, tanAction_g1, finrank_fixedSpace_restrict_inf] at h
  exact h

theorem klin_finrank_fixKO {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ ↥(fixedSpace (kAct 0) ⊓ fixedSpace (kAct 1) ⊓ orbitC ξ) = 4 := by
  have h := finrank_orbit_fixK ξ hξ
  rw [finrank_fixK_restrict, KAction.fixK, tanAction_g0, tanAction_g1, fixedSpace_restrict_eq,
    fixedSpace_restrict_eq, orbitInT, ← Submodule.comap_inf, ← Submodule.comap_inf] at h
  have hle : fixedSpace (kAct 0) ⊓ fixedSpace (kAct 1) ⊓ orbitSpace ξ ≤ tangentSpace ξ :=
    inf_le_right.trans (orbitSpace_le_tangentSpace ξ hξ)
  have heq : fixedSpace (confGen R0 shift0) ⊓ tangentSpace ξ ⊓
      (fixedSpace (confGen R1 shift1) ⊓ tangentSpace ξ) ⊓ orbitSpace ξ =
      fixedSpace (kAct 0) ⊓ fixedSpace (kAct 1) ⊓ orbitSpace ξ := by
    ext v
    simp only [Submodule.mem_inf]
    constructor
    · rintro ⟨⟨⟨h0, _⟩, h1, _⟩, hO⟩
      exact ⟨⟨h0, h1⟩, hO⟩
    · rintro ⟨⟨h0, h1⟩, hO⟩
      exact ⟨⟨⟨h0, orbitSpace_le_tangentSpace ξ hξ hO⟩, h1, orbitSpace_le_tangentSpace ξ hξ hO⟩, hO⟩
  rw [heq] at h
  rw [orbitC_eq_orbitSpace]
  exact ((Submodule.comapSubtypeEquivOfLe hle).finrank_eq).symm.trans h

theorem klin_resonance_zero {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (H : Fin 4) :
    resonanceCount (anchorTriple ξ hξ.1 H) = 0 := by
  rw [CKM.NativeGroupSliceConsumer.resonanceCount_anchorTriple, ite_eq_right (hξ.2 H 0),
    ite_eq_right (hξ.2 H 1), ite_eq_right (hξ.2 H 2)]

theorem klin_of_sq {V : Type*} [AddCommGroup V] [Module ℝ V] {g : Module.End ℝ V}
    (hg : ∀ x, g (g (g x)) = x) {v : V} (h : g (g v) = v) : g v = v :=
  calc g v = g (g (g (g v))) := (hg (g v)).symm
    _ = g (g v) := by rw [h]; exact h
    _ = v := h

theorem klin_cube_apply (H : Fin 4) (x : Cfg) : kAct H (kAct H (kAct H x)) = x :=
  klin_kAct_cube_apply H x

theorem klin_kAct_two_apply (x : Cfg) : kAct 2 x = kAct 0 (kAct 0 (kAct 1 (kAct 1 x))) := by
  rw [kAct_two, pow_two, pow_two, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply]

theorem klin_kAct_three_apply (x : Cfg) : kAct 3 x = kAct 0 (kAct 0 (kAct 1 x)) := by
  rw [kAct_three, pow_two, Module.End.mul_apply, Module.End.mul_apply]

theorem klin_comm_apply (x : Cfg) : kAct 1 (kAct 0 x) = kAct 0 (kAct 1 x) :=
  (LinearMap.congr_fun kAct_comm x).symm

theorem klin_fix_all {v : Cfg} (h0 : kAct 0 v = v) (h1 : kAct 1 v = v) (H : Fin 4) :
    kAct H v = v := by
  match H with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => rw [klin_kAct_two_apply, h1, h1, h0, h0]
  | 3 => rw [klin_kAct_three_apply, h1, h0, h0]

/-- Two distinct anchor generators generate `K`: their common fixed vectors are `K`-fixed. -/
theorem klin_fix_pair {H H' : Fin 4} (hHH' : H ≠ H') {v : Cfg} (hH : kAct H v = v)
    (hH' : kAct H' v = v) : kAct 0 v = v ∧ kAct 1 v = v := by
  have c0 := klin_cube_apply 0
  have c1 := klin_cube_apply 1
  -- (0,2)
  have p02 : kAct 0 v = v → kAct 2 v = v → kAct 1 v = v := fun ha h2 => by
    rw [klin_kAct_two_apply] at h2
    have hb : kAct 1 (kAct 1 v) = v := by
      have := congrArg (kAct 0) h2
      rwa [c0, ha] at this
    exact klin_of_sq c1 hb
  have p03 : kAct 0 v = v → kAct 3 v = v → kAct 1 v = v := fun ha h3 => by
    rw [klin_kAct_three_apply] at h3
    have := congrArg (kAct 0) h3
    rwa [c0, ha] at this
  have p12 : kAct 1 v = v → kAct 2 v = v → kAct 0 v = v := fun hb h2 => by
    rw [klin_kAct_two_apply, hb, hb] at h2
    exact klin_of_sq c0 h2
  have p13 : kAct 1 v = v → kAct 3 v = v → kAct 0 v = v := fun hb h3 => by
    rw [klin_kAct_three_apply, hb] at h3
    exact klin_of_sq c0 h3
  have p23 : kAct 2 v = v → kAct 3 v = v → kAct 0 v = v ∧ kAct 1 v = v := fun h2 h3 => by
    rw [klin_kAct_two_apply] at h2
    rw [klin_kAct_three_apply] at h3
    have e3 : kAct 1 v = kAct 0 v := by
      have := congrArg (kAct 0) h3
      rwa [c0] at this
    have e2 : kAct 1 (kAct 1 v) = kAct 0 v := by
      have := congrArg (kAct 0) h2
      rwa [c0] at this
    have e : kAct 0 (kAct 0 v) = kAct 0 v :=
      calc kAct 0 (kAct 0 v) = kAct 0 (kAct 1 v) := by rw [e3]
        _ = kAct 1 (kAct 0 v) := (klin_comm_apply v).symm
        _ = kAct 1 (kAct 1 v) := by rw [e3]
        _ = kAct 0 v := e2
    have ha : kAct 0 v = v := by
      have := congrArg (kAct 0) e
      rw [c0, e] at this
      exact this.symm
    exact ⟨ha, e3.trans ha⟩
  match H, H', hHH' with
  | 0, 1, _ => exact ⟨hH, hH'⟩
  | 1, 0, _ => exact ⟨hH', hH⟩
  | 0, 2, _ => exact ⟨hH, p02 hH hH'⟩
  | 2, 0, _ => exact ⟨hH', p02 hH' hH⟩
  | 0, 3, _ => exact ⟨hH, p03 hH hH'⟩
  | 3, 0, _ => exact ⟨hH', p03 hH' hH⟩
  | 1, 2, _ => exact ⟨p12 hH hH', hH⟩
  | 2, 1, _ => exact ⟨p12 hH' hH, hH'⟩
  | 1, 3, _ => exact ⟨p13 hH hH', hH⟩
  | 3, 1, _ => exact ⟨p13 hH' hH, hH'⟩
  | 2, 3, _ => exact p23 hH hH'
  | 3, 2, _ => exact p23 hH' hH
  | 0, 0, h => exact absurd rfl h
  | 1, 1, h => exact absurd rfl h
  | 2, 2, h => exact absurd rfl h
  | 3, 3, h => exact absurd rfl h

/-- The ring identity behind `Σ_H P_H = 1 + 3 P_K` for `K = C₃ × C₃`. -/
theorem klin_ring_id {V : Type*} [AddCommGroup V] [Module ℝ V] (a b : Module.End ℝ V) (hc : Commute a b) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) :
    (1 + a + a ^ 2) + (1 + b + b ^ 2) + (1 + a ^ 2 * b ^ 2 + (a ^ 2 * b ^ 2) ^ 2) +
        (1 + a ^ 2 * b + (a ^ 2 * b) ^ 2) =
      1 + 1 + 1 + (1 + a + a ^ 2) * (1 + b + b ^ 2) := by
  have ha4 : a ^ (2 * 2) = a := by rw [show 2 * 2 = 3 + 1 from rfl, pow_succ, ha, one_mul]
  have hb4 : b ^ (2 * 2) = b := by rw [show 2 * 2 = 3 + 1 from rfl, pow_succ, hb, one_mul]
  have h2 : (a ^ 2 * b ^ 2) ^ 2 = a * b := by
    rw [(hc.pow_pow 2 2).mul_pow, ← pow_mul, ← pow_mul, ha4, hb4]
  have h3 : (a ^ 2 * b) ^ 2 = a * b ^ 2 := by
    rw [(hc.pow_left 2).mul_pow, ← pow_mul, ha4]
  rw [h2, h3]
  simp only [add_mul, mul_add, one_mul, mul_one]
  abel

/-- The operator identity `Σ_H (1 + k_H + k_H²) = 3 + (1 + k₀ + k₀²)(1 + k₁ + k₁²)`: each
nonidentity element of `K = C₃ × C₃` lies in exactly one of the four order-three subgroups. -/
theorem klin_avg_sum :
    klinAvg (kAct 0) + klinAvg (kAct 1) + klinAvg (kAct 2) + klinAvg (kAct 3) =
      1 + 1 + 1 + klinAvg (kAct 0) * klinAvg (kAct 1) := by
  have e := klin_ring_id (kAct 0) (kAct 1) kAct_comm (kAct_cube 0) (kAct_cube 1)
  simp only [klinAvg, kAct_two, kAct_three]
  generalize kAct 0 = a at e ⊢
  generalize kAct 1 = b at e ⊢
  exact e

theorem finrank_tanN {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) : Module.finrank ℝ ↥(tanN ξ) = 28 := by
  have hu := hξ.1
  have hT : Module.finrank ℝ ↥(tangentSpace ξ) = 80 := by
    rw [finrank_tangentSpace ξ hu, Finset.sum_eq_zero fun H _ => klin_resonance_zero hξ H]
    norm_num
  have htop : tangentSpace ξ ⊔ normalC ξ = ⊤ := by
    rw [eq_top_iff, ← (isCompl_orbitC_normalC ξ hu).sup_eq_top]
    exact sup_le_sup_right (klin_orbitC_le hu) _
  have h := Submodule.finrank_sup_add_finrank_inf_eq (tangentSpace ξ) (normalC ξ)
  rw [htop, finrank_top, finrank_cfg, hT, finrank_normalC ξ hu] at h
  rw [tanN]
  exact Nat.add_left_cancel (h.trans (by norm_num : 80 + 1001 = 1053 + 28))

theorem finrank_fixQ {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) (H : Fin 4) :
    Module.finrank ℝ ↥(fixQ ξ H) = 10 := by
  have hu := hξ.1
  have h := klin_finrank_split (fixedSpace (kAct H)) (orbitC ξ) (normalC ξ) (tangentSpace ξ)
    ((3 : ℝ)⁻¹ • klinAvg (kAct H))
    (fun v => by
      rw [mem_fixedSpace, LinearMap.smul_apply, map_smul, klinAvg_fixed (kAct_cube H)])
    (fun v hv => by
      rw [LinearMap.smul_apply, klinAvg_of_fixed (mem_fixedSpace.1 hv), smul_smul,
        inv_mul_cancel₀ (by norm_num : (3 : ℝ) ≠ 0), one_smul])
    (fun v hv => Submodule.smul_mem _ _ (klinAvg_mem (fun _ hx => klin_kAct_mem_orbitC hu H hx) hv))
    (fun v hv => Submodule.smul_mem _ _ (klinAvg_mem (fun _ hx => klin_tanN_mem hu H hx) hv))
    (klin_orbitC_le hu) (isCompl_orbitC_normalC ξ hu)
  rw [klin_finrank_fixT hu, klin_finrank_fixO hu, klin_resonance_zero hξ] at h
  rw [fixQ, inf_comm]
  change Module.finrank ℝ ↥(fixedSpace (kAct H) ⊓ (tangentSpace ξ ⊓ normalC ξ)) = 10
  exact Nat.add_left_cancel (h.symm.trans (by norm_num : 26 + 2 * 0 = 16 + 10))

theorem finrank_fixQK {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) : Module.finrank ℝ ↥(fixQK ξ) = 4 := by
  have hu := hξ.1
  have hc : Commute (kAct 0) (kAct 1) := kAct_comm
  have hfix0 : ∀ v, kAct 0 (klinAvg (kAct 0) (klinAvg (kAct 1) v)) =
      klinAvg (kAct 0) (klinAvg (kAct 1) v) := fun v => klinAvg_fixed (kAct_cube 0) _
  have hfix1 : ∀ v, kAct 1 (klinAvg (kAct 0) (klinAvg (kAct 1) v)) =
      klinAvg (kAct 0) (klinAvg (kAct 1) v) := fun v => by
    rw [← Module.End.mul_apply, ← (klinAvg_commute hc).eq, Module.End.mul_apply,
      klinAvg_fixed (kAct_cube 1)]
  have h := klin_finrank_split (fixedSpace (kAct 0) ⊓ fixedSpace (kAct 1)) (orbitC ξ) (normalC ξ)
    (tangentSpace ξ) (((3 : ℝ)⁻¹ * (3 : ℝ)⁻¹) • (klinAvg (kAct 0) * klinAvg (kAct 1)))
    (fun v => by
      rw [LinearMap.smul_apply, Module.End.mul_apply]
      exact Submodule.smul_mem _ _ ⟨mem_fixedSpace.2 (hfix0 v), mem_fixedSpace.2 (hfix1 v)⟩)
    (fun v hv => by
      rw [LinearMap.smul_apply, Module.End.mul_apply,
        klinAvg_of_fixed (mem_fixedSpace.1 hv.2), map_smul,
        klinAvg_of_fixed (mem_fixedSpace.1 hv.1), smul_smul, smul_smul]
      rw [show (3 : ℝ)⁻¹ * (3 : ℝ)⁻¹ * 3 * 3 = 1 by norm_num, one_smul])
    (fun v hv => by
      rw [LinearMap.smul_apply, Module.End.mul_apply]
      exact Submodule.smul_mem _ _ (klinAvg_mem (fun _ hx => klin_kAct_mem_orbitC hu 0 hx)
        (klinAvg_mem (fun _ hx => klin_kAct_mem_orbitC hu 1 hx) hv)))
    (fun v hv => by
      rw [LinearMap.smul_apply, Module.End.mul_apply]
      exact Submodule.smul_mem _ _ (klinAvg_mem (fun _ hx => klin_tanN_mem hu 0 hx)
        (klinAvg_mem (fun _ hx => klin_tanN_mem hu 1 hx) hv)))
    (klin_orbitC_le hu) (isCompl_orbitC_normalC ξ hu)
  rw [klin_finrank_fixKT hu, klin_finrank_fixKO hu] at h
  have heq : fixQK ξ = fixedSpace (kAct 0) ⊓ fixedSpace (kAct 1) ⊓ (tangentSpace ξ ⊓ normalC ξ) := by
    ext v
    simp only [fixQK, tanN, Submodule.mem_inf]
    tauto
  rw [heq]
  exact Nat.add_left_cancel (h.symm.trans (by norm_num : 8 = 4 + 4))

theorem iSup_fixQ {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) : ⨆ H, fixQ ξ H = tanN ξ := by
  refine le_antisymm (iSup_le fun H => inf_le_left) fun v hv => ?_
  have hmem : ∀ H, klinAvg (kAct H) v ∈ fixQ ξ H := fun H =>
    ⟨klinAvg_mem (fun _ hx => klin_tanN_mem hξ H hx) hv,
      mem_fixedSpace.2 (klinAvg_fixed (kAct_cube H) v)⟩
  have hu : klinAvg (kAct 0) (klinAvg (kAct 1) v) ∈ fixQ ξ 0 :=
    ⟨klinAvg_mem (fun _ hx => klin_tanN_mem hξ 0 hx)
      (klinAvg_mem (fun _ hx => klin_tanN_mem hξ 1 hx) hv),
      mem_fixedSpace.2 (klinAvg_fixed (kAct_cube 0) _)⟩
  have hs := LinearMap.congr_fun klin_avg_sum v
  simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply] at hs
  have h3 : v = (3 : ℝ)⁻¹ • (klinAvg (kAct 0) v + klinAvg (kAct 1) v + klinAvg (kAct 2) v +
      klinAvg (kAct 3) v - klinAvg (kAct 0) (klinAvg (kAct 1) v)) := by
    rw [hs, add_sub_cancel_right, ← one_smul ℝ v, ← add_smul, ← add_smul, smul_smul]
    norm_num
  rw [h3]
  refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ (Submodule.mem_iSup_of_mem 0 hu))
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.mem_iSup_of_mem 0 (hmem 0)) (Submodule.mem_iSup_of_mem 1 (hmem 1)))
    (Submodule.mem_iSup_of_mem 2 (hmem 2))) (Submodule.mem_iSup_of_mem 3 (hmem 3))

theorem fixQK_eq_iInf (ξ : Fin 4 → ℂ) : fixQK ξ = ⨅ H, fixQ ξ H := by
  ext v
  simp only [fixQK, fixQ, Submodule.mem_iInf, Submodule.mem_inf, mem_fixedSpace]
  exact ⟨fun ⟨⟨hT, h0⟩, h1⟩ H => ⟨hT, klin_fix_all h0 h1 H⟩,
    fun h => ⟨⟨(h 0).1, (h 0).2⟩, (h 1).2⟩⟩

/-- Two distinct anchors already cut out `Q^K` (their generators generate `K`). -/
theorem fixQ_inf_fixQ {ξ : Fin 4 → ℂ} {H H' : Fin 4} (hHH' : H ≠ H') :
    fixQ ξ H ⊓ fixQ ξ H' = fixQK ξ := by
  ext v
  simp only [fixQK, fixQ, Submodule.mem_inf, mem_fixedSpace]
  constructor
  · rintro ⟨⟨hT, hH⟩, -, hH'⟩
    obtain ⟨h0, h1⟩ := klin_fix_pair hHH' hH hH'
    exact ⟨⟨hT, h0⟩, h1⟩
  · rintro ⟨⟨hT, h0⟩, h1⟩
    exact ⟨⟨hT, klin_fix_all h0 h1 H⟩, hT, klin_fix_all h0 h1 H'⟩

end CKM.NativeFourFamily

#print axioms CKM.NativeFourFamily.kAct_literalCfg
#print axioms CKM.NativeFourFamily.kAct_actC
#print axioms CKM.NativeFourFamily.kConj_mem_autC
#print axioms CKM.NativeFourFamily.kConj_one
#print axioms CKM.NativeFourFamily.continuous_kConj
#print axioms CKM.NativeFourFamily.kAct_mem_normalC
#print axioms CKM.NativeFourFamily.kAct_mem_orbitC
#print axioms CKM.NativeFourFamily.kAct_mem_tangentSpace
#print axioms CKM.NativeFourFamily.kAct_cube
#print axioms CKM.NativeFourFamily.kAct_comm
#print axioms CKM.NativeFourFamily.kAct_two
#print axioms CKM.NativeFourFamily.kAct_three
#print axioms CKM.NativeFourFamily.finrank_tanN
#print axioms CKM.NativeFourFamily.finrank_fixQ
#print axioms CKM.NativeFourFamily.finrank_fixQK
#print axioms CKM.NativeFourFamily.iSup_fixQ
#print axioms CKM.NativeFourFamily.fixQK_eq_iInf
#print axioms CKM.NativeFourFamily.fixQ_inf_fixQ

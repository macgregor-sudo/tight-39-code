module

public import ULCodeDict

@[expose] public section

/-!
# The code-space bridge: `Z / (G × Π) ≃ₜ` tight native codes modulo `G × S₃₉` 

The tight-code dictionary is supplied by `ULCodeDict`.

* `CodeModuli`: `tightLocus` modulo `G × S₃₉`, quotient topology.
* `unlabelledHomeo : UnlabelledSpace ≃ₜ CodeModuli`, induced by the inclusion `zeroSet ⊆ tightLocus`.
  Continuity of the inverse uses local constancy of the recovered partition (`partition_relative_nhds`
  / `zeroRel_eventually_eq`).
* `exists_code_slice_isOpenEmbedding`: the finite local slice quotient embeds openly in the actual
  unlabelled code quotient, with the literal code as basepoint.

No Gram-realization, injectivity, chosen-partition or continuity-of-choice assumption is made, and the
quotient is by the native group and relabellings only (not by arbitrary distance-preserving bijections
of finite codes).
-/

noncomputable section

namespace CKM.NativeUnlabelledSlice

open Glennie NativePolynomial CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeTightCode
open Option2.NativeStress.AnalyticDerivative (originalF)
open scoped Topology

/-! ## The code quotient -/

/-- Tight native codes modulo the native group and all point relabellings, quotient topology. -/
abbrev CodeModuli := Quotient codeSetoid

/-- The inclusion of the zero set into the code locus. -/
def zeroToCode (C : zeroSet) : tightLocus := ⟨C, zeroSet_subset_tightLocus C.2⟩

/-- The map induced by the inclusion. -/
def unlabelledToCode : UnlabelledSpace → CodeModuli :=
  Quotient.lift (fun C : zeroSet => (Quotient.mk codeSetoid (zeroToCode C) : CodeModuli))
    (by
      rintro C C' ⟨γ, h⟩
      exact Quotient.sound ⟨(γ.1, (γ.2 : Equiv.Perm (Fin 39))), h⟩)

theorem unlabelledToCode_mk (C : zeroSet) :
    unlabelledToCode (Quotient.mk bigSetoid C) = Quotient.mk codeSetoid (zeroToCode C) := rfl

/-- The literal label equivalence `p ↦ (p / 3, p % 3)`, inverse `framePointIndex`. -/
private def ulc_lab : Fin 39 ≃ Fin 13 × Fin 3 where
  toFun i := (⟨i.val / 3, by have := i.isLt; omega⟩, ⟨i.val % 3, by omega⟩)
  invFun x := ConfigurationResiduals.framePointIndex x.1 x.2
  left_inv i := by
    apply Fin.ext
    show 3 * (i.val / 3) + i.val % 3 = i.val
    omega
  right_inv x := by
    obtain ⟨f, a⟩ := x
    have ha := a.isLt
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
    · show (3 * f.val + a.val) / 3 = f.val
      omega
    · show (3 * f.val + a.val) % 3 = a.val
      omega

private theorem ulc_lab_fst (i : Fin 39) : ((ulc_lab i).1 : ℕ) = i.val / 3 := rfl

/-- Relabelling transports the zero relation. -/
private theorem ulc_zeroRel_permAct (σ : Equiv.Perm (Fin 39)) (C : Cfg) (i j : Fin 39) :
    zeroRel (permAct σ C) i j ↔ zeroRel C (σ.symm i) (σ.symm j) := by
  unfold zeroRel
  rw [Equiv.apply_eq_iff_eq]
  rfl

/-- Relabelling preserves the tight locus. -/
private theorem ulc_permAct_mem_tightLocus (σ : Equiv.Perm (Fin 39)) {C : Cfg}
    (hC : C ∈ tightLocus) : permAct σ C ∈ tightLocus :=
  ⟨fun i => hC.1 (σ.symm i), fun _ _ hij => hC.2 _ _ (σ.symm.injective.ne hij)⟩

/-- A tight code whose zero relation is the literal block relation lies in the zero set. -/
private theorem ulc_mem_zeroSet_of_zeroRel {C : Cfg} (hC : C ∈ tightLocus)
    (h : ∀ i j : Fin 39, zeroRel C i j ↔ i.val / 3 = j.val / 3) : C ∈ zeroSet := by
  rw [mem_zeroSet_iff_frames]
  refine ⟨fun f => frame_of_zero_overlaps _ (fun a => hC.1 _) fun a b hab => ?_, fun i j hij => ?_⟩
  · have ha := a.isLt
    have hb := b.isLt
    have hne : ConfigurationResiduals.framePointIndex f a ≠
        ConfigurationResiduals.framePointIndex f b := by
      intro heq
      apply hab
      have hv := congrArg Fin.val heq
      rw [ConfigurationResiduals.framePointIndex_val,
        ConfigurationResiduals.framePointIndex_val] at hv
      exact Fin.ext (by omega)
    have hz := (h (ConfigurationResiduals.framePointIndex f a)
      (ConfigurationResiduals.framePointIndex f b)).2 (by
        rw [ConfigurationResiduals.framePointIndex_val, ConfigurationResiduals.framePointIndex_val]
        omega)
    exact hz.resolve_left hne
  · have hne : i ≠ j := fun heq => hij (by rw [heq])
    rcases tight_overlap_values (codePoint C) hC.1 hC.2 i j hne with h0 | h3
    · exact absurd ((h i j).1 (Or.inr h0)) hij
    · exact h3

/-- Every tight code can be relabelled into the zero set (TC frame decomposition). -/
private theorem ulc_exists_std {C : Cfg} (hC : C ∈ tightLocus) :
    ∃ σ : Equiv.Perm (Fin 39), permAct σ C ∈ zeroSet := by
  obtain ⟨e, -, -, hiff⟩ := tight_frame_decomposition (codePoint C) hC.1 hC.2
  refine ⟨e.trans ulc_lab.symm,
    ulc_mem_zeroSet_of_zeroRel (ulc_permAct_mem_tightLocus _ hC) fun i j => ?_⟩
  rw [ulc_zeroRel_permAct]
  have key : ∀ k, e ((e.trans ulc_lab.symm).symm k) = ulc_lab k := fun k => by simp
  have hblock : ∀ p q, zeroRel C p q ↔ (e p).1 = (e q).1 := fun p q => by
    by_cases hpq : p = q
    · subst hpq
      exact ⟨fun _ => rfl, fun _ => Or.inl rfl⟩
    · unfold zeroRel
      simp only [hpq, false_or]
      exact hiff p q hpq
  rw [hblock, key, key, Fin.ext_iff, ulc_lab_fst, ulc_lab_fst]

/-- A relabelling between two zero-set configurations is frame preserving. -/
private theorem ulc_mem_framePerm {C : Cfg} (hC : C ∈ zeroSet) {σ : Equiv.Perm (Fin 39)}
    (hσ : permAct σ C ∈ zeroSet) : σ ∈ framePerm := by
  refine (mem_framePerm_iff' σ).2 fun p q => ?_
  have h1 := zeroRel_iff_of_mem_zeroSet hσ (σ p) (σ q)
  rw [ulc_zeroRel_permAct, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    zeroRel_iff_of_mem_zeroSet hC] at h1
  exact h1.symm

/-- The standardized relabelling of a code maps back to its code class. -/
private theorem ulc_toCode_std (C : tightLocus) {σ : Equiv.Perm (Fin 39)}
    (hσ : permAct σ (C : Cfg) ∈ zeroSet) :
    unlabelledToCode (Quotient.mk bigSetoid ⟨permAct σ (C : Cfg), hσ⟩) =
      Quotient.mk codeSetoid C := by
  rw [unlabelledToCode_mk]
  refine Quotient.sound ⟨(1, σ⁻¹), ?_⟩
  show actC (autVal 1) (permAct σ⁻¹ (permAct σ (C : Cfg))) = (C : Cfg)
  rw [autVal_one, actC_one, ContinuousLinearMap.id_apply, ← permAct_mul, inv_mul_cancel,
    permAct_one]

/-- Nearby codes with the same zero relation are standardized by the same relabelling. -/
private theorem ulc_std_of_zeroRel {C C' : Cfg} {σ : Equiv.Perm (Fin 39)}
    (hσ : permAct σ C ∈ zeroSet) (hC' : C' ∈ tightLocus) (h : zeroRel C' = zeroRel C) :
    permAct σ C' ∈ zeroSet := by
  refine ulc_mem_zeroSet_of_zeroRel (ulc_permAct_mem_tightLocus σ hC') fun i j => ?_
  rw [ulc_zeroRel_permAct, h, ← ulc_zeroRel_permAct]
  exact zeroRel_iff_of_mem_zeroSet hσ i j

theorem unlabelledToCode_bijective : Function.Bijective unlabelledToCode := by
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · induction x using Quotient.inductionOn with
    | h C =>
    induction y using Quotient.inductionOn with
    | h C' =>
    rw [unlabelledToCode_mk, unlabelledToCode_mk] at hxy
    obtain ⟨⟨g, σ⟩, h⟩ := Quotient.exact hxy
    have hz : actC (autVal g) (permAct σ (C : Cfg)) ∈ zeroSet := by
      rw [show actC (autVal g) (permAct σ (C : Cfg)) = (C' : Cfg) from h]
      exact C'.2
    have hσ : permAct σ (C : Cfg) ∈ zeroSet := (actC_mem_zeroSet_iff (autVal_mem g) _).1 hz
    exact Quotient.sound ⟨(g, ⟨σ, ulc_mem_framePerm C.2 hσ⟩), h⟩
  · induction y using Quotient.inductionOn with
    | h C =>
    obtain ⟨σ, hσ⟩ := ulc_exists_std C.2
    exact ⟨Quotient.mk bigSetoid ⟨permAct σ (C : Cfg), hσ⟩, ulc_toCode_std C hσ⟩

private theorem ulc_continuous_zeroToCode : Continuous zeroToCode :=
  Continuous.subtype_mk continuous_subtype_val _

theorem continuous_unlabelledToCode : Continuous unlabelledToCode := by
  exact Continuous.quotient_lift (continuous_quotient_mk'.comp ulc_continuous_zeroToCode) _

/-- Inverse continuity, from local constancy of the recovered partition. -/
theorem isOpenMap_unlabelledToCode : IsOpenMap unlabelledToCode := by
  intro U hU
  have hA : IsOpen (Quotient.mk bigSetoid ⁻¹' U) :=
    hU.preimage continuous_quotient_mk'
  obtain ⟨O, hO, hOA⟩ := isOpen_induced_iff.1 hA
  refine isQuotientMap_quotient_mk'.isOpen_preimage.1 ?_
  refine isOpen_iff_forall_mem_open.2 fun C hC => ?_
  obtain ⟨u, hu, hcu⟩ := hC
  obtain ⟨σ, hσ⟩ := ulc_exists_std C.2
  have hZ : Quotient.mk bigSetoid (⟨permAct σ (C : Cfg), hσ⟩ : zeroSet) ∈ U := by
    have he : Quotient.mk bigSetoid (⟨permAct σ (C : Cfg), hσ⟩ : zeroSet) = u :=
      unlabelledToCode_bijective.1 ((ulc_toCode_std C hσ).trans hcu.symm)
    rw [he]
    exact hu
  have hσO : permAct σ (C : Cfg) ∈ O :=
    (Set.ext_iff.1 hOA (⟨permAct σ (C : Cfg), hσ⟩ : zeroSet)).2 hZ
  refine ⟨{C' : tightLocus | zeroRel C'.1 = zeroRel C.1} ∩
      {C' : tightLocus | permAct σ (C'.1 : Cfg) ∈ O}, ?_, ?_, ⟨rfl, hσO⟩⟩
  · rintro C' ⟨h1, h2⟩
    have hz' : permAct σ (C'.1 : Cfg) ∈ zeroSet := ulc_std_of_zeroRel hσ C'.2 h1
    refine ⟨Quotient.mk bigSetoid ⟨permAct σ (C'.1 : Cfg), hz'⟩, ?_, ulc_toCode_std C' hz'⟩
    exact (Set.ext_iff.1 hOA (⟨permAct σ (C'.1 : Cfg), hz'⟩ : zeroSet)).1 h2
  · exact (isLocallyConstant_zeroRel.isOpen_fiber _).inter
      (hO.preimage ((permLin σ).continuous.comp continuous_subtype_val))

/-- **`Z / (G × Π) ≃ₜ` tight native codes modulo `G × S₃₉`.** -/
def unlabelledHomeo : UnlabelledSpace ≃ₜ CodeModuli :=
  (Equiv.ofBijective _ unlabelledToCode_bijective).toHomeomorphOfContinuousOpen
    continuous_unlabelledToCode isOpenMap_unlabelledToCode

theorem unlabelledHomeo_mk (C : zeroSet) :
    unlabelledHomeo (Quotient.mk bigSetoid C) = Quotient.mk codeSetoid (zeroToCode C) := rfl

/-! ## The transferred slice endpoint -/

/-- **Finite local slice quotient inside the unlabelled tight-code quotient.** -/
theorem exists_code_slice_isOpenEmbedding (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    ∃ W : Set Cfg, IsOpen W ∧ literalCfg ξ ∈ W ∧
      (∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W) ∧
      Topology.IsOpenEmbedding (unlabelledHomeo ∘ sliceQuotMap ξ W) ∧
      ∃ x : SliceQuot ξ W, unlabelledHomeo (sliceQuotMap ξ W x) =
        Quotient.mk codeSetoid ⟨literalCfg ξ, literalCfg_mem_tightLocus ξ hξ⟩ := by
  obtain ⟨W, hW, hPW, hinv, -, hemb, x, hx⟩ := exists_sliceQuot_isOpenEmbedding ξ hξ
  refine ⟨W, hW, hPW, hinv, unlabelledHomeo.isOpenEmbedding.comp hemb, x, ?_⟩
  show unlabelledHomeo (sliceQuotMap ξ W x) = _
  rw [hx]
  exact unlabelledHomeo_mk (basePt ξ hξ)

end CKM.NativeUnlabelledSlice

#print axioms CKM.NativeUnlabelledSlice.unlabelledToCode_bijective
#print axioms CKM.NativeUnlabelledSlice.continuous_unlabelledToCode
#print axioms CKM.NativeUnlabelledSlice.isOpenMap_unlabelledToCode
#print axioms CKM.NativeUnlabelledSlice.unlabelledHomeo
#print axioms CKM.NativeUnlabelledSlice.exists_code_slice_isOpenEmbedding

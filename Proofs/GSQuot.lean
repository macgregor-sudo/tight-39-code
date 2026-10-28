module

public import GSLocal

@[expose] public section

/-!
# The labelled orbit-space germ of the original zero set and the slice zero-set germ

* `zeroSet = {C : Cfg | originalF C = 0}`, with the subspace topology of `Cfg` (it may be
  singular; no manifold structure or dimension is used).
* `orbitSetoid`: `C ~ C'` iff `A • C = C'` for some `A ∈ G` (all of the compact group); an
  equivalence relation because `G` is a group and `G` preserves `zeroSet` (`originalF_actC`).
* `OrbitSpace = Quotient orbitSetoid` with the **quotient topology** (coinduced by the quotient map
  from the subspace topology on `zeroSet`).
* `sliceGerm ξ W = {C ∈ zeroSet | C ∈ W, C ∈ P + N(ξ)}` with the subspace topology, and
  `sliceToOrbit ξ W : sliceGerm ξ W → OrbitSpace` the restriction of the quotient map.
* `exists_sliceToOrbit_isOpenEmbedding`: for some open neighbourhood `W` of `P`, `sliceToOrbit ξ W`
  is an open embedding: a homeomorphism of the slice zero-set germ onto an open neighbourhood of
  the class of `P` in the labelled orbit space.
-/

noncomputable section

namespace CKM.NativeGroupSlice

open Glennie NativePolynomial CKM.NativeFirstOrder
open Option2.NativeStress.AnalyticDerivative (originalF)
open scoped Topology

/-- The real zero set of all 2184 original residual rows. -/
def zeroSet : Set Cfg := {C | originalF C = 0}

theorem actC_mem_zeroSet {A : CEnd} (hA : A ∈ autC) {C : Cfg} (hC : C ∈ zeroSet) :
    actC A C ∈ zeroSet :=
  (originalF_actC_eq_zero_iff hA C).2 hC

/-- Composition of two actions. -/
private theorem quot_actC_actC (A B : CEnd) (C : Cfg) : actC A (actC B C) = actC (A * B) C := by
  rw [actC_mul]; rfl

private theorem quot_actC_inv_cancel {A : CEnd} (hA : A ∈ autC) (C : Cfg) :
    actC (Ring.inverse A) (actC A C) = C := by
  rw [quot_actC_actC, (mul_inverse_of_mem_autOf hA).2, actC_one]; rfl

private theorem quot_actC_cancel_inv {A : CEnd} (hA : A ∈ autC) (C : Cfg) :
    actC A (actC (Ring.inverse A) C) = C := by
  rw [quot_actC_actC, (mul_inverse_of_mem_autOf hA).1, actC_one]; rfl

/-- The labelled orbit relation of the full group on the zero set. -/
def orbitSetoid : Setoid zeroSet where
  r C C' := ∃ A ∈ autC, actC A C = C'
  iseqv := by
    refine ⟨fun C => ⟨1, one_mem_autOf prodC, by rw [actC_one]; rfl⟩, ?_, ?_⟩
    · rintro C C' ⟨A, hA, h⟩
      exact ⟨Ring.inverse A, inverse_mem_autOf hA, by rw [← h]; exact quot_actC_inv_cancel hA C⟩
    · rintro C C' C'' ⟨A, hA, h⟩ ⟨B, hB, h'⟩
      exact ⟨B * A, mul_mem_autOf hB hA, by rw [← quot_actC_actC, h, h']⟩

/-- The labelled orbit space of the original zero set, with the quotient topology. -/
abbrev OrbitSpace := Quotient orbitSetoid

theorem literalCfg_mem_zeroSet (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : literalCfg ξ ∈ zeroSet :=
  originalF_literalCfg ξ hξ

/-- The slice zero-set germ inside a neighbourhood `W`. -/
def sliceGerm (ξ : Fin 4 → ℂ) (W : Set Cfg) : Set zeroSet :=
  {C | (C : Cfg) ∈ W ∧ (C : Cfg) ∈ sliceSet ξ}

/-- The restriction of the quotient map to the slice zero-set germ. -/
def sliceToOrbit (ξ : Fin 4 → ℂ) (W : Set Cfg) : sliceGerm ξ W → OrbitSpace :=
  fun C => Quotient.mk orbitSetoid C.1

/-- **Local slice homeomorphism.** -/
theorem exists_sliceToOrbit_isOpenEmbedding (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    ∃ W : Set Cfg, IsOpen W ∧ literalCfg ξ ∈ W ∧ Topology.IsOpenEmbedding (sliceToOrbit ξ W) := by
  set P := literalCfg ξ with hP
  set φ := slicePH ξ hξ with hφ
  obtain ⟨W₁, hW₁, hinj⟩ := exists_local_orbit_injective ξ hξ
  obtain ⟨W₁', hW₁'sub, hW₁'open, hPW₁'⟩ := mem_nhds_iff.1 hW₁
  -- normal vectors `n` with `(0, n)` in the chart source form an open set; realise it in `Cfg`
  have hN0 : IsOpen {n : normalC ξ | ((0 : derC), n) ∈ φ.source} :=
    φ.open_source.preimage (continuous_const.prodMk continuous_id)
  obtain ⟨O, hOopen, hO⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.1 hN0
  have h0O : (0 : Cfg) ∈ O := (Set.ext_iff.1 hO 0).2 (zero_mem_slicePH_source ξ hξ)
  let W : Set Cfg := W₁' ∩ (fun C => C - P) ⁻¹' O
  have hWopen : IsOpen W := hW₁'open.inter (hOopen.preimage (continuous_id.sub continuous_const))
  have hPW : P ∈ W := ⟨hPW₁', by simp [h0O]⟩
  have hsrc : ∀ s ∈ W, ∀ hs : s ∈ sliceSet ξ,
      ((0 : derC), (⟨s - P, hs⟩ : normalC ξ)) ∈ φ.source := by
    intro s hsW hs
    exact (Set.ext_iff.1 hO _).1 hsW.2
  have himg : ∀ s (hs : s ∈ sliceSet ξ), φ ((0 : derC), (⟨s - P, hs⟩ : normalC ξ)) = s := by
    intro s hs
    rw [hφ, slicePH_coe, sliceChart_zero_left]
    exact add_sub_cancel P s
  have hsymm : ∀ s ∈ W, ∀ hs : s ∈ sliceSet ξ, φ.symm s = ((0 : derC), (⟨s - P, hs⟩ : normalC ξ)) := by
    intro s hsW hs
    have h1 := φ.left_inv (hsrc s hsW hs)
    rwa [himg s hs] at h1
  have htgt : ∀ s ∈ W, s ∈ sliceSet ξ → s ∈ φ.target := by
    intro s hsW hs
    have h1 := φ.map_source (hsrc s hsW hs)
    rwa [himg s hs] at h1
  refine ⟨W, hWopen, hPW, ?_⟩
  have hcont : Continuous (sliceToOrbit ξ W) :=
    continuous_quot_mk.comp continuous_subtype_val
  have hinj' : Function.Injective (sliceToOrbit ξ W) := by
    rintro ⟨s, hsW, hss⟩ ⟨t, htW, hts⟩ h
    obtain ⟨A, hA, hst⟩ := Quotient.exact h
    exact Subtype.ext (Subtype.ext (hinj s ⟨hW₁'sub hsW.1, hss⟩ t ⟨hW₁'sub htW.1, hts⟩ A hA hst))
  have hopen : IsOpenMap (sliceToOrbit ξ W) := by
    intro V hV
    obtain ⟨O', hO'open, hO'⟩ :=
      (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal).isOpen_iff.1 hV
    apply isQuotientMap_quotient_mk'.isOpen_preimage.1
    rw [isOpen_iff_mem_nhds]
    rintro C ⟨x, hxV, hxC⟩
    obtain ⟨A, hA, hAx⟩ := Quotient.exact hxC
    have hB : Ring.inverse A ∈ autC := inverse_mem_autOf hA
    have hvW : ((x : zeroSet) : Cfg) ∈ W := x.2.1
    have hvS : ((x : zeroSet) : Cfg) ∈ sliceSet ξ := x.2.2
    have hvO' : ((x : zeroSet) : Cfg) ∈ O' := by
      rw [← hO'] at hxV; exact hxV
    have hBC : actC (Ring.inverse A) C = ((x : zeroSet) : Cfg) := by
      rw [← hAx]; exact quot_actC_inv_cancel hA _
    let F : Cfg → Cfg := fun y => P + ((φ.symm (actC (Ring.inverse A) y)).2 : Cfg)
    have hvT := htgt _ hvW hvS
    have hFC : F C = ((x : zeroSet) : Cfg) := by
      simp only [F, hBC, hsymm _ hvW hvS]
      exact add_sub_cancel P _
    have hFcont : ContinuousAt F C := by
      refine continuousAt_const.add
        (continuous_subtype_val.continuousAt.comp (continuous_snd.continuousAt.comp ?_))
      refine ContinuousAt.comp (f := actC (Ring.inverse A)) ?_
        (actC (Ring.inverse A)).continuous.continuousAt
      rw [hBC]; exact φ.continuousAt_symm hvT
    have hU : F ⁻¹' (O' ∩ W) ∩ (actC (Ring.inverse A)) ⁻¹' φ.target ∈ 𝓝 (C : Cfg) := by
      refine Filter.inter_mem (hFcont.preimage_mem_nhds ?_)
        ((actC (Ring.inverse A)).continuous.continuousAt.preimage_mem_nhds ?_)
      · rw [hFC]; exact (hO'open.inter hWopen).mem_nhds ⟨hvO', hvW⟩
      · rw [hBC]; exact φ.open_target.mem_nhds hvT
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds hU] with C' hC'
    obtain ⟨⟨hFO', hFW⟩, hT⟩ := hC'
    have hy : actC (groupChart (φ.symm (actC (Ring.inverse A) C')).1)
        (P + ((φ.symm (actC (Ring.inverse A) C')).2 : Cfg)) = actC (Ring.inverse A) C' :=
      φ.right_inv hT
    have hs'S : P + ((φ.symm (actC (Ring.inverse A) C')).2 : Cfg) ∈ sliceSet ξ := by
      show _ - P ∈ normalC ξ
      rw [add_sub_cancel_left]; exact Subtype.mem _
    have hs'Z : P + ((φ.symm (actC (Ring.inverse A) C')).2 : Cfg) ∈ zeroSet := by
      have h1 : actC (groupChart (φ.symm (actC (Ring.inverse A) C')).1)
          (P + ((φ.symm (actC (Ring.inverse A) C')).2 : Cfg)) ∈ zeroSet := by
        rw [hy]; exact actC_mem_zeroSet hB C'.2
      exact (originalF_actC_eq_zero_iff (groupChart_mem_autC _) _).1 h1
    refine ⟨⟨⟨_, hs'Z⟩, hFW, hs'S⟩, ?_, ?_⟩
    · rw [← hO']; exact hFO'
    · apply Quotient.sound
      refine ⟨A * groupChart (φ.symm (actC (Ring.inverse A) C')).1,
        mul_mem_autOf hA (groupChart_mem_autC _), ?_⟩
      show actC (A * _) _ = (C' : Cfg)
      rw [← quot_actC_actC, hy]; exact quot_actC_cancel_inv hA _
  exact .of_continuous_injective_isOpenMap hcont hinj' hopen

#print axioms actC_mem_zeroSet
#print axioms literalCfg_mem_zeroSet
#print axioms exists_sliceToOrbit_isOpenEmbedding

end CKM.NativeGroupSlice

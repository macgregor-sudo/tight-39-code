module

public import ULStab

@[expose] public section

/-!
# The finite local quotient: `(Z ∩ (P + N) ∩ W) / Γξ → Z / (G × Π)` is an open embedding


* `bigSetoid`: on the original zero set `zeroSet` (subspace topology of `Cfg`), `C ~ C'` iff
  `γ • C = C'` for some `γ ∈ G × Π`. `UnlabelledSpace = Quotient bigSetoid`, quotient topology.
* `stabSetoid ξ W`: on the slice zero-set germ `sliceGerm ξ W = {C ∈ zeroSet | C ∈ W ∩ (P + N)}`
  (accepted GS definition, subspace topology), `s ~ t` iff `γ • s = t` for some `γ ∈ Γξ`.
  `SliceQuot ξ W = Quotient (stabSetoid ξ W)`, quotient topology.
* `sliceQuotMap ξ W : SliceQuot ξ W → UnlabelledSpace`, induced by the inclusion.
* `exists_sliceQuot_isOpenEmbedding`: there is an open `Γξ`-invariant neighbourhood `W` of `P` on
  which both directions of the local orbit relation hold (two slice zero points in `W` are
  `G × Π`-related iff they are `Γξ`-related), `sliceQuotMap ξ W` is an open embedding, and the class
  of `P` is the image of the class of `P`.

Route. Finitely many label permutations `π` with `π • P ∉ G • P` are excluded near `P` by
compactness of `G`; for the others pick `(g_π, π) ∈ Γξ` and reduce to the accepted full local
`G`-orbit relation `exists_local_orbit_injective`. Openness: the `G`-saturation of an open slice set
is open (accepted `exists_sliceToOrbit_isOpenEmbedding`) and `Π` acts by homeomorphisms.
-/

noncomputable section

namespace CKM.NativeUnlabelledSlice

open Glennie NativePolynomial CKM.NativeFirstOrder CKM.NativeGroupSlice
open Option2.NativeStress.AnalyticDerivative (originalF)
open scoped Topology

/-- The action of `G × Π` restricted to the original zero set. -/
def zeroAct (γ : Big) (C : zeroSet) : zeroSet :=
  ⟨γ • (C : Cfg), (big_smul_mem_zeroSet_iff γ C).2 C.2⟩

theorem zeroAct_coe (γ : Big) (C : zeroSet) : (zeroAct γ C : Cfg) = γ • (C : Cfg) := rfl

/-- The unlabelled orbit relation of `G × Π` on the original zero set. -/
def bigSetoid : Setoid zeroSet where
  r C C' := ∃ γ : Big, γ • (C : Cfg) = C'
  iseqv := by
    refine ⟨fun C => ⟨1, one_smul _ _⟩, ?_, ?_⟩
    · rintro C C' ⟨γ, h⟩
      exact ⟨γ⁻¹, by rw [← h, inv_smul_smul]⟩
    · rintro C C' C'' ⟨γ, h⟩ ⟨δ, h'⟩
      exact ⟨δ * γ, by rw [mul_smul, h, h']⟩

/-- The unlabelled orbit space `Z / (G × Π)`, with the quotient topology. -/
abbrev UnlabelledSpace := Quotient bigSetoid

/-- The literal configuration as a point of the zero set. -/
def basePt (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : zeroSet := ⟨literalCfg ξ, literalCfg_mem_zeroSet ξ hξ⟩

/-- The `Γξ`-relation on the slice zero-set germ. -/
def stabSetoid (ξ : Fin 4 → ℂ) (W : Set Cfg) : Setoid (sliceGerm ξ W) where
  r s t := ∃ γ ∈ stab ξ, γ • ((s : zeroSet) : Cfg) = ((t : zeroSet) : Cfg)
  iseqv := by
    refine ⟨fun s => ⟨1, (stab ξ).one_mem, one_smul _ _⟩, ?_, ?_⟩
    · rintro s t ⟨γ, hγ, h⟩
      exact ⟨γ⁻¹, (stab ξ).inv_mem hγ, by rw [← h, inv_smul_smul]⟩
    · rintro s t u ⟨γ, hγ, h⟩ ⟨δ, hδ, h'⟩
      exact ⟨δ * γ, (stab ξ).mul_mem hδ hγ, by rw [mul_smul, h, h']⟩

/-- The finite local quotient `(Z ∩ (P + N) ∩ W) / Γξ`, with the quotient topology. -/
abbrev SliceQuot (ξ : Fin 4 → ℂ) (W : Set Cfg) := Quotient (stabSetoid ξ W)

/-- The natural map to the unlabelled orbit space. -/
def sliceQuotMap (ξ : Fin 4 → ℂ) (W : Set Cfg) : SliceQuot ξ W → UnlabelledSpace :=
  Quotient.lift (fun s : sliceGerm ξ W => (Quotient.mk bigSetoid (s : zeroSet) : UnlabelledSpace))
    (by
      rintro s t ⟨γ, -, h⟩
      exact Quotient.sound ⟨γ, h⟩)

theorem sliceQuotMap_mk (ξ : Fin 4 → ℂ) (W : Set Cfg) (s : sliceGerm ξ W) :
    sliceQuotMap ξ W (Quotient.mk _ s) = Quotient.mk bigSetoid (s : zeroSet) := rfl

/-- Each `zeroAct γ` is continuous. -/
private theorem ulq_continuous_zeroAct (γ : Big) : Continuous (zeroAct γ) :=
  ((continuous_const_smul γ).comp continuous_subtype_val).subtype_mk _

/-- Properness step for bad labels: near `(P, P)`, for every label `e` admitting no compensating
`g` with `(g, e) ∈ Γξ`, no `(g, e)` moves the first point to the second. Uses compactness of `G`
and finiteness of `Π`. -/
private theorem ulq_bad_eventually (ξ : Fin 4 → ℂ) :
    ∀ᶠ x : Cfg × Cfg in 𝓝 (literalCfg ξ, literalCfg ξ), ∀ e : framePerm,
      (∀ g : autGroup, (g, e) ∉ stab ξ) → ∀ g : autGroup, (g, e) • x.1 ≠ x.2 := by
  refine Filter.eventually_all.2 fun e => ?_
  by_cases he : ∀ g : autGroup, (g, e) ∉ stab ξ
  · have h := (isCompact_univ (X := autGroup)).eventually_forall_of_forall_eventually
      (x₀ := (literalCfg ξ, literalCfg ξ))
      (P := fun (x : Cfg × Cfg) (g : autGroup) => (g, e) • x.1 ≠ x.2) ?_
    · filter_upwards [h] with x hx _ g using hx g (Set.mem_univ g)
    · intro g _
      have hne : (g, e) • literalCfg ξ ≠ literalCfg ξ := fun h' => he g ((mem_stab_iff ξ _).2 h')
      have hcont : Continuous fun z : (Cfg × Cfg) × autGroup => ((z.2, e) • z.1.1, z.1.2) :=
        (Continuous.smul (f := fun z : (Cfg × Cfg) × autGroup => ((z.2, e) : Big))
          (g := fun z : (Cfg × Cfg) × autGroup => z.1.1)
          (continuous_snd.prodMk continuous_const) (continuous_fst.comp continuous_fst)).prodMk
          (continuous_snd.comp continuous_fst)
      exact (hcont.continuousAt (x := ((literalCfg ξ, literalCfg ξ), g))).preimage_mem_nhds
        ((isOpen_ne_fun continuous_fst continuous_snd).mem_nhds hne)
  · exact Filter.Eventually.of_forall fun _ h => absurd h he

/-- A `Γξ`-invariant open neighbourhood of `P` inside a given open neighbourhood: the finite
intersection `⋂_{γ ∈ Γξ} γ⁻¹ • W₀`. -/
private theorem ulq_invariant_open (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {W₀ : Set Cfg}
    (h0 : IsOpen W₀) (hP : literalCfg ξ ∈ W₀) :
    ∃ W : Set Cfg, IsOpen W ∧ literalCfg ξ ∈ W ∧ W ⊆ W₀ ∧
      ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W := by
  have := finite_stab ξ hξ
  refine ⟨⋂ γ : stab ξ, (fun C : Cfg => (γ : Big) • C) ⁻¹' W₀,
    isOpen_iInter_of_finite fun γ => h0.preimage (continuous_const_smul _), ?_, ?_, ?_⟩
  · simp only [Set.mem_iInter, Set.mem_preimage]
    intro γ
    rw [(mem_stab_iff ξ _).1 γ.2]
    exact hP
  · intro C hC
    have h1 := Set.mem_iInter.1 hC 1
    simpa using h1
  · intro δ hδ C
    simp only [Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h γ
      have h1 := h ⟨(γ : Big) * δ⁻¹, (stab ξ).mul_mem γ.2 ((stab ξ).inv_mem hδ)⟩
      rwa [mul_smul, inv_smul_smul] at h1
    · intro h γ
      rw [← mul_smul]
      exact h ⟨(γ : Big) * δ, (stab ξ).mul_mem γ.2 hδ⟩

/-- The local orbit relation: bad labels are excluded, good labels reduce to the accepted full
local `G`-orbit relation. -/
private theorem ulq_relation (ξ : Fin 4 → ℂ) {W WL a b : Set Cfg}
    (hWL : ∀ s ∈ WL ∩ sliceSet ξ, ∀ t ∈ WL ∩ sliceSet ξ, ∀ A ∈ autC, actC A s = t → s = t)
    (hab : a ×ˢ b ⊆ {x : Cfg × Cfg | ∀ e : framePerm,
      (∀ g : autGroup, (g, e) ∉ stab ξ) → ∀ g : autGroup, (g, e) • x.1 ≠ x.2})
    (hWa : W ⊆ a) (hWb : W ⊆ b) (hWWL : W ⊆ WL)
    (hinv : ∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W)
    {s t : Cfg} (hsW : s ∈ W) (hsS : s ∈ sliceSet ξ) (htW : t ∈ W) (htS : t ∈ sliceSet ξ)
    (γ : Big) (hγ : γ • s = t) : ∃ δ ∈ stab ξ, δ • s = t := by
  obtain ⟨g, e⟩ := γ
  by_cases he : ∀ g' : autGroup, (g', e) ∉ stab ξ
  · exact absurd hγ (hab (Set.mk_mem_prod (hWa hsW) (hWb htW)) e he g)
  · push Not at he
    obtain ⟨g', hg'⟩ := he
    have hs'W : (g', e) • s ∈ W := (hinv _ hg' s).2 hsW
    have hs'S : (g', e) • s ∈ sliceSet ξ := (smul_mem_sliceSet_iff hg' s).2 hsS
    have hdecomp : ((g * g'⁻¹, (1 : framePerm)) : Big) * (g', e) = (g, e) :=
      Prod.ext (by simp) (by simp)
    have ht' : ((g * g'⁻¹, (1 : framePerm)) : Big) • ((g', e) • s) = t := by
      rw [← hγ, ← hdecomp, mul_smul]
    have ht'' : actC (autVal (g * g'⁻¹)) ((g', e) • s) = t := ht'
    exact ⟨(g', e), hg', hWL _ ⟨hWWL hs'W, hs'S⟩ t ⟨hWWL htW, htS⟩ _ (autVal_mem _) ht''⟩

/-- Openness of saturations: the `G × Π`-saturation in the zero set of an open subset of the slice
zero-set germ in `W` is open, when `W ⊆ WG` is open and `sliceToOrbit ξ WG` is an open embedding. -/
private theorem ulq_bigSat_open (ξ : Fin 4 → ℂ) {W WG : Set Cfg} (hW : IsOpen W) (hsub : W ⊆ WG)
    (hemb : Topology.IsOpenEmbedding (sliceToOrbit ξ WG)) {V : Set (sliceGerm ξ W)}
    (hV : IsOpen V) :
    IsOpen {C : zeroSet | ∃ s ∈ V, ∃ γ : Big, γ • ((s : zeroSet) : Cfg) = (C : Cfg)} := by
  obtain ⟨O, hO, rfl⟩ :=
    (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal).isOpen_iff.1 hV
  let V' : Set (sliceGerm ξ WG) := {y | ((y : zeroSet) : Cfg) ∈ O ∩ W}
  have hV' : IsOpen V' :=
    (hO.inter hW).preimage (continuous_subtype_val.comp continuous_subtype_val)
  let T : Set zeroSet := Quotient.mk orbitSetoid ⁻¹' (sliceToOrbit ξ WG '' V')
  have hT : IsOpen T := (hemb.isOpenMap V' hV').preimage continuous_quot_mk
  have hset : {C : zeroSet | ∃ s ∈ ((Subtype.val ∘ Subtype.val) ⁻¹' O : Set (sliceGerm ξ W)),
      ∃ γ : Big,
      γ • ((s : zeroSet) : Cfg) = (C : Cfg)} = ⋃ γ : Big, zeroAct γ ⁻¹' T := by
    ext C
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨s, hs, γ, hγ⟩
      refine ⟨γ⁻¹, (⟨(s : zeroSet), hsub s.2.1, s.2.2⟩ : sliceGerm ξ WG), ⟨hs, s.2.1⟩, ?_⟩
      show Quotient.mk orbitSetoid (s : zeroSet) = Quotient.mk orbitSetoid (zeroAct γ⁻¹ C)
      congr 1
      apply Subtype.ext
      show _ = γ⁻¹ • (C : Cfg)
      rw [← hγ, inv_smul_smul]
    · rintro ⟨γ, y, ⟨hyO, hyW⟩, hy⟩
      obtain ⟨A, hA, hAy⟩ := Quotient.exact hy
      rw [← range_autVal] at hA
      obtain ⟨A', rfl⟩ := hA
      refine ⟨⟨(y : zeroSet), hyW, y.2.2⟩, hyO, γ⁻¹ * (A', 1), ?_⟩
      have h1 : ((A', (1 : framePerm)) : Big) • ((y : zeroSet) : Cfg) = γ • (C : Cfg) := hAy
      rw [mul_smul, h1, inv_smul_smul]
  rw [hset]
  exact isOpen_iUnion fun γ => hT.preimage (ulq_continuous_zeroAct γ)

/-- **Finite local quotient theorem.** -/
theorem exists_sliceQuot_isOpenEmbedding (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    ∃ W : Set Cfg, IsOpen W ∧ literalCfg ξ ∈ W ∧
      (∀ γ ∈ stab ξ, ∀ C : Cfg, γ • C ∈ W ↔ C ∈ W) ∧
      (∀ s t : sliceGerm ξ W,
        (∃ γ : Big, γ • ((s : zeroSet) : Cfg) = ((t : zeroSet) : Cfg)) ↔
          ∃ γ ∈ stab ξ, γ • ((s : zeroSet) : Cfg) = ((t : zeroSet) : Cfg)) ∧
      Topology.IsOpenEmbedding (sliceQuotMap ξ W) ∧
      ∃ x : SliceQuot ξ W, sliceQuotMap ξ W x = Quotient.mk bigSetoid (basePt ξ hξ) := by
  set P := literalCfg ξ with hPdef
  obtain ⟨WG, hWGo, hPWG, hemb⟩ := exists_sliceToOrbit_isOpenEmbedding ξ hξ
  obtain ⟨WL, hWL, hinjL⟩ := exists_local_orbit_injective ξ hξ
  obtain ⟨a, ha, b, hb, hab⟩ := mem_nhds_prod_iff.1 (ulq_bad_eventually ξ)
  have hW0 : a ∩ b ∩ WL ∩ WG ∈ 𝓝 P :=
    Filter.inter_mem (Filter.inter_mem (Filter.inter_mem ha hb) hWL) (hWGo.mem_nhds hPWG)
  obtain ⟨W₀, hW₀sub, hW₀o, hPW₀⟩ := mem_nhds_iff.1 hW0
  obtain ⟨W, hWo, hPW, hWsub, hinv⟩ := ulq_invariant_open ξ hξ hW₀o hPW₀
  have hWa : W ⊆ a := fun x hx => (hW₀sub (hWsub hx)).1.1.1
  have hWb : W ⊆ b := fun x hx => (hW₀sub (hWsub hx)).1.1.2
  have hWWL : W ⊆ WL := fun x hx => (hW₀sub (hWsub hx)).1.2
  have hWWG : W ⊆ WG := fun x hx => (hW₀sub (hWsub hx)).2
  have hrel : ∀ s t : sliceGerm ξ W,
      (∃ γ : Big, γ • ((s : zeroSet) : Cfg) = ((t : zeroSet) : Cfg)) ↔
        ∃ γ ∈ stab ξ, γ • ((s : zeroSet) : Cfg) = ((t : zeroSet) : Cfg) := by
    intro s t
    constructor
    · rintro ⟨γ, hγ⟩
      exact ulq_relation ξ hinjL hab hWa hWb hWWL hinv s.2.1 s.2.2 t.2.1 t.2.2 γ hγ
    · rintro ⟨γ, -, hγ⟩
      exact ⟨γ, hγ⟩
  refine ⟨W, hWo, hPW, hinv, hrel, ?_,
    Quotient.mk _ ⟨basePt ξ hξ, hPW, literalCfg_mem_sliceSet ξ⟩, rfl⟩
  have hcont : Continuous (sliceQuotMap ξ W) :=
    Continuous.quotient_lift (continuous_quot_mk.comp
      (continuous_subtype_val (p := fun C => C ∈ sliceGerm ξ W))) _
  have hinj : Function.Injective (sliceQuotMap ξ W) := by
    intro x y hxy
    obtain ⟨s, rfl⟩ := Quotient.exists_rep x
    obtain ⟨t, rfl⟩ := Quotient.exists_rep y
    obtain ⟨γ, hγ⟩ := Quotient.exact hxy
    exact Quotient.sound ((hrel s t).1 ⟨γ, hγ⟩)
  have hopen : IsOpenMap (sliceQuotMap ξ W) := by
    intro U hU
    have hV : IsOpen (Quotient.mk (stabSetoid ξ W) ⁻¹' U) := hU.preimage continuous_quot_mk
    apply (isQuotientMap_quotient_mk' (s := bigSetoid)).isOpen_preimage.1
    have hset : (@Quotient.mk' _ bigSetoid) ⁻¹' (sliceQuotMap ξ W '' U) =
        {C : zeroSet | ∃ s ∈ Quotient.mk (stabSetoid ξ W) ⁻¹' U, ∃ γ : Big,
          γ • ((s : zeroSet) : Cfg) = (C : Cfg)} := by
      ext C
      constructor
      · rintro ⟨x, hxU, hx⟩
        obtain ⟨s, rfl⟩ := Quotient.exists_rep x
        obtain ⟨γ, hγ⟩ := Quotient.exact hx
        exact ⟨s, hxU, γ, hγ⟩
      · rintro ⟨s, hs, γ, hγ⟩
        exact ⟨Quotient.mk _ s, hs, Quotient.sound ⟨γ, hγ⟩⟩
    rw [hset]
    exact ulq_bigSat_open ξ hWo hWWG hemb hV
  exact .of_continuous_injective_isOpenMap hcont hinj hopen

end CKM.NativeUnlabelledSlice

#print axioms CKM.NativeUnlabelledSlice.bigSetoid
#print axioms CKM.NativeUnlabelledSlice.stabSetoid
#print axioms CKM.NativeUnlabelledSlice.sliceQuotMap
#print axioms CKM.NativeUnlabelledSlice.exists_sliceQuot_isOpenEmbedding

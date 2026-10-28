module

public import GSQuot
public import NativeFrameRelabelling
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.ConstMulAction

@[expose] public section

/-!
# The native group `G`, the frame/outcome relabelling group `Π = S₃ ≀ S₁₃`, and their actions


* `autGroup`: the actual native automorphism set `autC` (all bijective real-linear maps of the 27
  upper coordinates preserving the original product `prodC`, i.e. `Glennie.jordan`) as a subgroup of
  the units of `CEnd`. Its carrier is exactly `autC` (`mem_autGroup_iff`, `autGroupEquiv`); it is a
  topological group (subspace topology of the units) and compact (`isCompact_autC`).
* `framePerm`: the permutations of the 39 actual labels that map frames to frames, where frame `f`
  is the label block `{framePointIndex f a | a : Fin 3} = {p | p / 3 = f}`. Its elements are exactly
  the accepted `NativeFrameRelabelling.pointPerm σ τ` (`mem_framePerm_iff`): an arbitrary
  permutation `σ` of the thirteen frames together with an independent outcome permutation `τ f` in
  each frame. So `framePerm ≅ S₃ ≀ S₁₃`, acting through the literal `Fin 39` label equivalence.
* Actions on `Cfg = Fin 39 → Fin 27 → ℝ`, left actions:
  `g • C = actC g C` (pointwise, `(g • C) i = g (C i)`), and `e • C = C ∘ e⁻¹`
  (`(e • C) i = C (e.symm i)`; the accepted pullback is `relabel σ τ C = (pointPerm σ τ)⁻¹ • C`).
  The two actions commute (`permAct_actC`). On the product group `Big = autGroup × framePerm`,
  `(g, e) • C = g • (e • C)`; composition is componentwise, `((g, e) * (g', e')) • C =
  (g, e) • ((g', e') • C)`.
* Both actions preserve and reflect the original zero set `zeroSet = {C | originalF C = 0}`:
  `G` by the accepted `originalF_actC_eq_zero_iff`, `Π` by the accepted
  `NativeFrameRelabelling.all_original_F_iff` (no abstract replacement of the equations).
-/

noncomputable section

namespace CKM.NativeUnlabelledSlice

open Glennie NativePolynomial CKM.NativeFirstOrder CKM.NativeGroupSlice
open Option2.NativeStress.AnalyticDerivative (originalF)
open scoped Topology

/-! ## The native automorphism group -/

/-- The native automorphism group: units of `CEnd` whose underlying map lies in `autC`. -/
def autGroup : Subgroup CEndˣ where
  carrier := {u | (u : CEnd) ∈ autC}
  mul_mem' := fun ha hb => mul_mem_autOf ha hb
  one_mem' := one_mem_autOf prodC
  inv_mem' := by
    intro u hu
    show ((u⁻¹ : CEndˣ) : CEnd) ∈ autC
    rw [← Ring.inverse_unit u]
    exact inverse_mem_autOf hu

theorem mem_autGroup_iff (u : CEndˣ) : u ∈ autGroup ↔ (u : CEnd) ∈ autC := Iff.rfl

/-- The underlying endomorphism of a group element. -/
abbrev autVal (g : autGroup) : CEnd := ((g : CEndˣ) : CEnd)

theorem autVal_mem (g : autGroup) : autVal g ∈ autC := g.2

theorem autVal_mul (g h : autGroup) : autVal (g * h) = autVal g * autVal h := rfl

theorem autVal_one : autVal 1 = 1 := rfl

theorem autVal_inv (g : autGroup) : autVal g⁻¹ = Ring.inverse (autVal g) := by
  exact (Ring.inverse_unit (g : CEndˣ)).symm

theorem autVal_injective : Function.Injective autVal := by
  intro g h hgh
  exact Subtype.ext (Units.ext hgh)

/-- The group is exactly the set `autC`. -/
def autGroupEquiv : autGroup ≃ autC where
  toFun g := ⟨autVal g, autVal_mem g⟩
  invFun A := ⟨⟨A.1, Ring.inverse A.1, (mul_inverse_of_mem_autOf A.2).1,
    (mul_inverse_of_mem_autOf A.2).2⟩, A.2⟩
  left_inv _ := Subtype.ext (Units.ext rfl)
  right_inv _ := rfl

theorem autGroupEquiv_apply (g : autGroup) : (autGroupEquiv g : CEnd) = autVal g := rfl

/-- Inversion on the units of a topological monoid is continuous for the `embedProduct`
topology (`u ↦ (u, op u⁻¹)`): it swaps the two factors up to `op`. -/
private theorem ulg_continuousInv_units : ContinuousInv CEndˣ := by
  refine ⟨Units.isInducing_embedProduct.continuous_iff.2 ?_⟩
  have h1 : Continuous fun u : CEndˣ => ((u⁻¹ : CEndˣ) : CEnd) := Units.continuous_coe_inv
  have h2 : Continuous fun u : CEndˣ => MulOpposite.op ((u : CEnd)) :=
    MulOpposite.continuous_op.comp Units.continuous_val
  exact h1.prodMk h2

/-- `G` is a topological group (subspace topology of the units of `CEnd`). -/
instance : IsTopologicalGroup autGroup := by
  have : ContinuousInv CEndˣ := ulg_continuousInv_units
  have : IsTopologicalGroup CEndˣ := { }
  infer_instance

/-- The underlying map is a topological embedding with image `autC`. -/
theorem isEmbedding_autVal : Topology.IsEmbedding autVal := by
  exact Units.isOpenEmbedding_val.isEmbedding.comp Topology.IsEmbedding.subtypeVal

theorem range_autVal : Set.range autVal = autC := by
  ext A
  constructor
  · rintro ⟨g, rfl⟩
    exact autVal_mem g
  · intro hA
    exact ⟨autGroupEquiv.symm ⟨A, hA⟩, rfl⟩

instance : CompactSpace autGroup := by
  refine ⟨isEmbedding_autVal.isCompact_iff.2 ?_⟩
  rw [Set.image_univ, range_autVal]
  exact isCompact_autC

/-! ## The frame/outcome relabelling group -/

/-- Frame-preserving permutations of the 39 actual labels (frame of `p` is `p / 3`). -/
def framePerm : Subgroup (Equiv.Perm (Fin 39)) where
  carrier := {e | ∀ p q : Fin 39, (e p).val / 3 = (e q).val / 3 ↔ p.val / 3 = q.val / 3}
  mul_mem' := by
    intro a b ha hb p q
    exact (ha (b p) (b q)).trans (hb p q)
  one_mem' := fun p q => Iff.rfl
  inv_mem' := by
    intro a ha p q
    have h := ha (a⁻¹ p) (a⁻¹ q)
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h
    exact h.symm

theorem mem_framePerm_iff' (e : Equiv.Perm (Fin 39)) :
    e ∈ framePerm ↔ ∀ p q : Fin 39, (e p).val / 3 = (e q).val / 3 ↔ p.val / 3 = q.val / 3 :=
  Iff.rfl

/-- **`Π = S₃ ≀ S₁₃`:** the frame-preserving permutations are exactly the accepted relabellings
`pointPerm σ τ` (frame permutation `σ`, outcome permutation `τ f` inside each frame). -/
theorem mem_framePerm_iff (e : Equiv.Perm (Fin 39)) :
    e ∈ framePerm ↔ ∃ (σ : Equiv.Perm (Fin 13)) (τ : Fin 13 → Equiv.Perm (Fin 3)),
      e = NativeFrameRelabelling.pointPerm σ τ := by
  constructor
  · intro he
    have hv : ∀ (f : Fin 13) (a : Fin 3),
        (ConfigurationResiduals.framePointIndex f a).val = 3 * f.val + a.val := fun _ _ => rfl
    have hfr : ∀ (f : Fin 13) (a : Fin 3),
        (ConfigurationResiduals.framePointIndex f a).val / 3 = f.val := by
      intro f a; rw [hv]; have := a.isLt; omega
    -- frame map
    let σf : Fin 13 → Fin 13 := fun f =>
      ⟨(e (ConfigurationResiduals.framePointIndex f 0)).val / 3, by
        have := (e (ConfigurationResiduals.framePointIndex f 0)).isLt; omega⟩
    have hσinj : Function.Injective σf := by
      intro f g hfg
      have h1 : (e (ConfigurationResiduals.framePointIndex f 0)).val / 3 =
          (e (ConfigurationResiduals.framePointIndex g 0)).val / 3 := congrArg Fin.val hfg
      have h2 := (he _ _).1 h1
      rw [hfr, hfr] at h2
      exact Fin.ext h2
    let σ : Equiv.Perm (Fin 13) := Equiv.ofBijective σf (Finite.injective_iff_bijective.1 hσinj)
    let τf : Fin 13 → Fin 3 → Fin 3 := fun f a =>
      ⟨(e (ConfigurationResiduals.framePointIndex f a)).val % 3, Nat.mod_lt _ (by norm_num)⟩
    have hsame : ∀ (f : Fin 13) (a : Fin 3),
        (e (ConfigurationResiduals.framePointIndex f a)).val / 3 =
          (e (ConfigurationResiduals.framePointIndex f 0)).val / 3 := by
      intro f a
      exact (he _ _).2 (by rw [hfr, hfr])
    have hτinj : ∀ f, Function.Injective (τf f) := by
      intro f a b hab
      have h1 : (e (ConfigurationResiduals.framePointIndex f a)).val % 3 =
          (e (ConfigurationResiduals.framePointIndex f b)).val % 3 := congrArg Fin.val hab
      have h2 := (hsame f a).trans (hsame f b).symm
      have h3 : e (ConfigurationResiduals.framePointIndex f a) =
          e (ConfigurationResiduals.framePointIndex f b) := by
        apply Fin.ext; omega
      have h4 := congrArg Fin.val (e.injective h3)
      rw [hv, hv] at h4
      exact Fin.ext (by omega)
    let τ : Fin 13 → Equiv.Perm (Fin 3) := fun f =>
      Equiv.ofBijective (τf f) (Finite.injective_iff_bijective.1 (hτinj f))
    refine ⟨σ, τ, ?_⟩
    ext p
    have hp : p = ConfigurationResiduals.framePointIndex ⟨p.val / 3, by omega⟩ ⟨p.val % 3, by omega⟩ := by
      apply Fin.ext; rw [hv]; simp only; omega
    rw [hp, NativeFrameRelabelling.pointPerm_framePointIndex, hv]
    have h := hsame ⟨p.val / 3, by omega⟩ ⟨p.val % 3, by omega⟩
    change _ = 3 * ((e (ConfigurationResiduals.framePointIndex ⟨p.val / 3, by omega⟩ 0)).val / 3) +
      (e (ConfigurationResiduals.framePointIndex ⟨p.val / 3, by omega⟩ ⟨p.val % 3, by omega⟩)).val % 3
    omega
  · rintro ⟨σ, τ, rfl⟩ p q
    exact NativeFrameRelabelling.pointPerm_same_frame σ τ p q

theorem pointPerm_mem_framePerm (σ : Equiv.Perm (Fin 13)) (τ : Fin 13 → Equiv.Perm (Fin 3)) :
    NativeFrameRelabelling.pointPerm σ τ ∈ framePerm :=
  (mem_framePerm_iff _).2 ⟨σ, τ, rfl⟩

instance : Finite framePerm := inferInstance

/-- `Π` is finite and carries the discrete topology. -/
instance : TopologicalSpace framePerm := ⊥

instance : DiscreteTopology framePerm := ⟨rfl⟩

/-! ## Actions on configurations -/

/-- The label action `e • C = C ∘ e⁻¹` of any permutation of the 39 labels. -/
def permAct (e : Equiv.Perm (Fin 39)) (C : Cfg) : Cfg := fun i => C (e.symm i)

theorem permAct_apply (e : Equiv.Perm (Fin 39)) (C : Cfg) (i : Fin 39) :
    permAct e C i = C (e.symm i) := rfl

theorem permAct_one (C : Cfg) : permAct 1 C = C := rfl

theorem permAct_mul (e e' : Equiv.Perm (Fin 39)) (C : Cfg) :
    permAct (e * e') C = permAct e (permAct e' C) := rfl

/-- The accepted pullback relabelling is the inverse label action. -/
theorem relabel_eq_permAct (σ : Equiv.Perm (Fin 13)) (τ : Fin 13 → Equiv.Perm (Fin 3)) (C : Cfg) :
    NativeFrameRelabelling.relabel σ τ C = permAct (NativeFrameRelabelling.pointPerm σ τ)⁻¹ C := rfl

/-- The label action as a continuous linear map. -/
def permLin (e : Equiv.Perm (Fin 39)) : Cfg →L[ℝ] Cfg :=
  LinearMap.toContinuousLinearMap
    { toFun := permAct e
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem permLin_apply (e : Equiv.Perm (Fin 39)) (C : Cfg) : permLin e C = permAct e C := rfl

/-- The `G`- and label actions commute. -/
theorem permAct_actC (e : Equiv.Perm (Fin 39)) (A : CEnd) (C : Cfg) :
    permAct e (actC A C) = actC A (permAct e C) := by
  funext i
  rw [permAct_apply, actC_apply, actC_apply, permAct_apply]

/-- The product group `G × Π`. -/
abbrev Big := autGroup × framePerm

/-- `(g, e) • C = g • (e • C)`. -/
def bigAct (γ : Big) (C : Cfg) : Cfg := actC (autVal γ.1) (permAct (γ.2 : Equiv.Perm (Fin 39)) C)

instance : MulAction Big Cfg where
  smul := bigAct
  one_smul C := by
    show actC 1 (permAct 1 C) = C
    rw [actC_one]; rfl
  mul_smul γ δ C := by
    show actC (autVal γ.1 * autVal δ.1)
        (permAct ((γ.2 : Equiv.Perm (Fin 39)) * (δ.2 : Equiv.Perm (Fin 39))) C) =
      actC (autVal γ.1) (permAct (γ.2 : Equiv.Perm (Fin 39))
        (actC (autVal δ.1) (permAct (δ.2 : Equiv.Perm (Fin 39)) C)))
    rw [actC_mul, ContinuousLinearMap.comp_apply, permAct_actC, permAct_mul]

theorem big_smul_def (γ : Big) (C : Cfg) :
    γ • C = actC (autVal γ.1) (permAct (γ.2 : Equiv.Perm (Fin 39)) C) := rfl

theorem big_smul_apply (γ : Big) (C : Cfg) (i : Fin 39) :
    (γ • C) i = autVal γ.1 (C ((γ.2 : Equiv.Perm (Fin 39)).symm i)) := by
  rw [big_smul_def, actC_apply, permAct_apply]

/-- Composition convention: the product of `G × Π` is componentwise. -/
theorem big_mul_def (γ δ : Big) : γ * δ = (γ.1 * δ.1, γ.2 * δ.2) := rfl

/-- The action is a left action: `(γ * δ) • C = γ • (δ • C)`. -/
theorem big_mul_smul (γ δ : Big) (C : Cfg) : (γ * δ) • C = γ • (δ • C) := mul_smul γ δ C

/-- Inverse convention: `(g, e)⁻¹ = (g⁻¹, e⁻¹)`, with `autVal g⁻¹ = Ring.inverse (autVal g)`. -/
theorem big_inv_def (γ : Big) : γ⁻¹ = (γ.1⁻¹, γ.2⁻¹) := rfl

theorem big_inv_smul_smul (γ : Big) (C : Cfg) : γ⁻¹ • (γ • C) = C := inv_smul_smul γ C

theorem big_smul_inv_smul (γ : Big) (C : Cfg) : γ • (γ⁻¹ • C) = C := smul_inv_smul γ C

/-- The action of one element as a continuous linear map. -/
def bigLin (γ : Big) : Cfg →L[ℝ] Cfg := (actC (autVal γ.1)).comp (permLin (γ.2 : Equiv.Perm (Fin 39)))

theorem bigLin_apply (γ : Big) (C : Cfg) : bigLin γ C = γ • C := by
  rfl

/-- The action is jointly continuous. -/
instance : ContinuousSMul Big Cfg := by
  refine ⟨?_⟩
  have hperm : Continuous fun q : framePerm × Cfg => permAct (q.1 : Equiv.Perm (Fin 39)) q.2 :=
    continuous_prod_of_discrete_left.2 fun e => (permLin (e : Equiv.Perm (Fin 39))).continuous
  have hA : Continuous fun p : Big × Cfg => autVal p.1.1 :=
    isEmbedding_autVal.continuous.comp (continuous_fst.comp continuous_fst)
  have hP : Continuous fun p : Big × Cfg => permAct (p.1.2 : Equiv.Perm (Fin 39)) p.2 :=
    hperm.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  exact actC.continuous₂.comp (hA.prodMk hP)

/-! ## Preservation of the original zero set -/

theorem permAct_mem_zeroSet_iff {e : Equiv.Perm (Fin 39)} (he : e ∈ framePerm) (C : Cfg) :
    permAct e C ∈ zeroSet ↔ C ∈ zeroSet := by
  obtain ⟨σ, τ, hστ⟩ := (mem_framePerm_iff e⁻¹).1 (framePerm.inv_mem he)
  have hrel : permAct e C = NativeFrameRelabelling.relabel σ τ C := by
    rw [relabel_eq_permAct, ← hστ, inv_inv]
  have hZ : ∀ X : Cfg, X ∈ zeroSet ↔ ∀ r : Fin 2184,
      MvPolynomial.eval (PartialAction.pack X) (ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r)
        = 0 := by
    intro X
    exact funext_iff
  rw [hZ, hZ, hrel]
  exact NativeFrameRelabelling.all_original_F_iff σ τ (1 / 2 : ℝ) (1 / 3 : ℝ) C

theorem actC_mem_zeroSet_iff {A : CEnd} (hA : A ∈ autC) (C : Cfg) :
    actC A C ∈ zeroSet ↔ C ∈ zeroSet :=
  originalF_actC_eq_zero_iff hA C

theorem big_smul_mem_zeroSet_iff (γ : Big) (C : Cfg) : γ • C ∈ zeroSet ↔ C ∈ zeroSet := by
  rw [big_smul_def, actC_mem_zeroSet_iff (autVal_mem γ.1), permAct_mem_zeroSet_iff γ.2.2]

end CKM.NativeUnlabelledSlice

#print axioms CKM.NativeUnlabelledSlice.autGroup
#print axioms CKM.NativeUnlabelledSlice.autVal_inv
#print axioms CKM.NativeUnlabelledSlice.autVal_injective
#print axioms CKM.NativeUnlabelledSlice.autGroupEquiv
#print axioms CKM.NativeUnlabelledSlice.isEmbedding_autVal
#print axioms CKM.NativeUnlabelledSlice.range_autVal
#print axioms CKM.NativeUnlabelledSlice.instCompactSpaceSubtypeUnitsCEndMemSubgroupAutGroup
#print axioms CKM.NativeUnlabelledSlice.mem_framePerm_iff
#print axioms CKM.NativeUnlabelledSlice.permLin_apply
#print axioms CKM.NativeUnlabelledSlice.permAct_actC
#print axioms CKM.NativeUnlabelledSlice.big_smul_apply
#print axioms CKM.NativeUnlabelledSlice.bigLin_apply
#print axioms CKM.NativeUnlabelledSlice.permAct_mem_zeroSet_iff
#print axioms CKM.NativeUnlabelledSlice.big_smul_mem_zeroSet_iff

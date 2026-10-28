module

public import NativePhaseFullNormalBound

@[expose] public section

/-! The actual complete native normal zero germ, as a homeomorphism onto the
common-plus-four-axis model. Every source/target neighborhood remains explicit.
Dimensions below are linear model dimensions, not topological dimension claims. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.PhaseNormalForm
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CKM.NativeSliceNormalSplitting CKM.NativeSliceImplicitReduction
open BookHT PhaseSheetChart PhaseRangeReduction PhaseFullNormalBound
open Filter Topology
variable {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)

def zeroModel (ξ : Fin 4 → ℂ) : Set (ReducedCoordinates ξ) :=
  {q | q.2=0 ∧ ∃ i : Fin 4, FourBlock.OnAxis i q.1.2}
def nativeZeros (ξ : Fin 4 → ℂ) : Set (Normal ξ) :=
  {n | AnalyticDerivative.originalF (literalCfg ξ+(n : Cfg))=0}
def chartDomain (V : Set (Normal ξ)) : Set (ReducedCoordinates ξ) :=
  (reducedPH hξ).source ∩ (reducedPH hξ) ⁻¹' V

/-- Arbitrarily prescribed smaller neighborhoods are respected. The codomain
is the complete original-equation zero set, not just constructed family images. -/
theorem normal_form_homeomorph : ∃ δ : ℝ, 0 < δ ∧
    ∀ V : Set (Normal ξ), IsOpen V → (0 : Normal ξ) ∈ V →
      V ⊆ Metric.ball 0 δ →
      IsOpen (chartDomain hξ V) ∧ (0 : ReducedCoordinates ξ) ∈ chartDomain hξ V ∧
      chartDomain hξ V ⊆ (reducedPH hξ).source ∧
      (reducedPH hξ) '' chartDomain hξ V = V ∧
      ∃ e : ↥(chartDomain hξ V ∩ zeroModel ξ) ≃ₜ ↥(V ∩ nativeZeros ξ),
        (∀ q, (e q : Normal ξ) = reducedPH hξ q.1) ∧
        (∀ n, (e.symm n : ReducedCoordinates ξ) = (reducedPH hξ).symm n.1) := by
  obtain ⟨δ,hδ,hzero⟩ := local_normal_zero_iff hξ
  refine ⟨δ,hδ,?_⟩
  intro V hV hV0 hsmall
  have ht (n : Normal ξ) (hn : n ∈ V) :=
    hzero n (by simpa only [Metric.mem_ball,dist_zero_right] using hsmall hn)
  have hopen : IsOpen (chartDomain hξ V) :=
    (reducedPH hξ).isOpen_inter_preimage hV
  have hsource : chartDomain hξ V ⊆ (reducedPH hξ).source := Set.inter_subset_left
  have himage : (reducedPH hξ) '' chartDomain hξ V = V := by
    ext n
    constructor
    · rintro ⟨q,hq,rfl⟩; exact hq.2
    · intro hn
      refine ⟨(reducedPH hξ).symm n,?_,(reducedPH hξ).right_inv (ht n hn).1⟩
      exact ⟨(reducedPH hξ).map_target (ht n hn).1,by
        change reducedPH hξ ((reducedPH hξ).symm n) ∈ V
        rwa [(reducedPH hξ).right_inv (ht n hn).1]⟩
  have hzimage : (reducedPH hξ) '' (chartDomain hξ V ∩ zeroModel ξ) = V ∩ nativeZeros ξ := by
    ext n
    constructor
    · rintro ⟨q,⟨hq,hqa⟩,rfl⟩
      refine ⟨hq.2,(ht _ hq.2).2.mpr ?_⟩
      rw [(reducedPH hξ).left_inv hq.1]
      exact hqa
    · rintro ⟨hn,hnz⟩
      have hnt := (ht n hn).1
      refine ⟨(reducedPH hξ).symm n,⟨?_,(ht n hn).2.mp hnz⟩,(reducedPH hξ).right_inv hnt⟩
      exact ⟨(reducedPH hξ).map_target hnt,by
        change reducedPH hξ ((reducedPH hξ).symm n) ∈ V
        rwa [(reducedPH hξ).right_inv hnt]⟩
  refine ⟨hopen,⟨zero_mem_reducedPH_source hξ,?_⟩,hsource,himage,?_⟩
  · change reducedPH hξ 0 ∈ V
    rwa [reducedPH_zero]
  · let e := (reducedPH hξ).homeomorphOfImageSubsetSource
      (fun q hq => hsource hq.1) hzimage
    exact ⟨e,fun _ => rfl,fun _ => rfl⟩

include hξ in
/-- The native common factor is the actual accepted common tangent space. -/
theorem common_finrank : Module.finrank ℝ (Common ξ) = 4 := finrank_fixQK hξ

/-- Actual Book axis, with the original outer-Pi norm inherited as a submodule. -/
def axisSpace (i : Fin 4) : Submodule ℝ Blocks where
  carrier := {z | FourBlock.OnAxis i z}
  zero_mem' := by intro j hj; rfl
  add_mem' := by intro x y hx hy j hj; simp only [Pi.add_apply,hx j hj,hy j hj,add_zero]
  smul_mem' := by intro a x hx j hj; simp only [Pi.smul_apply,hx j hj,smul_zero]

def axisEquiv (i : Fin 4) : Triple ≃ₗ[ℝ] axisSpace i where
  toFun u := ⟨Pi.single i u,by intro j hj; simp [hj]⟩
  invFun z := z.1 i
  left_inv u := by simp
  right_inv z := by
    apply Subtype.ext
    ext j
    by_cases hj : j=i
    · subst j; simp
    · simp [hj,z.property j hj]
  map_add' u v := by
    apply Subtype.ext
    ext j
    by_cases hj : j=i
    · subst j; simp
    · simp [hj]
  map_smul' a u := by
    apply Subtype.ext
    ext j
    by_cases hj : j=i
    · subst j; simp
    · simp [hj]

theorem axis_finrank (i : Fin 4) : Module.finrank ℝ (axisSpace i) = 6 := by
  rw [← (axisEquiv i).finrank_eq]
  exact BookHT.NativeNormalKernelBridge.finrank_triple_real

include hξ in
theorem sheet_model_finrank (i : Fin 4) : Module.finrank ℝ (Common ξ × axisSpace i) = 10 := by
  rw [Module.finrank_prod,common_finrank hξ,axis_finrank]

end Option2.NativeStress.PhaseNormalForm
#print axioms Option2.NativeStress.PhaseNormalForm.normal_form_homeomorph
#print axioms Option2.NativeStress.PhaseNormalForm.sheet_model_finrank

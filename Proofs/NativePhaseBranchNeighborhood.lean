module

public import NativePhaseSheetMultiplier

@[expose] public section

/-!
# Pointwise native complex sheet isolation

The original polynomial residual ideal is used without radicalization.
Analytic germ identities are transferred to an actual neighborhood, with a
single neighborhood for all 1053 coordinate equations. Nothing here asserts
real nonvanishing density, a ten-dimensional slice, or full zero exhaustion.

-/

noncomputable section
namespace Option2.NativeStress.PhaseBranchNeighborhoodA7
open CKM.NativeFirstOrder CKM.NativeFourFamily
open PhasePivotA6 PhasePivotLocusA6 PhaseJetBoundA6 PhaseHilbertA6
open PhaseAnalyticBranchesA6 PhaseSheetMultiplierA7 ConvergentResidualJets
open Filter
open scoped Topology

/-- All actual translated original residuals vanish at this displacement. -/
def NativeComplexZero (ξ : Fin 4 → ℂ) (x : Fin 1053 → ℂ) : Prop :=
  ∀ r : Fin 2184, MvPolynomial.eval x (nativeRows ξ r) = 0

private def zeroFunctionIdeal (ξ : Fin 4 → ℂ) : Ideal (PolyCalc.analyticAtZero 1053) where
  carrier := {f | ∀ᶠ x in 𝓝 0, NativeComplexZero ξ x → f.1 x = 0}
  zero_mem' := Filter.Eventually.of_forall fun _ _ => rfl
  add_mem' := by
    intro f g hf hg
    filter_upwards [hf,hg] with x hx hy hz
    change f.1 x + g.1 x = 0
    rw [hx hz,hy hz,add_zero]
  smul_mem' := by
    intro a f hf
    filter_upwards [hf] with x hx hz
    change a.1 x * f.1 x = 0
    rw [hx hz,mul_zero]

private theorem toGerm_surjective : Function.Surjective (PolyCalc.toGerm 1053) := by
  rintro ⟨_,f,hf,rfl⟩
  exact ⟨⟨f,hf⟩,rfl⟩

private theorem nativeIdeal_le_zeroFunctionMap (ξ : Fin 4 → ℂ) :
    nativePhaseAnalyticIdeal ξ ≤
      (zeroFunctionIdeal ξ).map (PolyCalc.toGerm 1053).toRingHom := by
  apply Ideal.map_le_iff_le_comap.2
  apply Ideal.span_le.2
  rintro _ ⟨r,rfl⟩
  let c : Fin 1053 → (Fin 1053 → ℂ) → ℂ := fun j x => x j
  have hc : ∀ j, AnalyticAt ℂ (c j) 0 := PolyCalc.analyticAt_coord 1053
  let f : PolyCalc.analyticAtZero 1053 :=
    MvPolynomial.aeval (fun j => PolyCalc.analyticElt 1053 (c j) (hc j)) (nativeRows ξ r)
  have hf : f ∈ zeroFunctionIdeal ξ := by
    apply Filter.Eventually.of_forall
    intro x hx
    rw [PolyCalc.coe_aeval_analytic c hc]
    simpa [MvPolynomial.aeval_def,Algebra.algebraMap_self,c] using hx r
  have he : PolyCalc.toGerm 1053 f = polynomialGerm 1053 (nativeRows ξ r) := by
    change PolyCalc.toGerm 1053 (MvPolynomial.aeval _ _) = _
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  change polynomialGerm 1053 (nativeRows ξ r) ∈
    (zeroFunctionIdeal ξ).map (PolyCalc.toGerm 1053).toRingHom
  rw [← he]
  exact Ideal.mem_map_of_mem (PolyCalc.toGerm 1053).toRingHom hf

/-- Membership in the actual native residual ideal implies pointwise
vanishing on original zeros near the basepoint, for any analytic representative. -/
theorem nativeIdeal_representative_vanishes (ξ : Fin 4 → ℂ)
    (f : (Fin 1053 → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0)
    (hm : ofAnalyticAt f hf ∈ nativePhaseAnalyticIdeal ξ) :
    ∀ᶠ x in 𝓝 0, NativeComplexZero ξ x → f x = 0 := by
  have hm' := nativeIdeal_le_zeroFunctionMap ξ hm
  obtain ⟨g,hg,he⟩ :=
    (Ideal.mem_map_iff_of_surjective (PolyCalc.toGerm 1053).toRingHom
      toGerm_surjective).1 hm'
  have he' : g.1 =ᶠ[𝓝 0] f := (ofAnalyticAt_eq_iff g.2 hf).1 he
  filter_upwards [hg,he'] with x hx heq hz
  exact heq ▸ hx hz

/-- Away from one analytic multiplier which is a nonzero germ on the
selected actual branch, the entire original complex zero set locally equals
that branch. The displayed analytic retraction and one common neighborhood
are constructed; neither pointwise identity is supplied as a hypothesis. -/
theorem native_complex_sheet_isolation (u : NativePhaseTorus)
    (hgood : IsGoodPhase u.1) (hpivot : u ∈ nativePivotLocus) (H : Fin 4) :
    ∃ κ : (Fin 1053 → ℂ) → ℂ, AnalyticAt ℂ κ 0 ∧
      ¬ ((fun y => κ (branch H u.1 hgood.1 y)) =ᶠ[𝓝 0] 0) ∧
      ∃ ρ : (Fin 1053 → ℂ) → (Fin 62 → ℂ),
        AnalyticAt ℂ ρ 0 ∧ ρ 0 = 0 ∧
        ((fun y => ρ (branch H u.1 hgood.1 y)) =ᶠ[𝓝 0] id) ∧
        ∃ U : Set (Fin 1053 → ℂ), IsOpen U ∧ 0 ∈ U ∧
          ∀ x ∈ U, κ x ≠ 0 →
            (NativeComplexZero u.1 x ↔ x = branch H u.1 hgood.1 (ρ x)) := by
  obtain ⟨k,hknz,hkmul⟩ := native_phase_sheet_multiplier u hgood hpivot H
  obtain ⟨κ,hκ,hκeq⟩ := k.2
  have hkrep : ofAnalyticAt κ hκ = k := Subtype.ext hκeq
  let φ := branch H u.1 hgood.1
  have hφ : AnalyticAt ℂ φ 0 := branch_analyticAt H u.1 hgood.1
  have hφ0 : φ 0 = 0 := branch_zero H u.1 hgood.1
  have hφd := branch_hasFDerivAt H u.1 hgood.1
  obtain ⟨L,hL⟩ := branchDerivative_leftInverse H u.1 hgood.1
  let e := AnalyticPullback.chart φ hφ hφd hL
  let ρ := e.symm ∘ L
  have hρ : AnalyticAt ℂ ρ 0 := AnalyticPullback.chartSymmComp_analyticAt φ hφ hφ0 hφd hL
  have hρ0 : ρ 0 = 0 := AnalyticPullback.chartSymmComp_zero φ hφ hφ0 hφd hL
  have hinv : (fun y => ρ (φ y)) =ᶠ[𝓝 0] id :=
    e.eventually_left_inverse (AnalyticPullback.zero_mem_chart_source φ hφ hφd hL)
  have hnz : ¬ ((fun y => κ (φ y)) =ᶠ[𝓝 0] 0) := by
    intro hz
    apply hknz
    rw [← hkrep,branchPullback,AnalyticPullback.pullback_ofAnalyticAt,
      AnalyticPullback.ofAnalyticAt_eq_zero_iff]
    exact hz
  have hall : ∀ j : Fin 1053, ∀ᶠ x in 𝓝 0,
      NativeComplexZero u.1 x → κ x * (x j - φ (ρ x) j) = 0 := by
    intro j
    let d : (Fin 1053 → ℂ) → ℂ := fun x => x j - φ (ρ x) j
    have hd : AnalyticAt ℂ d 0 :=
      (PolyCalc.analyticAt_coord 1053 j).sub
        ((AnalyticPullback.analyticAt_apply φ hφ hφ0 j).comp_of_eq hρ hρ0)
    have hdker : branchPullback H u.1 hgood.1 (ofAnalyticAt d hd) = 0 := by
      rw [branchPullback,AnalyticPullback.pullback_ofAnalyticAt,
        AnalyticPullback.ofAnalyticAt_eq_zero_iff]
      filter_upwards [hinv] with y hy
      change φ y j - φ (ρ (φ y)) j = 0
      simp only [hy,id_eq,sub_self]
    have hmul : ofAnalyticAt (fun x => κ x * d x) (hκ.mul hd) ∈
        nativePhaseAnalyticIdeal u.1 := by
      change ofAnalyticAt κ hκ * ofAnalyticAt d hd ∈ _
      rw [hkrep]
      exact hkmul _ hdker
    exact nativeIdeal_representative_vanishes u.1 _ (hκ.mul hd) hmul
  obtain ⟨U,hUsub,hU,h0⟩ := mem_nhds_iff.1 (Filter.eventually_all.2 hall)
  refine ⟨κ,hκ,hnz,ρ,hρ,hρ0,hinv,U,hU,h0,?_⟩
  intro x hx hkx
  constructor
  · intro hz
    funext j
    exact sub_eq_zero.1 ((mul_eq_zero.1 (hUsub hx j hz)).resolve_left hkx)
  · intro he r
    rw [he]
    exact branch_original_rows H u.1 hgood.1 r _

#print axioms nativeIdeal_representative_vanishes
#print axioms native_complex_sheet_isolation
end Option2.NativeStress.PhaseBranchNeighborhoodA7

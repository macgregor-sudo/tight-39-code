module

public import PairingDefinitions
public import PairingResidual
public import NativeActualStateEquivalence
public import NativeAnchorFixerClassification
public import NativeActualNineFrameDictionary
public import NativeNormalizedA2Headline
public import A3Family
public import NativeOriginalGIdempotencyDifferential
public import A4Main

/-!
# Existing A1, A2 and A4 proof adapters

Proof/helper declarations extracted from A1Compatibility,
A1NineFrameCompatibility, A2PublicAdapter and A4PublicAdapter.
Problem definitions are supplied by PairingDefinitions; the proved residual
identity is supplied by PairingResidual. No Challenge proof placeholders
are imported. Native helper definitions required by these proofs are retained.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise Manifold ContDiff Topology

-- Existing declarations from A1Compatibility.lean
namespace Option2StatementA1
open CompactAlbert CompactAlbert.ActualQuartetStates
open QuadraticCertificate.ExactCKMConfiguration QuadraticCertificate.ExactCKMSharedFrames
open NativePolynomial.ConfigurationResiduals UnitaryErrorBases.ComplexQuartet

theorem state_equivalence : ∃ e : State ≃ SU3,
    (∀ x, (e x).val = (3 : ℂ) • (toTitsCoordinates x.val).2.2) ∧
    (∀ U, (e.symm U).val = nativeComplementaryPoint U.val) ∧
    (∀ x, e.symm (e x) = x) ∧ (∀ U, e (e.symm U) = U) := by
  let a : State ≃ ActualQuartetStates.State :=
    { toFun := fun x => ⟨x.val, x.property.1, (actualQuartetReadouts_iff_literal x.val).mpr x.property.2⟩
      invFun := fun x => ⟨x.val, x.property.1, (actualQuartetReadouts_iff_literal x.val).mp x.property.2⟩
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun x => by apply Subtype.ext; rfl }
  let e : State ≃ SU3 := a.trans stateEquivSpecialUnitary
  exact ⟨e, (fun _ => rfl), (fun _ => rfl), e.symm_apply_apply, e.apply_symm_apply⟩

private theorem phase_representative (s : PhaseIndex) :
    ∃ t : Fin 3, (t.val : PhaseIndex) = s := by
  have h : s = 0 ∨ s = 1 ∨ s = 2 := (by decide : ∀ z : PhaseIndex, z = 0 ∨ z = 1 ∨ z = 2) s
  rcases h with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

theorem fixesQuartet_iff_actual (f : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert) :
    FixesQuartet f ↔ ∀ i : Fin 39, i.val < 12 → f (nativePoint i) = nativePoint i := by
  constructor
  · rintro ⟨hE,hP⟩ i hi
    rcases (actual_anchor_labels i).mp hi with ⟨t,rfl⟩ | ⟨s,t,rfl⟩
    · rw [congrFun nativePoint_coordinate_eq_literal t]; exact hE t
    · rw [congrFun (nativePoint_phase_eq_literal s) t]; exact hP _ _
  · intro h
    constructor
    · intro t
      rw [← congrFun nativePoint_coordinate_eq_literal t]
      exact h _ ((actual_anchor_labels _).mpr (Or.inl ⟨t,rfl⟩))
    · intro s t
      obtain ⟨sf,hsf⟩ := phase_representative s
      obtain ⟨tf,htf⟩ := phase_representative t
      rw [← hsf, ← htf, ← congrFun (nativePoint_phase_eq_literal sf) tf]
      exact h _ ((actual_anchor_labels _).mpr (Or.inr ⟨sf,tf,rfl⟩))

theorem quartet_fixer_classification
    (f : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert)
    (hprod : ∀ x y, f (Glennie.jordan x y) = Glennie.jordan (f x) (f y)) :
    FixesQuartet f ↔ ∃! R : TitsComplexMatrix,
      R * R.conjTranspose = 1 ∧ R.det = 1 ∧
      ∀ x : Glennie.Albert, matrixPair (f x) = ((matrixPair x).1, (matrixPair x).2 * R) := by
  rw [fixesQuartet_iff_actual]
  exact native_anchor_fixer_classification f hprod

/-- Every determinant-one right unitary is realized by an actual automorphism. -/
theorem quartet_fixer_converse (R : TitsComplexMatrix)
    (hR : R * R.conjTranspose = (1 : TitsComplexMatrix)) (hdet : R.det = 1) :
    ∃ f : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert,
      (∀ x y : Glennie.Albert,
        f (Glennie.jordan x y) = Glennie.jordan (f x) (f y)) ∧
      FixesQuartet f ∧
      ∀ x : Glennie.Albert,
        matrixPair (f x) = ((matrixPair x).1, (matrixPair x).2 * R) := by
  obtain ⟨f, hprod, hfix, hpair⟩ := native_anchor_fixer_converse R hR hdet
  exact ⟨f, hprod, (fixesQuartet_iff_actual f).mpr hfix, hpair⟩

end Option2StatementA1

-- Existing declarations from A1NineFrameCompatibility.lean
/- Inline after A1 definitions; native Solution side imports NativeActualNineFrameDictionary
and NativeActualStateEquivalence. The theorem signature is the standalone target. -/
namespace Option2StatementA1
open CompactAlbert

theorem nine_frame_array (p : Fin 9 → Fin 3 → Glennie.Albert) :
    ((∀ r, Glennie.Frame (p r) ∧ ∀ k, LiteralReadouts (p r k)) ∧
      ∀ r s, r ≠ s → ∀ k l, Glennie.trace (Glennie.jordan (p r k) (p s l)) = (1/3:ℝ)) ↔
    ∃ U : Fin 9 → TitsComplexMatrix,
      (∀ r, U r * (U r).conjTranspose = 1 ∧ (U r).det = 1) ∧
      (∀ r, p r = nativeCentralTriple (U r) ∨ p r = nativeReverseCentralTriple (U r)) ∧
      ∀ r s, r ≠ s → Matrix.trace ((U r).conjTranspose * U s) = 0 := by
  have h := ActualNineFrameDictionary.actual_nine_frames_iff_trace_orthogonal_array p
  constructor
  · rintro ⟨hf,hc⟩
    exact h.mp ⟨fun r => ⟨(hf r).1, fun k =>
      (ActualQuartetStates.actualQuartetReadouts_iff_literal _).mpr ((hf r).2 k)⟩,hc⟩
  · intro hU
    obtain ⟨hf,hc⟩ := h.mpr hU
    exact ⟨fun r => ⟨(hf r).1, fun k =>
      (ActualQuartetStates.actualQuartetReadouts_iff_literal _).mp ((hf r).2 k)⟩,hc⟩
end Option2StatementA1

-- Existing declarations from A2PublicAdapter.lean
namespace Option2StatementA2.Native
open UnitaryErrorBases.SpecialUnitaryConstraints UnitaryErrorBases.ThreeCycleNormalized
open CompactAlbert CKM.NativeFirstOrder

def charts : Charts where
  su := specialUnitaryLocalChart
  lift := standardCenterLocalLift
  phase := phaseExponentialLocalParam
  representative := standardCenterRepresentative
  quotientAtlas := standardCenterQuotientChartedSpace
  phaseAtlas := phaseExponentialChartedSpace

theorem charts_pinned : ChartsPinned charts := by
  constructor
  · exact self_mem_specialUnitaryLocalChart_source
  · intro Q R
    change (specialUnitaryIdentityCoordinates (Q.val.conjTranspose*R.val)).val = _
    exact tangentNormalCoordinates_fst _
  · exact analyticOnNhd_specialUnitaryLocalChart_symm_val
  · exact standardCenterLocalLift_symm_apply
  · exact standardCenterLocalLift_apply_self
  · exact standardCenterLocalLift_mem_source
  · exact zero_mem_phaseExponentialLocalParam_source
  · intro d x
    rw [show charts.phase = phaseExponentialLocalParam from rfl, phaseExponentialLocalParam_apply]
    rfl
  · exact standardCenterRepresentative_mk
  · rfl
  · intro q; rfl
  · rfl
  · intro d; rfl

def maps : Maps where
  torus := phaseTripleHomeomorph
  array p := nativeNormalizedProjectiveArray (descendedNormalizedParameterProjectiveHomeomorph p)
  configuration := nativeNormalizedDescendedConfiguration

theorem maps_pinned : MapsPinned maps := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hz⟩ := native_normalized_A2
  constructor
  · intro d; exact ⟨rfl,rfl⟩
  · intro z; rfl
  · intro Q d
    change nativeNormalizedProjectiveArray (QuotientGroup.mk Q,phaseTripleHomeomorph d) = _
    rw [nativeNormalizedProjectiveArray_mk]
    change nativeThreeCycleArray Q.val (phaseTripleHomeomorph.symm (phaseTripleHomeomorph d)) = _
    rw [phaseTripleHomeomorph.symm_apply_apply]
    rfl
  · intro p i hi
    have h := (hz p).2.1 i hi
    rw [← literalPoint_low (fun _=>1) i (by omega)] at h
    exact h
  · intro p r k
    exact (hz p).2.2.1 r k

theorem conclusions : Conclusions charts maps := by
  obtain ⟨hm,hdim,_,_,_,hf,hp,hn,_,hz⟩ := native_normalized_A2
  refine ⟨hm,hdim,hf,hp,?_,?_⟩
  · intro p
    obtain ⟨h0,h1,h2⟩ := hn (descendedNormalizedParameterProjectiveHomeomorph p)
    refine ⟨h0, fun r => congrFun h1 r, fun R hR r => congrFun (h2 R hR) r⟩
  · intro p
    funext r
    rw [Option2StatementResidual.originalF_eq_native]
    exact (hz p).2.2.2 r
end Option2StatementA2.Native

namespace Option2StatementA2
theorem full_A2 : FullA2 := ⟨Native.charts,Native.charts_pinned,Native.maps,Native.maps_pinned,Native.conclusions⟩
end Option2StatementA2

-- Existing declarations from A4PublicAdapter.lean
namespace Option2StatementA4
open Glennie CompactAlbert CKM.NativeFirstOrder CKM.NativeDerivationTriality
namespace Native
open CKM.NativeIntrinsicTriality
attribute [local instance 100] LieRing.ofAssociativeRing

def data : Data where
  der := jordanDerivations.toSubmodule
  s := diagonalFixer.toSubmodule
  t := commonCartan.toSubmodule
  skew := skewEnd.toSubmodule
  r0 := R0
  r1 := R1
  ψ := psi.toLinearEquiv
  x := sRootX
  y := sRootY
  pointwise H := (pointwiseFactor H).toSubmodule
  s0 := sAction.g0
  s1 := sAction.g1
  tin := cartanInS
  sq0 := sQuotAction.g0
  sq1 := sQuotAction.g1

theorem data_pinned : Pinned data := by
  constructor
  · exact R0_isNativeAut.1
  · exact R1_isNativeAut.1
  · exact R0_isNativeAut.2
  · exact R1_isNativeAut.2
  · exact R0_cube
  · exact R1_cube
  · exact R0_mul_R1_comm
  · intro D; rfl
  · intro D
    change (Reuse.IsJordanDerivation D ∧ FixesDiagonal D) ↔ _
    simp only [data, mem_jordanDerivations]
    constructor
    · rintro ⟨hD,h0,h1,h2⟩
      refine ⟨hD,?_⟩
      intro i; fin_cases i
      · exact h0
      · exact h1
      · exact h2
    · rintro ⟨hD,h⟩; exact ⟨hD,h 0,h 1,h 2⟩
  · intro D; rfl
  · intro A
    change A∈skewEnd ↔ _
    rw [mem_skewEnd_iff']
    simp only [dot, Glennie.octDot, eq_neg_iff_add_eq_zero]
  · intro x; exact nativeRightMultiply_pair _ x
  · rfl
  · exact psi_apply
  · intro α a
    change ((psi (psi.symm _):skewEnd):Module.End ℝ Octonion) a = _
    rw [LieEquiv.apply_symm_apply]
    unfold rootX rootXFn
    split <;> rfl
  · intro α a
    change ((psi (psi.symm _):skewEnd):Module.End ℝ Octonion) a = _
    rw [LieEquiv.apply_symm_apply]
    unfold rootY rootYFn
    split <;> rfl
  · intro H D
    change D∈pointwiseFactor H ↔ _
    rw [mem_pointwiseFactor]
    simp only [anchorFixedAlg, mem_fixedSpace]
    fin_cases H <;> rfl
  · exact sAction_g0_apply
  · exact sAction_g1_apply
  · intro D; rfl
  · intro D; rfl
  · intro D; rfl

def phase (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : PhaseData data ξ where
  tangent := tangentSpace ξ
  orbit := orbitSpace ξ
  ev := evalDer ξ
  orbitIn := orbitInT ξ
  a0 := (tanAction ξ hξ).g0
  a1 := (tanAction ξ hξ).g1
  o0 := ((tanAction ξ hξ).restrict (orbitInT ξ) (orbitInT_invariant ξ hξ)).g0
  o1 := ((tanAction ξ hξ).restrict (orbitInT ξ) (orbitInT_invariant ξ hξ)).g1
  q0 := (tangentQuotAction ξ hξ).g0
  q1 := (tangentQuotAction ξ hξ).g1
  ad := (adTau ξ hξ).toLinearEquiv
  z := zs ξ hξ
  z0 := (zAction ξ hξ).g0
  z1 := (zAction ξ hξ).g1

theorem phase_pinned (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : PhasePinned data ξ (phase ξ hξ) := by
  constructor
  · rw [Option2StatementResidual.originalF_eq_native]
    funext r
    exact literalCfg_all_original_F ξ hξ r
  · obtain ⟨b⟩ := anchorBinding0_nonempty ξ hξ
    intro i
    change R0 (literalPoint ξ (shifted 0 i)) = literalPoint ξ i
    have hi : outcomeShift shift0 i = shifted 0 i := by fin_cases i <;> rfl
    rw [← hi]
    exact b.generator_fixes i
  · obtain ⟨b⟩ := anchorBinding1_nonempty ξ hξ
    intro i
    change R1 (literalPoint ξ (shifted 1 i)) = literalPoint ξ i
    have hi : outcomeShift shift1 i = shifted 1 i := by fin_cases i <;> rfl
    rw [← hi]
    exact b.generator_fixes i
  · have hf : Option2StatementResidual.originalF = Option2.NativeStress.AnalyticDerivative.originalF :=
      funext Option2StatementResidual.originalF_eq_native
    rw [hf]; rfl
  · exact evalDer_apply ξ
  · rfl
  · intro v; rfl
  · intro v i
    change NativePolynomial.upperCoordinates (R0 (NativePolynomial.fromUpperCoordinates (v.val (outcomeShift shift0 i)))) = _
    have hi : outcomeShift shift0 i = shifted 0 i := by fin_cases i <;> rfl
    rw [hi]; rfl
  · intro v i
    change NativePolynomial.upperCoordinates (R1 (NativePolynomial.fromUpperCoordinates (v.val (outcomeShift shift1 i)))) = _
    have hi : outcomeShift shift1 i = shifted 1 i := by fin_cases i <;> rfl
    rw [hi]; rfl
  · intro v; rfl
  · intro v; rfl
  · intro v; rfl
  · intro v; rfl
  · intro l hl D a
    have he := congrArg (fun f : Module.End ℝ (Module.End ℝ Octonion) => f (psi D) a)
      (adRot_liftEig_eq ξ hξ (liftChoice_sq ξ) hl)
    exact (congrArg (fun f : Module.End ℝ Octonion => f a) (psi_adTau ξ hξ D)).trans he
  · intro D; exact mem_fixedSpace
  · intro D; rfl
  · intro D; rfl

private theorem eqv_native {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {ρ : KAction V} {σ : KAction W}
    (h : Nonempty (KEquiv ρ σ)) : eqv ρ.g0 ρ.g1 σ.g0 σ.g1 := by
  obtain ⟨e⟩ := h
  exact ⟨e.toLinearEquiv,e.map_g0,e.map_g1⟩

private theorem fixed_eq {V : Type*} [AddCommGroup V] [Module ℝ V] (f : Module.End ℝ V) :
    fixed f = fixedSpace f := by
  ext v
  simp [fixed, fixedSpace, LinearMap.mem_eqLocus, LinearMap.mem_ker, sub_eq_zero]

theorem conclusions (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Conclusions data ξ (phase ξ hξ) := by
  obtain ⟨hm,ht,hs,hz⟩ := native_intrinsic_triality ξ hξ
  constructor
  · exact eqv_native hm
  · exact eqv_native ht
  · exact eqv_native hs
  · exact eqv_native hz
  · exact orbitSpace_le_tangentSpace ξ hξ
  · exact evalDer_injective ξ hξ
  · exact finrank_orbitSpace ξ hξ
  · intro H
    let ρ := (tanAction ξ hξ).restrict (orbitInT ξ) (orbitInT_invariant ξ hξ)
    have he : fixed (gen (phase ξ hξ).o0 (phase ξ hξ).o1 H) = ρ.fixH H := by
      change fixed (gen ρ.g0 ρ.g1 H) = ρ.fixH H
      rw [fixed_eq (V := ↥(orbitInT ξ)) (gen ρ.g0 ρ.g1 H)]
      fin_cases H <;> rfl
    exact (congrArg (fun S : Submodule ℝ (orbitInT ξ) => Module.finrank ℝ S) he).trans
      (finrank_orbit_fixH ξ hξ H)
  · let ρ := (tanAction ξ hξ).restrict (orbitInT ξ) (orbitInT_invariant ξ hξ)
    have he : fixed (phase ξ hξ).o0 ⊓ fixed (phase ξ hξ).o1 = ρ.fixK := by
      change fixed ρ.g0 ⊓ fixed ρ.g1 = ρ.fixK
      rw [fixed_eq (V := ↥(orbitInT ξ)) ρ.g0, fixed_eq (V := ↥(orbitInT ξ)) ρ.g1]
      rfl
    exact (congrArg (fun S : Submodule ℝ (orbitInT ξ) => Module.finrank ℝ S) he).trans
      (finrank_orbit_fixK ξ hξ)
  · exact commonCartan_le_diagonalFixer
  · exact fun _ hD _ hE => commonCartan_abelian hD hE
  · exact fun _ hD h => commonCartan_selfCentralizing hD h
  · exact finrank_commonCartan
  · exact fun α _ hh => commonCartan_bracket_sRootX α hh
  · exact fun α _ hh => commonCartan_bracket_sRootY α hh
  · intro l l' hl hl' B a
    exact congrArg (fun f : Module.End ℝ (Module.End ℝ Octonion) => f B a) (adRot_liftEig_eq ξ hξ hl hl')
  · exact adTau_sRootX ξ hξ
  · exact adjointTorus_betaWeight ξ hξ
  · exact adjointTorus_rowWeight ξ hξ
  · exact rowWeight_char
  · exact hexagon_cover
  · exact fun _ _ hne α => hexagon_disjoint hne α
  · exact rootPlane_le_zs_iff ξ hξ
  · exact cartanInS_le_zs ξ hξ
  · exact fun _ _ hα => sRoot_mem_pointwiseFactor hα
  · exact fun _ _ hα a b h => sRoot_plane_inf_pointwiseFactor hα a b h
  · exact finrank_pointwiseFactor
  · exact mem_pointwiseFactor_succ_iff
  · exact mem_hexagon_zero_iff
end Native

theorem full_A4 : FullA4 :=
  ⟨Native.data, Native.data_pinned, fun ξ hξ =>
    ⟨Native.phase ξ hξ,Native.phase_pinned ξ hξ,Native.conclusions ξ hξ⟩⟩
end Option2StatementA4

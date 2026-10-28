module

public import A4DerFixed
public import A3Main
public import A3CommonFixed
public import A4Span

@[expose] public section

/-!
# The actual orbit tangent `O(ξ) ⊆ T(ξ)` and the compensated `K`-action

* `evalDer ξ D = (i ↦ upperCoordinates (D (P_i(ξ))))`, the orbit derivative of the literal 39-point
  configuration (all 1053 real coordinates) along a native derivation `D`.
* Every native derivation gives a tangent vector at every unit phase: `orbitSpace ξ ≤ tangentSpace ξ`.
* The 39 literal projectors span `J` at every unit phase (thirteen mutually orthogonal centred
  two-planes span the trace-zero part), so evaluation is injective and `dim O(ξ) = 52`.
* `K` acts on `T(ξ)` by A3's compensated actions `(R0, shift0)`, `(R1, shift1)`, transported through
  the coordinate decoding; evaluation is equivariant for conjugation of derivations, so `O(ξ)` is
  invariant, with `dim O^H = 16`, `dim O^K = 4`. A3 gives `dim T^H = 26 + 2 r_H`, `dim T^K = 8`.
-/

noncomputable section

namespace CKM.NativeIntrinsicTriality

open Glennie CKM.NativeDerivationTriality CKM.NativeFirstOrder
open NativePolynomial NativePolynomial.ConfigurationResiduals

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Orbit derivative of the literal configuration along an endomorphism. -/
def evalDer (ξ : Fin 4 → ℂ) : Module.End ℝ Albert →ₗ[ℝ] PartialAction.Configuration ℝ :=
  decodeVariation.symm.toLinearMap ∘ₗ LinearMap.pi fun i => LinearMap.applyₗ (literalPoint ξ i)

theorem evalDer_apply (ξ : Fin 4 → ℂ) (D : Module.End ℝ Albert) (i : Fin 39) :
    evalDer ξ D i = upperCoordinates (D (literalPoint ξ i)) := by
  rfl

/-! ## Helpers: decoding, the tangent space and transfer of subspaces -/

theorem decodeVariation_evalDer (ξ : Fin 4 → ℂ) (D : Module.End ℝ Albert) :
    decodeVariation (evalDer ξ D) = fun i => D (literalPoint ξ i) :=
  decodeVariation.apply_symm_apply _

theorem literalCfg_decode (ξ : Fin 4 → ℂ) :
    (fun i => fromUpperCoordinates (literalCfg ξ i)) = literalPoint ξ :=
  funext fun i => fromUpperCoordinates_upperCoordinates (literalPoint ξ i)

/-- The tangent space, decoded: the native first-order system of the literal family. -/
theorem mem_tangentSpace_iff (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (u : PartialAction.Configuration ℝ) :
    u ∈ tangentSpace ξ ↔ decodeVariation u ∈ firstOrderSystem (literalPoint ξ) := by
  rw [tangentSpace, mem_ker_fderiv_originalF_iff _ (literalCfg_all_original_F ξ hξ), literalCfg_decode]

/-- Every point index is a frame/outcome index. -/
theorem exists_framePointIndex (i : Fin 39) : ∃ f a, i = framePointIndex f a :=
  ⟨⟨i.val / 3, by omega⟩, ⟨i.val % 3, by omega⟩,
    Fin.ext (by rw [framePointIndex_val]; show i.val = 3 * (i.val / 3) + i.val % 3; omega)⟩

/-- A Jordan derivation moves any configuration of thirteen frames inside its first-order system. -/
theorem derivation_mem_firstOrderSystem (p : Fin 39 → Albert)
    (hp : ∀ f : Fin 13, Glennie.Frame (fun t : Fin 3 => p (framePointIndex f t)))
    {D : Module.End ℝ Albert} (hD : D ∈ jordanDerivations) :
    (fun i => D (p i)) ∈ firstOrderSystem p := by
  have hD' := mem_jordanDerivations.1 hD
  refine ⟨fun i => ?_, fun f s => ?_, fun f => ?_, fun fg a b => ?_⟩
  · obtain ⟨f, a, rfl⟩ := exists_framePointIndex i
    have h := hD' (p (framePointIndex f a)) (p (framePointIndex f a))
    rw [(hp f).idempotent a] at h
    show (2 : ℝ) • Glennie.jordan (p (framePointIndex f a)) (D (p (framePointIndex f a))) =
      D (p (framePointIndex f a))
    rw [two_smul]
    conv_rhs => rw [h, Glennie.jordan_comm (D _)]
  · have hne : (ConfigurationResidualIndices.withinPair s).val.1 ≠
        (ConfigurationResidualIndices.withinPair s).val.2 :=
      ne_of_lt (ConfigurationResidualIndices.withinPair s).property
    have h := hD' (p (framePointIndex f (ConfigurationResidualIndices.withinPair s).val.1))
      (p (framePointIndex f (ConfigurationResidualIndices.withinPair s).val.2))
    rw [(hp f).orthogonal _ _ hne, map_zero] at h
    rw [add_comm, ← h]
  · have h1 := (hp f).sum_unit
    rw [Fin.sum_univ_three, ← map_add, ← map_add, h1]
    exact derivation_map_one hD'
  · have h := derivation_trace_eq_zero hD' (Glennie.jordan (p (framePointIndex fg.val.1 a))
      (p (framePointIndex fg.val.2 b)))
    rw [hD', ← Glennie.traceLinear_apply, map_add, Glennie.traceLinear_apply,
      Glennie.traceLinear_apply] at h
    rw [add_comm]
    exact h

/-- Transport of a subspace through the decoding equivalence preserves dimension. -/
theorem finrank_eq_of_decode (S : Submodule ℝ (PartialAction.Configuration ℝ))
    (S' : Submodule ℝ (Fin 39 → Albert)) (h : ∀ u, u ∈ S ↔ decodeVariation u ∈ S') :
    Module.finrank ℝ S = Module.finrank ℝ S' := by
  refine (decodeVariation.ofSubmodules S S' ?_).finrank_eq
  ext x
  rw [Submodule.mem_map_equiv, h, LinearEquiv.apply_symm_apply]

/-- The actual orbit tangent: the image of all native Jordan derivations. -/
def orbitSpace (ξ : Fin 4 → ℂ) : Submodule ℝ (PartialAction.Configuration ℝ) :=
  jordanDerivations.toSubmodule.map (evalDer ξ)

theorem orbitSpace_le_tangentSpace (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    orbitSpace ξ ≤ tangentSpace ξ := by
  rintro u ⟨D, hD, rfl⟩
  rw [mem_tangentSpace_iff ξ hξ, decodeVariation_evalDer]
  exact derivation_mem_firstOrderSystem _ (literal_frame ξ hξ) hD

theorem evalDer_injective (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Function.Injective (evalDer ξ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro D hD
  have h : ∀ i, D (literalPoint ξ i) = 0 := fun i => by
    have := congrArg (fun u => decodeVariation u i) hD
    simpa only [decodeVariation_evalDer, map_zero, Pi.zero_apply] using this
  exact LinearMap.ext_on_range (span_literalPoint ξ hξ) (g := 0) fun i => h i

theorem finrank_orbitSpace (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ (orbitSpace ξ) = 52 := by
  rw [orbitSpace, ← (Submodule.equivMapOfInjective _ (evalDer_injective ξ hξ) _).finrank_eq]
  exact finrank_jordanDerivations

/-! ## The compensated `K`-action on configurations and on the tangent space -/

/-- A compensated action `(g, σ)`, transported to the original real coordinates. -/
def confGen (g : Module.End ℝ Albert) (σ : Fin 13 → Fin 3) : Module.End ℝ (PartialAction.Configuration ℝ) :=
  decodeVariation.symm.toLinearMap ∘ₗ compensated g (outcomeShift σ) ∘ₗ decodeVariation.toLinearMap

/-! ### Helpers for the compensated action -/

/-- Conjugation of a variation endomorphism through the coordinate decoding. -/
def decodeConj (F : Module.End ℝ (Fin 39 → Albert)) : Module.End ℝ (PartialAction.Configuration ℝ) :=
  decodeVariation.symm.toLinearMap ∘ₗ F ∘ₗ decodeVariation.toLinearMap

theorem confGen_eq_decodeConj (g : Module.End ℝ Albert) (σ : Fin 13 → Fin 3) :
    confGen g σ = decodeConj (compensated g (outcomeShift σ)) := rfl

theorem decodeVariation_decodeConj (F : Module.End ℝ (Fin 39 → Albert))
    (u : PartialAction.Configuration ℝ) : decodeVariation (decodeConj F u) = F (decodeVariation u) :=
  decodeVariation.apply_symm_apply _

theorem decodeVariation_confGen (g : Module.End ℝ Albert) (σ : Fin 13 → Fin 3)
    (u : PartialAction.Configuration ℝ) :
    decodeVariation (confGen g σ u) = compensated g (outcomeShift σ) (decodeVariation u) :=
  decodeVariation.apply_symm_apply _

theorem decodeConj_mul (F G : Module.End ℝ (Fin 39 → Albert)) :
    decodeConj F * decodeConj G = decodeConj (F * G) := by
  refine LinearMap.ext fun u => decodeVariation.injective ?_
  rw [Module.End.mul_apply, decodeVariation_decodeConj, decodeVariation_decodeConj,
    decodeVariation_decodeConj, Module.End.mul_apply]

theorem decodeConj_one : decodeConj 1 = 1 := by
  refine LinearMap.ext fun u => decodeVariation.injective ?_
  rw [decodeVariation_decodeConj, Module.End.one_apply, Module.End.one_apply]

theorem decodeConj_pow (F : Module.End ℝ (Fin 39 → Albert)) (n : ℕ) :
    decodeConj F ^ n = decodeConj (F ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, decodeConj_one]
  | succ n ih => rw [pow_succ, ih, decodeConj_mul, pow_succ]

theorem compensated_cube (g : Module.End ℝ Albert) (σ : Fin 13 → Fin 3) (hg : g ^ 3 = 1) :
    compensated g (outcomeShift σ) ^ 3 = 1 := by
  have h := compensated_word g 1 σ 0 3 0
  rw [pow_zero, mul_one, pow_zero, mul_one, hg] at h
  rw [h]
  have : (fun f => (3 : ℕ) • σ f + (0 : ℕ) • (0 : Fin 13 → Fin 3) f) = 0 := by
    funext f
    simp only [zero_smul, add_zero, Pi.zero_apply]
    generalize σ f = a
    fin_cases a <;> rfl
  rw [this, compensated_one]

theorem confGen_cube (g : Module.End ℝ Albert) (σ : Fin 13 → Fin 3) (hg : g ^ 3 = 1) :
    confGen g σ ^ 3 = 1 := by
  rw [confGen_eq_decodeConj, decodeConj_pow, compensated_cube g σ hg, decodeConj_one]

theorem confGen_comm : confGen R0 shift0 * confGen R1 shift1 = confGen R1 shift1 * confGen R0 shift0 := by
  rw [confGen_eq_decodeConj, confGen_eq_decodeConj, decodeConj_mul, decodeConj_mul]
  congr 1
  simp only [compensated_mul, outcomeShift_mul, R0_mul_R1_comm, add_comm shift0 shift1]

theorem compensated_anchor2 : compensated (anchorGenerator 2) (outcomeShift (anchorShift 2)) =
    compensated R0 (outcomeShift shift0) ^ 2 * compensated R1 (outcomeShift shift1) ^ 2 := by
  rw [compensated_word]
  congr 2
  funext f
  simp only [anchorShift, two_nsmul]
  generalize shift0 f = a
  generalize shift1 f = b
  revert a b
  decide

theorem compensated_anchor3 : compensated (anchorGenerator 3) (outcomeShift (anchorShift 3)) =
    compensated R0 (outcomeShift shift0) ^ 2 * compensated R1 (outcomeShift shift1) ^ 1 := by
  rw [compensated_word, pow_one]
  congr 2
  funext f
  simp only [anchorShift, two_nsmul, one_nsmul]
  generalize shift0 f = a
  generalize shift1 f = b
  revert a b
  decide

theorem isNativeAut_anchorGenerator (H : Fin 4) : IsNativeAut (anchorGenerator H) := by
  fin_cases H
  · exact R0_isNativeAut
  · exact R1_isNativeAut
  · show IsNativeAut (R0 ^ 2 * R1 ^ 2)
    simp only [pow_two]
    exact isNativeAut_mul (isNativeAut_mul R0_isNativeAut R0_isNativeAut)
      (isNativeAut_mul R1_isNativeAut R1_isNativeAut)
  · show IsNativeAut (R0 ^ 2 * R1)
    simp only [pow_two]
    exact isNativeAut_mul (isNativeAut_mul R0_isNativeAut R0_isNativeAut) R1_isNativeAut

/-- Each anchor generator, compensated and decoded, preserves the tangent space. -/
theorem confGen_anchor_mem (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4)
    {u : PartialAction.Configuration ℝ} (hu : u ∈ tangentSpace ξ) :
    confGen (anchorGenerator H) (anchorShift H) u ∈ tangentSpace ξ := by
  rw [mem_tangentSpace_iff ξ hξ] at hu ⊢
  rw [decodeVariation_confGen]
  exact compensated_mem_firstOrderSystem _ (isNativeAut_anchorGenerator H) _ _
    (anchorBinding_nonempty ξ hξ H).some.generator_fixes hu

theorem mem_fixedSpace_confGen_inf_iff (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (g : Module.End ℝ Albert)
    (σ : Fin 13 → Fin 3) (u : PartialAction.Configuration ℝ) :
    u ∈ fixedSpace (confGen g σ) ⊓ tangentSpace ξ ↔
      decodeVariation u ∈ fixedSpace (compensated g (outcomeShift σ)) ⊓ firstOrderSystem (literalPoint ξ) := by
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_fixedSpace, mem_fixedSpace, mem_tangentSpace_iff ξ hξ,
    ← decodeVariation.injective.eq_iff, decodeVariation_confGen]

/-- For `g³ = 1` fixing the configuration up to `π`, `g² P_i = P_{π i}`. -/
theorem sq_apply_of_fixes {g : Module.End ℝ Albert} (hg3 : g ^ 3 = 1) {π : Equiv.Perm (Fin 39)}
    {P : Fin 39 → Albert} (hfix : ∀ i, g (P (π i)) = P i) (i : Fin 39) : (g ^ 2) (P i) = P (π i) := by
  conv_lhs => rw [← hfix i]
  rw [← Module.End.mul_apply, ← pow_succ, hg3, Module.End.one_apply]

/-- Equivariance of evaluation for a compensated generator fixing the literal configuration. -/
theorem confGen_evalDer_of_fixes (ξ : Fin 4 → ℂ) {g : Module.End ℝ Albert} {σ : Fin 13 → Fin 3}
    (hg3 : g ^ 3 = 1) (hfix : ∀ i, g (literalPoint ξ (outcomeShift σ i)) = literalPoint ξ i)
    (D : Module.End ℝ Albert) : confGen g σ (evalDer ξ D) = evalDer ξ (conjAct g D) := by
  apply decodeVariation.injective
  rw [decodeVariation_confGen, decodeVariation_evalDer, decodeVariation_evalDer]
  funext i
  rw [compensated_apply, conjAct_apply, Module.End.mul_apply, Module.End.mul_apply,
    sq_apply_of_fixes hg3 hfix i]

theorem confGen_R0_mem (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {u : PartialAction.Configuration ℝ}
    (hu : u ∈ tangentSpace ξ) : confGen R0 shift0 u ∈ tangentSpace ξ :=
  confGen_anchor_mem ξ hξ 0 hu

theorem confGen_R1_mem (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {u : PartialAction.Configuration ℝ}
    (hu : u ∈ tangentSpace ξ) : confGen R1 shift1 u ∈ tangentSpace ξ :=
  confGen_anchor_mem ξ hξ 1 hu

theorem restrict_cube_eq_one {M : Type*} [AddCommGroup M] [Module ℝ M] (f : Module.End ℝ M)
    (V : Submodule ℝ M) (hf : ∀ x ∈ V, f x ∈ V) (h : f ^ 3 = 1) : f.restrict hf ^ 3 = 1 :=
  LinearMap.ext fun x => Subtype.ext ((coe_restrict_pow f V hf 3 x).trans (by rw [h]; rfl))

theorem restrict_comm {M : Type*} [AddCommGroup M] [Module ℝ M] (f g : Module.End ℝ M)
    (V : Submodule ℝ M) (hf : ∀ x ∈ V, f x ∈ V) (hg : ∀ x ∈ V, g x ∈ V) (h : f * g = g * f) :
    f.restrict hf * g.restrict hg = g.restrict hg * f.restrict hf :=
  LinearMap.ext fun x => Subtype.ext (congrArg (fun F => F x.1) h)

/-- `K` acting on the actual tangent space `T(ξ)` by the compensated actions. -/
def tanAction (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : KAction (tangentSpace ξ) where
  g0 := (confGen R0 shift0).restrict fun _ hu => confGen_R0_mem ξ hξ hu
  g1 := (confGen R1 shift1).restrict fun _ hu => confGen_R1_mem ξ hξ hu
  g0_cube := restrict_cube_eq_one _ _ _ (confGen_cube R0 shift0 R0_cube)
  g1_cube := restrict_cube_eq_one _ _ _ (confGen_cube R1 shift1 R1_cube)
  comm := restrict_comm _ _ _ _ _ confGen_comm

theorem kAction_gen_two {V : Type*} [AddCommGroup V] [Module ℝ V] (ρ : KAction V) :
    ρ.gen 2 = ρ.g0 ^ 2 * ρ.g1 ^ 2 := rfl
theorem kAction_gen_three {V : Type*} [AddCommGroup V] [Module ℝ V] (ρ : KAction V) :
    ρ.gen 3 = ρ.g0 ^ 2 * ρ.g1 ^ 1 := by
  rw [pow_one]; rfl

theorem restrict_pow_mul_coe {M : Type*} [AddCommGroup M] [Module ℝ M] (f g : Module.End ℝ M)
    (V : Submodule ℝ M) (hf : ∀ x ∈ V, f x ∈ V) (hg : ∀ x ∈ V, g x ∈ V) (m n : ℕ) (x : V) :
    ((f.restrict hf ^ m * g.restrict hg ^ n) x : M) = (f ^ m * g ^ n) x := by
  rw [Module.End.mul_apply, coe_restrict_pow, coe_restrict_pow, Module.End.mul_apply]

theorem tanAction_g0 (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (tanAction ξ hξ).g0 = (confGen R0 shift0).restrict fun _ hu => confGen_R0_mem ξ hξ hu := rfl
theorem tanAction_g1 (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (tanAction ξ hξ).g1 = (confGen R1 shift1).restrict fun _ hu => confGen_R1_mem ξ hξ hu := rfl

theorem confGen_word (m n : ℕ) {H : Fin 4}
    (hw : compensated (anchorGenerator H) (outcomeShift (anchorShift H)) =
      compensated R0 (outcomeShift shift0) ^ m * compensated R1 (outcomeShift shift1) ^ n) :
    confGen R0 shift0 ^ m * confGen R1 shift1 ^ n = confGen (anchorGenerator H) (anchorShift H) := by
  rw [confGen_eq_decodeConj, confGen_eq_decodeConj, confGen_eq_decodeConj, decodeConj_pow,
    decodeConj_pow, decodeConj_mul, hw]

theorem tanAction_gen_coe_word (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (m n : ℕ) {H : Fin 4}
    (hgen : (tanAction ξ hξ).gen H = (tanAction ξ hξ).g0 ^ m * (tanAction ξ hξ).g1 ^ n)
    (hw : compensated (anchorGenerator H) (outcomeShift (anchorShift H)) =
      compensated R0 (outcomeShift shift0) ^ m * compensated R1 (outcomeShift shift1) ^ n)
    (x : tangentSpace ξ) :
    (((tanAction ξ hξ).gen H x : tangentSpace ξ) : PartialAction.Configuration ℝ) =
      confGen (anchorGenerator H) (anchorShift H) x := by
  rw [hgen, tanAction_g0, tanAction_g1, restrict_pow_mul_coe, confGen_word m n hw]

theorem tanAction_gen_coe (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) (x : tangentSpace ξ) :
    (((tanAction ξ hξ).gen H x : tangentSpace ξ) : PartialAction.Configuration ℝ) =
      confGen (anchorGenerator H) (anchorShift H) x := by
  match H with
  | 0 => rfl
  | 1 => rfl
  | 2 => exact tanAction_gen_coe_word ξ hξ 2 2 (kAction_gen_two _) compensated_anchor2 x
  | 3 => exact tanAction_gen_coe_word ξ hξ 2 1 (kAction_gen_three _) compensated_anchor3 x

theorem tanAction_gen_eq (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    (tanAction ξ hξ).gen H =
      (confGen (anchorGenerator H) (anchorShift H)).restrict fun _ hu => confGen_anchor_mem ξ hξ H hu :=
  LinearMap.ext fun x => Subtype.ext (tanAction_gen_coe ξ hξ H x)

theorem finrank_tanAction_fixH (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    Module.finrank ℝ ((tanAction ξ hξ).fixH H) =
      26 + 2 * UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ H) := by
  rw [KAction.fixH, tanAction_gen_eq, finrank_fixedSpace_restrict,
    finrank_eq_of_decode _ _ (mem_fixedSpace_confGen_inf_iff ξ hξ _ _), finrank_anchorFixed]

theorem finrank_tanAction_fixK (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ (tanAction ξ hξ).fixK = 8 := by
  rw [KAction.fixK]
  refine (finrank_fixedSpace_restrict_inf (confGen R0 shift0) (confGen R1 shift1) (tangentSpace ξ)
    (fun _ hu => confGen_R0_mem ξ hξ hu) (fun _ hu => confGen_R1_mem ξ hξ hu)).trans ?_
  refine (finrank_eq_of_decode _ _ fun u => ?_).trans (finrank_commonFixed ξ hξ)
  rw [Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_inf, Submodule.mem_inf, mem_fixedSpace,
    mem_fixedSpace, mem_fixedSpace, mem_fixedSpace, mem_tangentSpace_iff ξ hξ,
    ← decodeVariation.injective.eq_iff, decodeVariation_confGen,
    ← decodeVariation.injective.eq_iff (a := confGen R1 shift1 u), decodeVariation_confGen]

/-- **Equivariance of the orbit map**: the compensated action of `R0` on an orbit derivative is the orbit
derivative of the conjugated derivation. -/
theorem confGen_R0_evalDer (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (D : Module.End ℝ Albert) :
    confGen R0 shift0 (evalDer ξ D) = evalDer ξ (conjAct R0 D) :=
  confGen_evalDer_of_fixes ξ R0_cube (anchorBinding_nonempty ξ hξ 0).some.generator_fixes D

theorem confGen_R1_evalDer (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (D : Module.End ℝ Albert) :
    confGen R1 shift1 (evalDer ξ D) = evalDer ξ (conjAct R1 D) :=
  confGen_evalDer_of_fixes ξ R1_cube (anchorBinding_nonempty ξ hξ 1).some.generator_fixes D

/-- The orbit tangent inside `T(ξ)`. -/
def orbitInT (ξ : Fin 4 → ℂ) : Submodule ℝ (tangentSpace ξ) :=
  (orbitSpace ξ).comap (tangentSpace ξ).subtype

theorem orbitInT_invariant (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (tanAction ξ hξ).IsInvariant (orbitInT ξ) := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨D, hD, hDv⟩ := hv
    show confGen R0 shift0 (v : PartialAction.Configuration ℝ) ∈ orbitSpace ξ
    rw [show (v : PartialAction.Configuration ℝ) = evalDer ξ D from hDv.symm, confGen_R0_evalDer ξ hξ]
    exact ⟨_, conjAct_mem_jordanDerivations R0_isNativeAut R0_cube hD, rfl⟩
  · obtain ⟨D, hD, hDv⟩ := hv
    show confGen R1 shift1 (v : PartialAction.Configuration ℝ) ∈ orbitSpace ξ
    rw [show (v : PartialAction.Configuration ℝ) = evalDer ξ D from hDv.symm, confGen_R1_evalDer ξ hξ]
    exact ⟨_, conjAct_mem_jordanDerivations R1_isNativeAut R1_cube hD, rfl⟩

/-- Evaluation of derivations into the orbit tangent inside `T(ξ)`. -/
def orbitMap (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : jordanDerivations →ₗ[ℝ] orbitInT ξ where
  toFun D := ⟨⟨evalDer ξ D, orbitSpace_le_tangentSpace ξ hξ ⟨D, D.2, rfl⟩⟩, ⟨D, D.2, rfl⟩⟩
  map_add' D E := Subtype.ext (Subtype.ext (map_add (evalDer ξ) (D : Module.End ℝ Albert) E))
  map_smul' c D := Subtype.ext (Subtype.ext (map_smul (evalDer ξ) c (D : Module.End ℝ Albert)))

theorem orbitMap_bijective (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Function.Bijective (orbitMap ξ hξ) := by
  refine ⟨fun D E h => Subtype.ext (evalDer_injective ξ hξ ?_), ?_⟩
  · exact congrArg (fun v : orbitInT ξ => ((v : tangentSpace ξ) : PartialAction.Configuration ℝ)) h
  · rintro ⟨⟨u, hu⟩, hv⟩
    obtain ⟨D, hD, h⟩ := hv
    exact ⟨⟨D, hD⟩, Subtype.ext (Subtype.ext h)⟩

/-- The `K`-equivariant evaluation equivalence `Der(J) ≃ O(ξ)`. -/
def orbitKEquiv (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    KEquiv derAction ((tanAction ξ hξ).restrict (orbitInT ξ) (orbitInT_invariant ξ hξ)) where
  toLinearEquiv := LinearEquiv.ofBijective (orbitMap ξ hξ) (orbitMap_bijective ξ hξ)
  map_g0 D := by
    apply Subtype.ext
    apply Subtype.ext
    show evalDer ξ ((derAction.g0 D : jordanDerivations) : Module.End ℝ Albert) =
      confGen R0 shift0 (evalDer ξ D)
    rw [derAction_g0_apply, confGen_R0_evalDer ξ hξ, conjAct_apply]
  map_g1 D := by
    apply Subtype.ext
    apply Subtype.ext
    show evalDer ξ ((derAction.g1 D : jordanDerivations) : Module.End ℝ Albert) =
      confGen R1 shift1 (evalDer ξ D)
    rw [derAction_g1_apply, confGen_R1_evalDer ξ hξ, conjAct_apply]

theorem finrank_orbit_fixH (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    Module.finrank ℝ (((tanAction ξ hξ).restrict (orbitInT ξ) (orbitInT_invariant ξ hξ)).fixH H) = 16 := by
  rw [← (orbitKEquiv ξ hξ).finrank_fixH_eq H, finrank_derAction_fixH]

theorem finrank_orbit_fixK (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ ((tanAction ξ hξ).restrict (orbitInT ξ) (orbitInT_invariant ξ hξ)).fixK = 4 := by
  rw [← (orbitKEquiv ξ hξ).finrank_fixK_eq, finrank_derAction_fixK]

/-- The orbit tangent inside `T(ξ)` is equivariantly the derivation algebra. -/
theorem orbit_kEquiv_der (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Nonempty (KEquiv derAction ((tanAction ξ hξ).restrict (orbitInT ξ) (orbitInT_invariant ξ hξ))) :=
  ⟨orbitKEquiv ξ hξ⟩

end CKM.NativeIntrinsicTriality

#print axioms CKM.NativeIntrinsicTriality.evalDer_apply
#print axioms CKM.NativeIntrinsicTriality.orbitSpace_le_tangentSpace
#print axioms CKM.NativeIntrinsicTriality.evalDer_injective
#print axioms CKM.NativeIntrinsicTriality.finrank_orbitSpace
#print axioms CKM.NativeIntrinsicTriality.confGen_R0_mem
#print axioms CKM.NativeIntrinsicTriality.confGen_R1_mem
#print axioms CKM.NativeIntrinsicTriality.tanAction
#print axioms CKM.NativeIntrinsicTriality.finrank_tanAction_fixH
#print axioms CKM.NativeIntrinsicTriality.finrank_tanAction_fixK
#print axioms CKM.NativeIntrinsicTriality.confGen_R0_evalDer
#print axioms CKM.NativeIntrinsicTriality.confGen_R1_evalDer
#print axioms CKM.NativeIntrinsicTriality.orbitInT_invariant
#print axioms CKM.NativeIntrinsicTriality.finrank_orbit_fixH
#print axioms CKM.NativeIntrinsicTriality.finrank_orbit_fixK
#print axioms CKM.NativeIntrinsicTriality.orbit_kEquiv_der

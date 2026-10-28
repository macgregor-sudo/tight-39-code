module

public import A3Tangent
public import A3Action
public import A3Elimination
public import A3CommonFixed
public import A3Anchor0
public import A3Anchor1
public import A3Anchor2
public import A3Anchor3

@[expose] public section

/-!
# A3: the native all-phase first-order theorem

For every four-tuple of unit complex phases `ξ`, the kernel of the real derivative of all 2184 original
residual rows, in all 1053 real coordinates, at the literal configuration `P(ξ)` has dimension
`80 + 2 Σ_H r_H(ξ)`, where `r_H(ξ)` counts the entries of the native phase triple `d_H(ξ)` whose cube is
one. No genericity, rank, transport or equivariance hypothesis enters.

Proof (MASTER §6.4–6.5): the tangent space is the native first-order system of `P(ξ)`; the compensated
generators `R0`, `R1` generate a `C₃ × C₃` action on it; finite averaging gives
`dim T = Σ_H dim T^H − 3 dim T^K`; each `T^H` is eliminated, through the anchor binding, to the quartet
first-order space (dimension 8) times the accepted matrix first-order space (dimension `18 + 2 r_H`);
and `dim T^K = 8`.
-/

noncomputable section

namespace CKM.NativeFirstOrder

open NativePolynomial

section Restrict

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

theorem fixedSpace_restrict_eq (f : Module.End ℝ M) (V : Submodule ℝ M) (hV : ∀ x ∈ V, f x ∈ V) :
    fixedSpace (f.restrict hV) = (fixedSpace f ⊓ V).comap V.subtype := by
  ext x
  simp only [mem_fixedSpace, Submodule.mem_comap, Submodule.mem_inf, Submodule.subtype_apply,
    Subtype.ext_iff, LinearMap.coe_restrict_apply, SetLike.coe_mem, and_true]

theorem finrank_fixedSpace_restrict (f : Module.End ℝ M) (V : Submodule ℝ M)
    (hV : ∀ x ∈ V, f x ∈ V) :
    Module.finrank ℝ (fixedSpace (f.restrict hV)) = Module.finrank ℝ ↥(fixedSpace f ⊓ V) := by
  rw [fixedSpace_restrict_eq]
  exact (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq

theorem finrank_fixedSpace_restrict_inf (f g : Module.End ℝ M) (V : Submodule ℝ M)
    (hf : ∀ x ∈ V, f x ∈ V) (hg : ∀ x ∈ V, g x ∈ V) :
    Module.finrank ℝ ↥(fixedSpace (f.restrict hf) ⊓ fixedSpace (g.restrict hg)) =
      Module.finrank ℝ ↥(fixedSpace f ⊓ fixedSpace g ⊓ V) := by
  have h : fixedSpace (f.restrict hf) ⊓ fixedSpace (g.restrict hg) =
      (fixedSpace f ⊓ fixedSpace g ⊓ V).comap V.subtype := by
    ext x
    simp only [Submodule.mem_inf, fixedSpace_restrict_eq, Submodule.mem_comap,
      Submodule.subtype_apply, SetLike.coe_mem, and_true]
  rw [h]
  exact (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq

end Restrict

theorem isNativeAut_mul {g h : Module.End ℝ Glennie.Albert} (hg : IsNativeAut g)
    (hh : IsNativeAut h) : IsNativeAut (g * h) :=
  ⟨fun x y => by simp only [Module.End.mul_apply, hh.jordan, hg.jordan],
   fun x => by simp only [Module.End.mul_apply, hg.trace, hh.trace]⟩

theorem outcomeShift_zero : outcomeShift 0 = 1 := by
  ext i
  simp [outcomeShift, pointRelabel, Equiv.prodShear]

theorem compensated_one : compensated (1 : Module.End ℝ Glennie.Albert) (outcomeShift 0) = 1 := by
  refine LinearMap.ext fun δ => funext fun i => ?_
  rw [compensated_apply, outcomeShift_zero]
  rfl

theorem compensated_word (g h : Module.End ℝ Glennie.Albert) (σ τ : Fin 13 → Fin 3) (m n : ℕ) :
    compensated g (outcomeShift σ) ^ m * compensated h (outcomeShift τ) ^ n =
      compensated (g ^ m * h ^ n) (outcomeShift (fun f => m • σ f + n • τ f)) := by
  have hpow : ∀ (g : Module.End ℝ Glennie.Albert) (σ : Fin 13 → Fin 3) (m : ℕ),
      compensated g (outcomeShift σ) ^ m = compensated (g ^ m) (outcomeShift fun f => m • σ f) := by
    intro g σ m
    induction m with
    | zero =>
      have : (fun f => (0 : ℕ) • σ f) = 0 := by funext f; simp
      rw [pow_zero, pow_zero, this, compensated_one]
    | succ m ih =>
      rw [pow_succ, ih, compensated_mul, outcomeShift_mul, pow_succ]
      congr 2
      funext f
      simp only [Pi.add_apply, succ_nsmul]
      abel
  rw [hpow, hpow, compensated_mul, outcomeShift_mul]
  congr 2
  funext f
  simp only [Pi.add_apply]
  abel

theorem coe_restrict_pow {M : Type*} [AddCommGroup M] [Module ℝ M] (f : Module.End ℝ M)
    (V : Submodule ℝ M) (hf : ∀ x ∈ V, f x ∈ V) (n : ℕ) (x : V) :
    (((f.restrict hf) ^ n) x : M) = (f ^ n) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]; rfl

local instance : FiniteDimensional ℝ Glennie.Albert :=
  LinearEquiv.finiteDimensional upperCoordinateEquiv.symm

/-- **MASTER §4.3.** At any real configuration, the kernel of the Fréchet derivative of all 2184 original
rows equals the kernel of their degree-one coefficient matrix after translation to the point. -/
theorem mem_ker_fderiv_originalF_iff_linearCoefficients (C u : PartialAction.Configuration ℝ) :
    u ∈ LinearMap.ker (fderiv ℝ Option2.NativeStress.AnalyticDerivative.originalF C).toLinearMap ↔
      ∀ r : Fin 2184, (∑ n : Fin 1053, PolynomialJets.equationLinearMatrix
        (fun s : Fin 2184 => PolynomialJets.translate (PartialAction.pack C)
          (ConfigurationResiduals.fRow (1/2 : ℝ) (1/3 : ℝ) s)) r n * PartialAction.pack u n) = 0 := by
  rw [(hasFDerivAt_originalF C).fderiv, LinearMap.mem_ker, funext_iff]
  refine forall_congr' fun r => ?_
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, FunLike.coe_sum,
    Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, packCLM_apply, Pi.zero_apply, PolynomialJets.equationLinearMatrix,
    PolyCalcReal.translate_coeff_single]

/-- The anchor bindings, at every unit phase. -/
theorem anchorBinding_nonempty (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    Nonempty (AnchorBinding (anchorGenerator H) (anchorShift H) (literalPoint ξ) (anchorTriple ξ hξ H)) := by
  fin_cases H
  exacts [anchorBinding0_nonempty ξ hξ, anchorBinding1_nonempty ξ hξ, anchorBinding2_nonempty ξ hξ,
    anchorBinding3_nonempty ξ hξ]

/-- **Fixed-tangent equivalence.** For each anchor `H` and every unit phase, the `H`-fixed native first-order
space of the literal family is real-linearly equivalent to the first-order space of a labelled complex quartet
(of dimension eight) times the accepted unrestricted first-order space of nine special unitaries, whose dimension
is `18 + 2 r_H`. -/
theorem anchorFixed_equiv (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    ∃ (q : Fin 4 → Fin 3 → CompactAlbert.TitsComplexMatrix) (W : UnitaryErrorBases.Family),
      Module.finrank ℝ (quartetFirstOrder q) = 8 ∧
      UnitaryErrorBases.IsUnitaryErrorBasis W ∧
      Module.finrank ℝ (UnitaryErrorBases.firstOrderSpace W) =
        18 + 2 * UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ H) ∧
      Nonempty (↥(fixedSpace (compensated (anchorGenerator H) (outcomeShift (anchorShift H))) ⊓
          firstOrderSystem (literalPoint ξ)) ≃ₗ[ℝ]
        ↥(quartetFirstOrder q) × ↥(UnitaryErrorBases.firstOrderSpace W)) := by
  obtain ⟨b⟩ := anchorBinding_nonempty ξ hξ H
  obtain ⟨e₁⟩ := b.fixedEquiv
  obtain ⟨e₂⟩ := fixed_stdAnchored_equiv b.q b.W b.q_idem b.W_ueb
  exact ⟨_, b.W, b.q_finrank, b.W_ueb, b.W_finrank, ⟨e₁.trans e₂⟩⟩

/-- **Anchor-fixed dimension.** `dim T^H = 26 + 2 r_H` at every unit phase. -/
theorem finrank_anchorFixed (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    Module.finrank ℝ ↥(fixedSpace (compensated (anchorGenerator H) (outcomeShift (anchorShift H))) ⊓
      firstOrderSystem (literalPoint ξ)) =
        26 + 2 * UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ H) := by
  obtain ⟨q, W, hq, -, hW, ⟨e⟩⟩ := anchorFixed_equiv ξ hξ H
  rw [e.finrank_eq, Module.finrank_prod, hq, hW]
  ring

/-- **A3.** The full native first-order tangent dimension at every unit phase. -/
theorem finrank_tangentSpace (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ (tangentSpace ξ) =
      80 + 2 * ∑ H : Fin 4, UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ H) := by
  classical
  obtain ⟨e⟩ := tangentSpace_equiv ξ (literalCfg_all_original_F ξ hξ)
  rw [e.finrank_eq]
  obtain ⟨b0⟩ := anchorBinding0_nonempty ξ hξ
  obtain ⟨b1⟩ := anchorBinding1_nonempty ξ hξ
  obtain ⟨b2⟩ := anchorBinding2_nonempty ξ hξ
  obtain ⟨b3⟩ := anchorBinding3_nonempty ξ hξ
  set P := literalPoint ξ
  set V := firstOrderSystem P
  -- Each anchor's fixed subspace has dimension `26 + 2 r_H`.
  have hfixed : ∀ {H : Fin 4} (b : AnchorBinding (anchorGenerator H) (anchorShift H) P
      (anchorTriple ξ hξ H)),
      Module.finrank ℝ ↥(fixedSpace (compensated (anchorGenerator H) (outcomeShift (anchorShift H))) ⊓ V)
        = 26 + 2 * UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ H) := by
    intro H b
    rw [b.finrank_fixed_eq, finrank_fixed_stdAnchored b.q b.W b.q_idem b.W_ueb, b.q_finrank,
      b.W_finrank]
    ring
  -- Every anchor generator, compensated, preserves the first-order system.
  have hinv : ∀ {H : Fin 4} (g : Module.End ℝ Glennie.Albert), IsNativeAut g →
      AnchorBinding g (anchorShift H) P (anchorTriple ξ hξ H) →
      ∀ x ∈ V, compensated g (outcomeShift (anchorShift H)) x ∈ V :=
    fun g hg b x hx => compensated_mem_firstOrderSystem g hg _ P b.generator_fixes hx
  have hR2 : IsNativeAut (R0 ^ 2 * R1 ^ 2) := by
    simp only [pow_two]
    exact isNativeAut_mul (isNativeAut_mul R0_isNativeAut R0_isNativeAut)
      (isNativeAut_mul R1_isNativeAut R1_isNativeAut)
  have hR3 : IsNativeAut (R0 ^ 2 * R1) := by
    simp only [pow_two]
    exact isNativeAut_mul (isNativeAut_mul R0_isNativeAut R0_isNativeAut) R1_isNativeAut
  have hV0 : ∀ x ∈ V, compensated R0 (outcomeShift shift0) x ∈ V := hinv (H := 0) R0 R0_isNativeAut b0
  have hV1 : ∀ x ∈ V, compensated R1 (outcomeShift shift1) x ∈ V := hinv (H := 1) R1 R1_isNativeAut b1
  have hR2' : IsNativeAut (anchorGenerator 2) := hR2
  have hR3' : IsNativeAut (anchorGenerator 3) := hR3
  have hV2 : ∀ x ∈ V, compensated (anchorGenerator 2) (outcomeShift (anchorShift 2)) x ∈ V :=
    hinv (H := 2) (anchorGenerator 2) hR2' b2
  have hV3 : ∀ x ∈ V, compensated (anchorGenerator 3) (outcomeShift (anchorShift 3)) x ∈ V :=
    hinv (H := 3) (anchorGenerator 3) hR3' b3
  set c0 := compensated R0 (outcomeShift shift0)
  set c1 := compensated R1 (outcomeShift shift1)
  let ρ0 : Module.End ℝ V := c0.restrict hV0
  let ρ1 : Module.End ℝ V := c1.restrict hV1
  -- Group relations.
  have hcube : ∀ (g : Module.End ℝ Glennie.Albert) (σ : Fin 13 → Fin 3), g ^ 3 = 1 →
      compensated g (outcomeShift σ) ^ 3 = 1 := by
    intro g σ hg
    have h := compensated_word g 1 σ 0 3 0
    rw [pow_zero, mul_one, pow_zero, mul_one, hg] at h
    rw [h]
    have : (fun f => (3 : ℕ) • σ f + (0 : ℕ) • (0 : Fin 13 → Fin 3) f) = 0 := by
      funext f
      simp only [zero_smul, add_zero, Pi.zero_apply]
      generalize σ f = a
      fin_cases a <;> rfl
    rw [this, compensated_one]
  have h0 : ρ0 ^ 3 = 1 :=
    LinearMap.ext fun x => Subtype.ext (by
      refine (coe_restrict_pow c0 V hV0 3 x).trans ?_
      rw [hcube R0 shift0 R0_cube]; rfl)
  have h1 : ρ1 ^ 3 = 1 :=
    LinearMap.ext fun x => Subtype.ext (by
      refine (coe_restrict_pow c1 V hV1 3 x).trans ?_
      rw [hcube R1 shift1 R1_cube]; rfl)
  have hcomm_amb : c0 * c1 = c1 * c0 := by
    simp only [c0, c1, compensated_mul, outcomeShift_mul, R0_mul_R1_comm, add_comm shift0 shift1]
  have hcomm : ρ0 * ρ1 = ρ1 * ρ0 :=
    LinearMap.ext fun x => Subtype.ext (congrArg (fun F => F x.1) hcomm_amb)
  -- The four cyclic subgroups are the four anchors.
  have hword : ∀ (m n : ℕ) {H : Fin 4} (hH : ∀ x ∈ V, compensated (anchorGenerator H)
        (outcomeShift (anchorShift H)) x ∈ V),
      compensated (anchorGenerator H) (outcomeShift (anchorShift H)) = c0 ^ m * c1 ^ n →
      Module.finrank ℝ (fixedSpace (ρ0 ^ m * ρ1 ^ n)) =
        Module.finrank ℝ ↥(fixedSpace (compensated (anchorGenerator H)
          (outcomeShift (anchorShift H))) ⊓ V) := by
    intro m n H hH hw
    have : ρ0 ^ m * ρ1 ^ n = (compensated (anchorGenerator H) (outcomeShift (anchorShift H))).restrict hH :=
      LinearMap.ext fun x => Subtype.ext (by
        refine (coe_restrict_pow c0 V hV0 m _).trans ?_
        rw [LinearMap.coe_restrict_apply, hw, Module.End.mul_apply]
        congr 1
        exact coe_restrict_pow c1 V hV1 n x)
    rw [this, finrank_fixedSpace_restrict]
  have w2 : compensated (anchorGenerator 2) (outcomeShift (anchorShift 2)) = c0 ^ 2 * c1 ^ 2 := by
    rw [compensated_word]
    congr 2
    funext f
    simp only [anchorShift, two_nsmul]
    generalize shift0 f = a
    generalize shift1 f = b
    revert a b
    decide
  have w3 : compensated (anchorGenerator 3) (outcomeShift (anchorShift 3)) = c0 ^ 2 * c1 ^ 1 := by
    rw [compensated_word, pow_one]
    congr 2
    funext f
    simp only [anchorShift, two_nsmul, one_nsmul]
    generalize shift0 f = a
    generalize shift1 f = b
    revert a b
    decide
  have f0 := hfixed b0
  have f1 := hfixed b1
  have f2 := hfixed b2
  have f3 := hfixed b3
  rw [show anchorGenerator 0 = R0 from rfl, show anchorShift 0 = shift0 from rfl] at f0
  rw [show anchorGenerator 1 = R1 from rfl, show anchorShift 1 = shift1 from rfl] at f1
  have kK : Module.finrank ℝ ↥(fixedSpace ρ0 ⊓ fixedSpace ρ1) = 8 :=
    (finrank_fixedSpace_restrict_inf c0 c1 V hV0 hV1).trans (finrank_commonFixed ξ hξ)
  have k0 : Module.finrank ℝ (fixedSpace ρ0) =
      26 + 2 * UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ 0) :=
    (finrank_fixedSpace_restrict c0 V hV0).trans f0
  have k1 : Module.finrank ℝ (fixedSpace ρ1) =
      26 + 2 * UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ 1) :=
    (finrank_fixedSpace_restrict c1 V hV1).trans f1
  have k2 : Module.finrank ℝ (fixedSpace (ρ0 ^ 2 * ρ1 ^ 2)) =
      26 + 2 * UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ 2) :=
    (hword 2 2 hV2 w2).trans f2
  have k3 : Module.finrank ℝ (fixedSpace (ρ0 ^ 2 * ρ1)) =
      26 + 2 * UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ 3) := by
    have h := (hword 2 1 hV3 w3).trans f3
    rwa [pow_one] at h
  have key := finrank_add_three_mul_finrank_fixed_inf ρ0 ρ1 hcomm h0 h1
  rw [kK, k0, k1, k2, k3] at key
  rw [Fin.sum_univ_four]
  omega

end CKM.NativeFirstOrder

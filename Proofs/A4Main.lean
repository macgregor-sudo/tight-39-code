module

public import A4Quotient
public import A4Pointwise

@[expose] public section

/-!
# A4: native intrinsic triality, `T(ξ)/O(ξ) ≃_K (s/t) × z_s(τ(ξ))` at every unit phase

Assembly of the preceding representation and centralizer results. The only hypothesis is
`IsUnitPhase ξ := ∀ a, Complex.normSq (ξ a) = 1`; all unit phases, including every resonance, are
covered.

* `T(ξ) = tangentSpace ξ` (A3): the kernel of the real derivative of all 2184 original rows in all
  1053 coordinates at the literal configuration. `O(ξ) = orbitInT ξ`: the image of the actual native
  Jordan derivations under `D ↦ (i ↦ D (P_i(ξ)))`. `K` acts by A3's compensated `(R0, shift0)`,
  `(R1, shift1)`.
* `s = diagonalFixer` (triality block), `t = commonCartan = Der(J)^K` (`cartanInS` inside `s`),
  `s/t` the real vector-space quotient; `K` acts on derivations by conjugation with `R0`, `R1`.
* `τ(ξ) = adjointTorus ξ` on `Q(D₄)` (`β₁ ↦ −A³, β₂ ↦ −B³, β₃ ↦ C³, β₄ ↦ −D³`), its adjoint action
  `adTau ξ` on `s` (orthogonal lift, lift-independent), and `z_s(τ(ξ)) = zs ξ`.
-/

noncomputable section

namespace CKM.NativeIntrinsicTriality

open Glennie CKM.NativeDerivationTriality CKM.NativeFirstOrder

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The product of the two standard models is the standard model of the sum. -/
theorem kEquiv_std_prod (n : Fin 4 → ℕ) :
    Nonempty (KEquiv ((stdAction 0 fun _ => 3).prod (stdAction 4 n)) (stdAction 4 fun H => 3 + n H)) := by
  apply kEquiv_std_of_finrank
  · rw [finrank_fixK_prod, finrank_fixK_std, finrank_fixK_std]
  · intro H
    rw [finrank_fixH_prod, finrank_fixH_std, finrank_fixH_std]
    ring

/-- **A4.** At every unit phase, a `K`-equivariant real-linear equivalence
`T(ξ)/O(ξ) ≃_K (s/t) × z_s(τ(ξ))`, through the three representation decompositions
`T/O ≃_K ℝ⁴ ⊕ ⨁_H V_H^(3+r_H)`, `s/t ≃_K ⨁_H V_H^3`, `z_s(τ) ≃_K ℝ⁴ ⊕ ⨁_H V_H^(r_H)`. -/
theorem native_intrinsic_triality (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Nonempty (KEquiv (tangentQuotAction ξ hξ) (sQuotAction.prod (zAction ξ hξ))) ∧
    Nonempty (KEquiv (tangentQuotAction ξ hξ)
      (stdAction 4 fun H => 3 + UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ H))) ∧
    Nonempty (KEquiv sQuotAction (stdAction 0 fun _ => 3)) ∧
    Nonempty (KEquiv (zAction ξ hξ)
      (stdAction 4 fun H => UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ H))) := by
  obtain ⟨e₁⟩ := tangentQuot_kEquiv ξ hξ
  obtain ⟨e₂⟩ := sQuot_kEquiv
  obtain ⟨e₃⟩ := zs_kEquiv ξ hξ
  have hK : Module.finrank ℝ (sQuotAction.prod (zAction ξ hξ)).fixK = 4 := by
    rw [finrank_fixK_prod, e₂.finrank_fixK_eq, e₃.finrank_fixK_eq, finrank_fixK_std, finrank_fixK_std]
  have hH : ∀ H, Module.finrank ℝ ((sQuotAction.prod (zAction ξ hξ)).fixH H) =
      4 + 2 * (3 + UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ H)) := by
    intro H
    rw [finrank_fixH_prod, e₂.finrank_fixH_eq, e₃.finrank_fixH_eq, finrank_fixH_std, finrank_fixH_std]
    ring
  obtain ⟨e₄⟩ := kEquiv_std_of_finrank (sQuotAction.prod (zAction ξ hξ)) 4 _ hK hH
  exact ⟨⟨e₁.trans e₄.symm⟩, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩

/-- The native objects bound in the endpoint, at every unit phase. -/
theorem native_intrinsic_triality_bindings (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    -- the actual orbit tangent and its fixed dimensions
    orbitSpace ξ ≤ tangentSpace ξ ∧ Function.Injective (evalDer ξ) ∧
    Module.finrank ℝ (orbitSpace ξ) = 52 ∧
    (∀ H, Module.finrank ℝ (((tanAction ξ hξ).restrict (orbitInT ξ) (orbitInT_invariant ξ hξ)).fixH H) = 16) ∧
    Module.finrank ℝ ((tanAction ξ hξ).restrict (orbitInT ξ) (orbitInT_invariant ξ hξ)).fixK = 4 ∧
    -- the common Cartan
    commonCartan ≤ diagonalFixer ∧
    (∀ D ∈ commonCartan, ∀ E ∈ commonCartan, D * E = E * D) ∧
    (∀ D ∈ diagonalFixer, (∀ E ∈ commonCartan, D * E = E * D) → D ∈ commonCartan) ∧
    Module.finrank ℝ commonCartan = 4 ∧
    -- the actual roots
    (∀ α : PosRoot, ∀ h ∈ commonCartan,
      h * (sRootX α : Module.End ℝ Albert) - (sRootX α : Module.End ℝ Albert) * h =
        rootEval α h • (sRootY α : Module.End ℝ Albert)) ∧
    (∀ α : PosRoot, ∀ h ∈ commonCartan,
      h * (sRootY α : Module.End ℝ Albert) - (sRootY α : Module.End ℝ Albert) * h =
        -(rootEval α h • (sRootX α : Module.End ℝ Albert))) ∧
    -- the adjoint torus: lift independence, root values, the twelve signed rows
    (∀ lam lam' : ℂ, lam ^ 2 = liftSq ξ → lam' ^ 2 = liftSq ξ →
      adRot (liftEig ξ lam) = adRot (liftEig ξ lam')) ∧
    (∀ α : PosRoot, adTau ξ hξ (sRootX α) =
      (adjointTorus ξ α.weight).re • sRootX α + (adjointTorus ξ α.weight).im • sRootY α) ∧
    (∀ i, adjointTorus ξ (betaWeight i) = betaValue ξ i) ∧
    (∀ H j, adjointTorus ξ (rowWeight H j) = anchorPhases ξ H j ^ 3) ∧
    (∀ H j, weightChar (rowWeight H j) = kChar H) ∧
    (∀ α, ∃ H, α ∈ hexagon H) ∧ (∀ H H', H ≠ H' → ∀ α, ¬ (α ∈ hexagon H ∧ α ∈ hexagon H')) ∧
    -- the centralizer
    (∀ α : PosRoot, (sRootX α ∈ zs ξ hξ ∧ sRootY α ∈ zs ξ hξ) ↔ adjointTorus ξ α.weight = 1) ∧
    cartanInS ≤ zs ξ hξ ∧
    -- the four pointwise factors
    (∀ H α, α ∈ hexagon H →
      (sRootX α : Module.End ℝ Albert) ∈ pointwiseFactor H ∧
        (sRootY α : Module.End ℝ Albert) ∈ pointwiseFactor H) ∧
    (∀ H α, α ∉ hexagon H → ∀ a b : ℝ,
      a • (sRootX α : Module.End ℝ Albert) + b • (sRootY α : Module.End ℝ Albert) ∈ pointwiseFactor H →
        a = 0 ∧ b = 0) ∧
    (∀ H, Module.finrank ℝ (pointwiseFactor H) = 8) ∧
    (∀ (i : Fin 3) D, D ∈ pointwiseFactor i.succ ↔ transportTinv i * D * transportT i ∈ pointwiseFactor 0) ∧
    (∀ α, α ∈ hexagon 0 ↔ ∃ a b : Fin 3, a ≠ b ∧ α.weight = h0WeightVec a - h0WeightVec b) :=
  ⟨orbitSpace_le_tangentSpace ξ hξ, evalDer_injective ξ hξ, finrank_orbitSpace ξ hξ,
    finrank_orbit_fixH ξ hξ, finrank_orbit_fixK ξ hξ,
    commonCartan_le_diagonalFixer, fun _ hD _ hE => commonCartan_abelian hD hE,
    fun _ hD hc => commonCartan_selfCentralizing hD hc, finrank_commonCartan,
    fun α _ hh => commonCartan_bracket_sRootX α hh, fun α _ hh => commonCartan_bracket_sRootY α hh,
    fun _ _ hl hl' => adRot_liftEig_eq ξ hξ hl hl', adTau_sRootX ξ hξ, adjointTorus_betaWeight ξ hξ,
    adjointTorus_rowWeight ξ hξ, rowWeight_char, hexagon_cover, fun _ _ hne α => hexagon_disjoint hne α,
    rootPlane_le_zs_iff ξ hξ, cartanInS_le_zs ξ hξ,
    fun _ _ hα => sRoot_mem_pointwiseFactor hα, fun _ _ hα a b h => sRoot_plane_inf_pointwiseFactor hα a b h,
    finrank_pointwiseFactor, mem_pointwiseFactor_succ_iff, mem_hexagon_zero_iff⟩

end CKM.NativeIntrinsicTriality

module

public import A3Interfaces
public import A3ElimMain

@[expose] public section

/-!
# Fixed-space elimination in the standard anchored picture

For the standard anchored configuration of an idempotent Hermitian quartet `q` and a unitary error basis
`W`, the `R0`-fixed native first-order variations are exactly parametrized, through `elimForward`, by the
quartet first-order space times the accepted unrestricted matrix first-order space of `W`.
-/

noncomputable section

namespace CKM.NativeFirstOrder

open NativePolynomial NativePolynomial.ConfigurationResiduals CompactAlbert

variable (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian}) (W : UnitaryErrorBases.Family)

/-- `R0` with its shift fixes the standard anchored configuration. -/
theorem R0_stdAnchored (i : Fin 39) : R0 (stdAnchored q W (stdShift i)) = stdAnchored q W i := by
  exact Elim.R0_stdAnchored' q W i

theorem elimForward_mem (hq : ∀ k t, (q k t).val * (q k t).val = (q k t).val)
    (hW : UnitaryErrorBases.IsUnitaryErrorBasis W) {δ : Fin 39 → Glennie.Albert}
    (hfix : δ ∈ fixedSpace (compensated R0 stdShift)) (hδ : δ ∈ firstOrderSystem (stdAnchored q W)) :
    (elimForward δ).1 ∈ quartetFirstOrder (fun k t => (q k t).val) ∧
      (elimForward δ).2 ∈ UnitaryErrorBases.firstOrderSpace W := by
  exact Elim.elimForward_mem' q W hq hW hfix hδ

theorem elimForward_injOn (hq : ∀ k t, (q k t).val * (q k t).val = (q k t).val)
    (hW : UnitaryErrorBases.IsUnitaryErrorBasis W) {δ δ' : Fin 39 → Glennie.Albert}
    (hfix : δ ∈ fixedSpace (compensated R0 stdShift)) (hδ : δ ∈ firstOrderSystem (stdAnchored q W))
    (hfix' : δ' ∈ fixedSpace (compensated R0 stdShift))
    (hδ' : δ' ∈ firstOrderSystem (stdAnchored q W)) (h : elimForward δ = elimForward δ') :
    δ = δ' := by
  -- Injectivity needs only the fixed-point and frame-sum rows; the other hypotheses are not used.
  exact (fun _ _ => Elim.elimForward_injOn' q W hfix hδ hfix' hδ' h) hq hW

theorem elimForward_surjOn (hq : ∀ k t, (q k t).val * (q k t).val = (q k t).val)
    (hW : UnitaryErrorBases.IsUnitaryErrorBasis W)
    (x : (Fin 4 → Fin 3 → TitsComplexMatrix) × UnitaryErrorBases.Family)
    (hx₁ : x.1 ∈ quartetFirstOrder (fun k t => (q k t).val))
    (hx₂ : x.2 ∈ UnitaryErrorBases.firstOrderSpace W) :
    ∃ δ, δ ∈ fixedSpace (compensated R0 stdShift) ∧ δ ∈ firstOrderSystem (stdAnchored q W) ∧
      elimForward δ = x := by
  exact Elim.elimForward_surjOn' q W hq hW x hx₁ hx₂

/-- The elimination map is a real-linear equivalence from the `R0`-fixed first-order variations onto
the quartet first-order space times the unrestricted matrix first-order space of `W`. -/
theorem fixed_stdAnchored_equiv (hq : ∀ k t, (q k t).val * (q k t).val = (q k t).val)
    (hW : UnitaryErrorBases.IsUnitaryErrorBasis W) :
    Nonempty (↥(fixedSpace (compensated R0 stdShift) ⊓ firstOrderSystem (stdAnchored q W)) ≃ₗ[ℝ]
      ↥(quartetFirstOrder fun k t => (q k t).val) × ↥(UnitaryErrorBases.firstOrderSpace W)) := by
  let S := fixedSpace (compensated R0 stdShift) ⊓ firstOrderSystem (stdAnchored q W)
  let Q := quartetFirstOrder fun k t => (q k t).val
  let F := UnitaryErrorBases.firstOrderSpace W
  have hmem : ∀ δ : S, (elimForward δ.1).1 ∈ Q ∧ (elimForward δ.1).2 ∈ F := fun δ =>
    elimForward_mem q W hq hW (Submodule.mem_inf.mp δ.2).1 (Submodule.mem_inf.mp δ.2).2
  let φ : S →ₗ[ℝ] Q × F :=
    LinearMap.prod
      (LinearMap.codRestrict Q
        ((LinearMap.fst ℝ _ _) ∘ₗ elimForward ∘ₗ S.subtype) (fun δ => (hmem δ).1))
      (LinearMap.codRestrict F
        ((LinearMap.snd ℝ _ _) ∘ₗ elimForward ∘ₗ S.subtype) (fun δ => (hmem δ).2))
  have hbij : Function.Bijective φ := by
    constructor
    · intro a b hab
      apply Subtype.ext
      have h1 := congrArg (fun p : Q × F => (p.1 : Fin 4 → Fin 3 → TitsComplexMatrix)) hab
      have h2 := congrArg (fun p : Q × F => (p.2 : UnitaryErrorBases.Family)) hab
      exact elimForward_injOn q W hq hW (Submodule.mem_inf.mp a.2).1 (Submodule.mem_inf.mp a.2).2
        (Submodule.mem_inf.mp b.2).1 (Submodule.mem_inf.mp b.2).2 (Prod.ext h1 h2)
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      obtain ⟨δ, hf, hfo, he⟩ := elimForward_surjOn q W hq hW (a, b) ha hb
      refine ⟨⟨δ, Submodule.mem_inf.mpr ⟨hf, hfo⟩⟩, ?_⟩
      apply Prod.ext <;> apply Subtype.ext
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
  exact ⟨LinearEquiv.ofBijective φ hbij⟩

theorem finrank_fixed_stdAnchored (hq : ∀ k t, (q k t).val * (q k t).val = (q k t).val)
    (hW : UnitaryErrorBases.IsUnitaryErrorBasis W) :
    Module.finrank ℝ ↥(fixedSpace (compensated R0 stdShift) ⊓ firstOrderSystem (stdAnchored q W)) =
      Module.finrank ℝ (quartetFirstOrder fun k t => (q k t).val) +
        Module.finrank ℝ (UnitaryErrorBases.firstOrderSpace W) := by
  obtain ⟨e⟩ := fixed_stdAnchored_equiv q W hq hW
  rw [e.finrank_eq, Module.finrank_prod]

end CKM.NativeFirstOrder

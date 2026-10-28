module
public import PairingDefinitions
public import PairingA6
public import PairingCode
public import NativeLocalDimensionTen
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Option2StatementCode
open Option2StatementA6 CKM.NativeFirstOrder
theorem native_A7_local_dimension :
    ∃ rows : (Fin 4 → ℂ) → Fin 2184 → MvPolynomial (Fin 1053) ℂ,
      (∀ ξ x r, MvPolynomial.eval (fun j => (x j : ℂ)) (rows ξ r) =
        (Option2StatementResidual.originalF (displaced ξ x) r : ℂ)) ∧
      (∃ p : MvPolynomial (Fin 4) ℂ, p ≠ 0 ∧
        replacementLocus rows = CKM.NativeGoodPhase.GoodAvoid p) ∧
      ∀ u ∈ replacementLocus rows,
        (∀ N : Set CodeModuli, IsOpen N → phaseClass u ∈ N →
          (10 : WithBot ℕ∞) ≤ smallInductiveDimension N) ∧
        ∃ N : Set CodeModuli, IsOpen N ∧ phaseClass u ∈ N ∧
          smallInductiveDimension N = (10 : WithBot ℕ∞) := by
  let rows := Option2.NativeStress.PhaseHilbertA6.nativeRows
  have hl : replacementLocus rows = Option2.NativeStress.PhaseA6.nativeA6Locus := rfl
  refine ⟨rows, ?_, ?_, ?_⟩
  · intro ξ x r
    rw [Option2StatementResidual.originalF_eq_native]
    have hp : NativePolynomial.PartialAction.pack (displaced ξ x) =
        NativePolynomial.PartialAction.pack (literalCfg ξ) + x := by
      funext k
      simp only [NativePolynomial.PartialAction.pack, displaced, Pi.add_apply]
      congr 1
      exact congrArg x ((finProdFinEquiv : Fin 39 × Fin 27 ≃ Fin 1053).apply_symm_apply k)
    change MvPolynomial.eval _ (Option2.NativeStress.PhaseHilbertA6.nativeRows ξ r) =
      (MvPolynomial.eval (NativePolynomial.PartialAction.pack (displaced ξ x))
        (NativePolynomial.ConfigurationResiduals.fRow (1/2 : ℝ) (1/3 : ℝ) r) : ℂ)
    rw [hp]
    exact Option2.NativeStress.PhaseRealSheetIsolationA7.nativeRows_real_eval ξ x r
  · refine ⟨Option2.NativeStress.PhasePivotLocusA6.pivotPolynomial,
      Option2.NativeStress.PhasePivotLocusA6.pivotPolynomial_ne_zero, ?_⟩
    exact hl.trans Option2.NativeStress.PhaseA6.nativeA6Locus_eq_goodAvoid
  · intro u hu
    have hu' : u ∈ Option2.NativeStress.PhaseA6.nativeA6Locus := hl ▸ hu
    obtain ⟨hlo,N,hN,huN,hdim⟩ :=
      Option2.NativeStress.NativeLocalDimensionA7.native_code_local_dimension_ten u hu'
    constructor
    · intro V hV huV
      have hb := hlo (quotientHomeomorph '' V)
        (quotientHomeomorph.isOpenMap V hV)
        (by simpa only [quotientHomeomorph_phaseClass] using Set.mem_image_of_mem quotientHomeomorph huV)
      rwa [← (quotientHomeomorph.image V).smallInductiveDimension_congr] at hb
    · refine ⟨quotientHomeomorph.symm '' N,
        quotientHomeomorph.symm.isOpenMap N hN, ?_, ?_⟩
      · refine ⟨CKM.NativeGoodPhase.codeClass u, huN, ?_⟩
        exact quotientHomeomorph.symm_apply_eq.mpr (quotientHomeomorph_phaseClass u).symm
      · exact (quotientHomeomorph.symm.image N).smallInductiveDimension_congr.symm.trans hdim
end Option2StatementCode
#print axioms Option2StatementCode.native_A7_local_dimension

module

public import GPLabelled
public import ULCode

@[expose] public section

/-!
# Accumulation in the unlabelled tight-code quotient

`codeClass u` is the class of the literal configuration in `CodeModuli = tightLocus / (G × S₃₉)`,
formed with the existing constructor and `literalCfg_mem_tightLocus`. It is continuous, so the
labelled sequences of `GPLabelled` give classes converging to the class at the limiting phase. The
classes are not asserted pairwise distinct or different from the limit.
-/

noncomputable section

open MvPolynomial Filter Topology CKM.NativeFirstOrder CKM.NativeFourFamily
open CKM.NativeTightCode CKM.NativeUnlabelledSlice
open Option2.NativeStress.AnalyticDerivative (originalF)

namespace CKM.NativeGoodPhase

/-- The native quotient map from phases to unlabelled tight codes. -/
def codeClass (u : PhaseTorus) : CodeModuli :=
  Quotient.mk codeSetoid ⟨literalCfg u.1, literalCfg_mem_tightLocus u.1 u.2⟩

theorem continuous_codeClass : Continuous codeClass := by
  -- The quotient map composed with the continuous corestriction of `literalCfg` to `tightLocus`.
  exact continuous_quotient_mk'.comp
    (continuous_literalCfg_phase.subtype_mk fun u => literalCfg_mem_tightLocus u.1 u.2)

/-- **Code accumulation.** -/
theorem exists_seq_goodAvoid_code {p : MvPolynomial (Fin 4) ℂ} (hp : p ≠ 0) (u₀ : PhaseTorus) :
    ∃ u : ℕ → PhaseTorus, (∀ n, u n ∈ GoodAvoid p) ∧ (∀ n, u n ≠ u₀) ∧
      Tendsto u atTop (𝓝 u₀) ∧ (∀ n, originalF (literalCfg (u n).1) = 0) ∧
      (∀ n, literalCfg (u n).1 ∈ tightLocus) ∧
      Tendsto (fun n => literalCfg (u n).1) atTop (𝓝 (literalCfg u₀.1)) ∧
      Tendsto (fun n => codeClass (u n)) atTop (𝓝 (codeClass u₀)) := by
  -- The labelled sequence, with tight-code membership and the class limit by continuity.
  obtain ⟨u, hu, hne, ht, hF, hcfg⟩ := exists_seq_goodAvoid_labelled hp u₀
  exact ⟨u, hu, hne, ht, hF, fun n => literalCfg_mem_tightLocus (u n).1 (u n).2, hcfg,
    (continuous_codeClass.tendsto u₀).comp ht⟩

/-- **At the original code.** Every neighbourhood of the class of the original code contains the
class of a good phase `≠ 1` avoiding `p`. -/
theorem exists_goodAvoid_codeClass_mem_nhds_one {p : MvPolynomial (Fin 4) ℂ} (hp : p ≠ 0)
    {V : Set CodeModuli} (hV : V ∈ 𝓝 (codeClass onePhase)) :
    ∃ u : PhaseTorus, u ≠ onePhase ∧ u ∈ GoodAvoid p ∧ codeClass u ∈ V := by
  -- Along the punctured sequence at `onePhase`, the classes eventually lie in `V`.
  obtain ⟨u, hu, hne, -, -, -, -, hcls⟩ := exists_seq_goodAvoid_code hp onePhase
  obtain ⟨n, hn⟩ := (hcls.eventually hV).exists
  exact ⟨u n, hne n, hu n, hn⟩

end CKM.NativeGoodPhase

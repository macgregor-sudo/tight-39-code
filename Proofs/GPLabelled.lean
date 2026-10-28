module

public import GPPhase
public import A5Analytic

@[expose] public section
set_option backward.proofsInPublic true

/-!
# Accumulation in the literal labelled configuration

`ξ ↦ literalCfg ξ` is continuous (it is real-analytic coordinatewise, A5's `faman_ana_literalPoint`),
so the punctured phase sequences of `GPPhase` give configurations of the original zero set
(`originalF (literalCfg ξ) = 0`, accepted `originalF_literalCfg`) converging to the literal
configuration at the limiting phase. This module does not import the unlabelled tight-code quotient.
-/

noncomputable section

open MvPolynomial Filter Topology CKM.NativeFirstOrder CKM.NativeFourFamily
open Option2.NativeStress.AnalyticDerivative (originalF)

namespace CKM.NativeGoodPhase

theorem continuous_literalCfg : Continuous literalCfg := by
  -- Each coordinate `ξ ↦ upperCoordinates (literalPoint ξ i)` is real-analytic (A5), with
  -- `ξ = id` and the coordinate projections as the analytic phase inputs.
  have hcoord : ∀ (x : Fin 4 → ℂ) (a : Fin 4), AnalyticAt ℝ (fun y : Fin 4 → ℂ => y a) x :=
    fun x a => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℂ) a).analyticAt x
  rw [continuous_iff_continuousAt]
  intro x
  show ContinuousAt (fun ξ : Fin 4 → ℂ => fun i =>
    NativePolynomial.upperCoordinates (literalPoint ξ i)) x
  exact continuousAt_pi.mpr fun i => (faman_ana_literalPoint (ξ := id) (hcoord x) i).continuousAt

theorem continuous_literalCfg_phase : Continuous fun u : PhaseTorus => literalCfg u.1 :=
  continuous_literalCfg.comp continuous_subtype_val

/-- **Labelled accumulation.** -/
theorem exists_seq_goodAvoid_labelled {p : MvPolynomial (Fin 4) ℂ} (hp : p ≠ 0) (u₀ : PhaseTorus) :
    ∃ u : ℕ → PhaseTorus, (∀ n, u n ∈ GoodAvoid p) ∧ (∀ n, u n ≠ u₀) ∧
      Tendsto u atTop (𝓝 u₀) ∧ (∀ n, originalF (literalCfg (u n).1) = 0) ∧
      Tendsto (fun n => literalCfg (u n).1) atTop (𝓝 (literalCfg u₀.1)) := by
  -- The punctured phase sequence, pushed through the continuous labelled configuration.
  obtain ⟨u, hu, hne, ht⟩ := exists_seq_goodAvoid_tendsto hp u₀
  exact ⟨u, hu, hne, ht, fun n => CKM.NativeGroupSlice.originalF_literalCfg (u n).1 (u n).2,
    (continuous_literalCfg_phase.tendsto u₀).comp ht⟩

/-- The original code's phase `ξ = 1`. -/
def onePhase : PhaseTorus := ⟨fun _ => 1, fun _ => map_one Complex.normSq⟩

/-- **At the original code.** Every neighbourhood of the literal configuration at `ξ = 1` contains
the literal configuration of a good phase `≠ 1` avoiding `p`. -/
theorem exists_goodAvoid_literalCfg_mem_nhds_one {p : MvPolynomial (Fin 4) ℂ} (hp : p ≠ 0)
    {V : Set CKM.NativeGroupSlice.Cfg} (hV : V ∈ 𝓝 (literalCfg (fun _ => 1))) :
    ∃ u : PhaseTorus, u ≠ onePhase ∧ u ∈ GoodAvoid p ∧ literalCfg u.1 ∈ V := by
  -- Along the punctured sequence at `onePhase`, the configurations eventually lie in `V`.
  obtain ⟨u, hu, hne, -, -, hcfg⟩ := exists_seq_goodAvoid_labelled hp onePhase
  obtain ⟨n, hn⟩ := (hcfg.eventually hV).exists
  exact ⟨u n, hne n, hu n, hn⟩

end CKM.NativeGoodPhase
